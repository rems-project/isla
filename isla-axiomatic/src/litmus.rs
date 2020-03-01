// MIT License
//
// Copyright (c) 2019 Alasdair Armstrong
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::process::Stdio;
use toml::Value;

use isla_lib::concrete::BV;
use isla_lib::config::ISAConfig;
use isla_lib::ir::Symtab;
use isla_lib::log;
use isla_lib::zencode;

use crate::sandbox::SandboxedCommand;
use crate::sexp::Sexp;

/// We have a special purpose temporary file module which is used to
/// create the output file for each assembler/linker invocation. Each
/// call to new just creates a new file name using our PID and a
/// unique counter. This file isn't opened until we read it, after the
/// assembler has created the object file. Dropping the `TmpFile`
/// removes the file if it exists.
mod tmpfile {
    use std::env;
    use std::fs::{create_dir, remove_file, OpenOptions};
    use std::io::prelude::*;
    use std::path::{Path, PathBuf};
    use std::process;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Debug)]
    pub struct TmpFile {
        path: PathBuf,
    }

    static TMP_COUNTER: AtomicUsize = AtomicUsize::new(0);

    impl TmpFile {
        pub fn new() -> TmpFile {
            let mut path = env::temp_dir();
            path.push("isla");
            if !path.is_dir() {
                create_dir(&path).expect("Could not create temporary directory")
            }
            path.push(format!("isla_{}_{}", process::id(), TMP_COUNTER.fetch_add(1, Ordering::SeqCst)));
            TmpFile { path }
        }

        pub fn path(&self) -> &Path {
            self.path.as_ref()
        }

        pub fn read_to_end(&mut self) -> std::io::Result<Vec<u8>> {
            let mut fd = OpenOptions::new().read(true).open(&self.path)?;
            let mut buffer = Vec::new();
            fd.read_to_end(&mut buffer)?;
            Ok(buffer)
        }
    }

    impl Drop for TmpFile {
        fn drop(&mut self) {
            if remove_file(&self.path).is_err() {}
        }
    }
}

type ThreadName = String;

/// When we assemble a litmus test, we need to make sure any branch
/// instructions have addresses that will match the location at which
/// we load each thread in memory. To do this we invoke the linker and
/// give it a linker script with the address for each thread in the
/// litmus thread.
fn generate_linker_script<B>(threads: &[(ThreadName, &str)], isa: &ISAConfig<B>) -> String {
    use std::fmt::Write;

    let mut thread_address = isa.thread_base;

    let mut script = String::new();
    writeln!(&mut script, "start = 0;\nSECTIONS\n{{").unwrap();

    for (tid, _) in threads {
        writeln!(&mut script, "  . = 0x{:x};\n  litmus_{} : {{ *(litmus_{}) }}", thread_address, tid, tid).unwrap();
        thread_address += isa.thread_stride;
    }

    writeln!(&mut script, "}}").unwrap();
    script
}

/// This function takes some assembly code for each thread, which
/// should ideally be formatted as instructions separated by a newline
/// and a tab (`\n\t`), and invokes the assembler provided in the
/// `ISAConfig<B>` on this code. The generated ELF is then read in and
/// the assembled code is returned as a vector of bytes corresponding
/// to it's section in the ELF file as given by the thread name. If
/// `reloc` is true, then we will also invoke the linker to place each
/// thread's section at the correct address.
fn assemble<B>(
    threads: &[(ThreadName, &str)],
    reloc: bool,
    isa: &ISAConfig<B>,
) -> Result<(Vec<(ThreadName, Vec<u8>)>, String), String> {
    use goblin::Object;

    let objfile = tmpfile::TmpFile::new();

    let mut assembler = SandboxedCommand::new(&isa.assembler)
        .arg("-o")
        .arg(objfile.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .or_else(|err| Err(format!("Failed to spawn assembler {}. Got error: {}", &isa.assembler.display(), err)))?;

    // Write each thread to the assembler's standard input, in a section called `litmus_N` for each thread `N`
    {
        let stdin = assembler.stdin.as_mut().ok_or_else(|| "Failed to open stdin for assembler".to_string())?;
        for (thread_name, code) in threads.iter() {
            stdin
                .write_all(format!("\t.section litmus_{}\n", thread_name).as_bytes())
                .and_then(|_| stdin.write_all(code.as_bytes()))
                .or_else(|_| Err(format!("Failed to write to assembler input file {}", objfile.path().display())))?
        }
    }

    let output = assembler.wait_with_output().or_else(|_| Err("Failed to read stdout from assembler".to_string()))?;

    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).to_string());
    }

    let (mut objfile, objdump) = if reloc {
        let objfile_reloc = tmpfile::TmpFile::new();
        let linker_script = tmpfile::TmpFile::new();
        {
            let mut fd = File::create(linker_script.path())
                .or_else(|_| Err("Failed to create temp file for linker script".to_string()))?;
            fd.write_all(generate_linker_script(threads, isa).as_bytes())
                .or_else(|_| Err("Failed to write linker script".to_string()))?;
        }

        let linker_status = SandboxedCommand::new(&isa.linker)
            .arg("-T")
            .arg(linker_script.path())
            .arg("-o")
            .arg(objfile_reloc.path())
            .arg(objfile.path())
            .status()
            .or_else(|err| Err(format!("Failed to invoke linker {}. Got error: {}", &isa.linker.display(), err)))?;

        // Invoke objdump to get the assembled output in human readable
        // form. If objdump fails for whatever reason, we don't want to
        // consider it a hard error however.
        let objdump = {
            let output = SandboxedCommand::new(&isa.objdump).arg("-D").arg(objfile_reloc.path()).output();

            if let Ok(output) = output {
                String::from_utf8_lossy(if output.status.success() { &output.stdout } else { &output.stderr })
                    .to_string()
            } else {
                format!("Failed to invoke {}", &isa.objdump.display())
            }
        };

        if linker_status.success() {
            (objfile_reloc, objdump)
        } else {
            return Err(format!("Linker failed with exit code {}", linker_status));
        }
    } else {
        (objfile, "Objdump not available unless linker was used".to_string())
    };

    let buffer = objfile.read_to_end().or_else(|_| Err("Failed to read generated ELF file".to_string()))?;

    // Get the code from the generated ELF's `litmus_N` section for each thread
    let mut assembled: Vec<(ThreadName, Vec<u8>)> = Vec::new();
    match Object::parse(&buffer) {
        Ok(Object::Elf(elf)) => {
            let shdr_strtab = elf.shdr_strtab;
            for section in elf.section_headers {
                if let Some(Ok(section_name)) = shdr_strtab.get(section.sh_name) {
                    for (thread_name, _) in threads.iter() {
                        if section_name == format!("litmus_{}", thread_name) {
                            let offset = section.sh_offset as usize;
                            let size = section.sh_size as usize;
                            assembled.push((thread_name.to_string(), buffer[offset..(offset + size)].to_vec()))
                        }
                    }
                }
            }
        }
        Ok(_) => return Err("Generated object was not an ELF file".to_string()),
        Err(err) => return Err(format!("Failed to parse ELF file: {}", err)),
    };

    if assembled.len() != threads.len() {
        return Err("Could not find all threads in generated ELF file".to_string());
    };

    Ok((assembled, objdump))
}

/// For error reporting it's very helpful to be able to turn the raw
/// opcodes we work with into actual human-readable assembly. To do
/// this we use a regex to pair up the opcode with it's disassembly in
/// objdump output for the litmus test.
pub fn instruction_from_objdump<'obj>(opcode: &str, objdump: &'obj str) -> Option<String> {
    use regex::Regex;
    let instr_re = Regex::new(&format!(r"[0-9a-zA-Z]+:\t{} \t(.*)", opcode)).unwrap();

    // Find all instructions for an opcode in the objdump output. Return None if
    // for some reason they are non-unique
    // (this could happen if e.g. relocations have not been applied tojumps).
    let mut instr: Option<&'obj str> = None;
    for caps in instr_re.captures_iter(objdump) {
        if let Some(prev) = instr {
            if prev == caps.get(1)?.as_str().trim() {
                continue;
            } else {
                return None;
            }
        } else {
            instr = Some(caps.get(1)?.as_str().trim())
        }
    }

    let whitespace_re = Regex::new(r"\s+").unwrap();
    Some(whitespace_re.replace_all(instr?, " ").to_string())
}

pub fn assemble_instruction<B>(instr: &str, isa: &ISAConfig<B>) -> Result<Vec<u8>, String> {
    let instr = instr.to_owned() + "\n";
    if let [(_, bytes)] = assemble(&[("single".to_string(), &instr)], false, isa)?.0.as_slice() {
        Ok(bytes.to_vec())
    } else {
        Err(format!("Failed to assemble instruction {}", instr))
    }
}

fn parse_symbolic_locations(litmus_toml: &Value) -> Result<HashMap<String, u64>, String> {
    let sym_locs_table = match litmus_toml.get("locations") {
        Some(value) => value
            .as_table()
            .ok_or_else(|| "[locations] must be a table of <symbolic address> = <value> pairs".to_string())?,
        // Most litmus tests won't define any symbolic locations.
        None => return Ok(HashMap::new()),
    };

    let mut sym_locs = HashMap::new();
    for (sym_loc, value) in sym_locs_table {
        let value = u64::from_str_radix(value.as_str().ok_or_else(|| "Invalid symbolic address value")?, 10)
            .or_else(|_| Err("Could not parse symbolic location value as an integer".to_string()))?;
        sym_locs.insert(sym_loc.clone(), value);
    }

    Ok(sym_locs)
}

fn parse_init<B>(
    reg: &str,
    value: &Value,
    symbolic_addrs: &HashMap<String, u64>,
    symtab: &Symtab,
    isa: &ISAConfig<B>,
) -> Result<(u32, u64), String> {
    let reg = match isa.register_renames.get(reg) {
        Some(reg) => *reg,
        None => symtab.get(&zencode::encode(reg)).ok_or_else(|| format!("No register {} in thread init", reg))?,
    };

    let value = value.as_str().ok_or_else(|| "Init value must be a string".to_string())?;

    match symbolic_addrs.get(value) {
        Some(addr) => Ok((reg, *addr)),
        None => match i64::from_str_radix(value, 10) {
            Ok(n) => Ok((reg, n as u64)),
            Err(_) => Err(format!("Cannot handle initial value in litmus: {}", value)),
        }
    }
}

fn parse_thread_inits<'a, B>(
    thread: &'a Value,
    symbolic_addrs: &HashMap<String, u64>,
    symtab: &Symtab,
    isa: &ISAConfig<B>,
) -> Result<Vec<(u32, u64)>, String> {
    let inits = thread
        .get("init")
        .and_then(Value::as_table)
        .ok_or_else(|| "Thread init must be a list of register name/value pairs".to_string())?;

    inits.iter().map(|(reg, value)| parse_init(reg, value, symbolic_addrs, symtab, isa)).collect::<Result<_, _>>()
}

fn parse_assertion(assertion: &str) -> Result<Sexp<'_>, String> {
    let lexer = crate::sexp_lexer::SexpLexer::new(assertion);
    match crate::sexp_parser::SexpParser::new().parse(lexer) {
        Ok(sexp) => Ok(sexp),
        Err(e) => Err(format!("Could not parse final state in litmus file: {}", e)),
    }
}

#[derive(Debug)]
pub enum Loc {
    Register { reg: u32, thread_id: usize },
    LastWriteTo { address: u64 },
}

impl Loc {
    fn from_sexp<'a, B: BV>(
        sexp: &Sexp<'a>,
        symbolic_addrs: &HashMap<String, u64>,
        symtab: &Symtab,
        isa: &ISAConfig<B>,
    ) -> Option<Self> {
        use Loc::*;
        match sexp {
            Sexp::List(sexps) => {
                if sexp.is_fn("register", 2) && sexps.len() == 3 {
                    let reg = sexps[1].as_str()?;
                    let reg = match isa.register_renames.get(reg) {
                        Some(reg) => *reg,
                        None => symtab.get(&zencode::encode(reg))?,
                    };
                    let thread_id = sexps[2].as_usize()?;
                    Some(Register { reg, thread_id })
                } else if sexp.is_fn("last_write_to", 1) && sexps.len() == 2 {
                    let symbolic_addr = sexps[1].as_str()?;
                    let address = *symbolic_addrs.get(symbolic_addr)?;
                    Some(LastWriteTo { address })
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[derive(Debug)]
pub enum Prop<B> {
    EqLoc(Loc, B),
    True,
    False,
    And(Vec<Prop<B>>),
    Or(Vec<Prop<B>>),
    Not(Box<Prop<B>>),
    Implies(Box<Prop<B>>, Box<Prop<B>>),
}

impl<B: BV> Prop<B> {
    fn from_sexp<'a>(
        sexp: &Sexp<'a>,
        symbolic_addrs: &HashMap<String, u64>,
        symtab: &Symtab,
        isa: &ISAConfig<B>,
    ) -> Option<Self> {
        use Prop::*;
        match sexp {
            Sexp::Atom("true") => Some(True),
            Sexp::Atom("false") => Some(False),
            Sexp::List(sexps) => {
                if sexp.is_fn("=", 2) && sexps.len() == 3 {
                    Some(EqLoc(
                        Loc::from_sexp(&sexps[1], symbolic_addrs, symtab, isa)?,
                        B::from_u64(sexps[2].as_u64()?),
                    ))
                } else if sexp.is_fn("and", 1) {
                    sexps[1..]
                        .iter()
                        .map(|s| Prop::from_sexp(s, symbolic_addrs, symtab, isa))
                        .collect::<Option<_>>()
                        .map(Prop::And)
                } else if sexp.is_fn("or", 1) {
                    sexps[1..]
                        .iter()
                        .map(|s| Prop::from_sexp(s, symbolic_addrs, symtab, isa))
                        .collect::<Option<_>>()
                        .map(Prop::Or)
                } else if sexp.is_fn("=>", 2) && sexps.len() == 3 {
                    Some(Prop::Implies(
                        Box::new(Prop::from_sexp(&sexps[1], symbolic_addrs, symtab, isa)?),
                        Box::new(Prop::from_sexp(&sexps[2], symbolic_addrs, symtab, isa)?),
                    ))
                } else if sexp.is_fn("not", 1) && sexps.len() == 2 {
                    Prop::from_sexp(&sexps[1], symbolic_addrs, symtab, isa).map(|s| Prop::Not(Box::new(s)))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

pub type AssembledThread = (ThreadName, Vec<(u32, u64)>, Vec<u8>);

pub struct Litmus<B> {
    pub name: String,
    pub hash: Option<String>,
    pub symbolic_addrs: HashMap<String, u64>,
    pub symbolic_locations: HashMap<String, u64>,
    pub assembled: Vec<AssembledThread>,
    pub objdump: String,
    pub final_assertion: Prop<B>,
}

impl<B: BV> Litmus<B> {
    pub fn log(&self) {
        log!(log::LITMUS, &format!("Litmus test name: {}", self.name));
        log!(log::LITMUS, &format!("Litmus test hash: {:?}", self.hash));
        log!(log::LITMUS, &format!("Litmus test symbolic addresses: {:?}", self.symbolic_addrs));
        log!(log::LITMUS, &format!("Litmus test data: {:#?}", self.assembled));
        log!(log::LITMUS, &format!("Litmus test final assertion: {:?}", self.final_assertion));
    }

    pub fn parse(contents: &str, symtab: &Symtab, isa: &ISAConfig<B>) -> Result<Self, String> {
        let litmus_toml = match contents.parse::<Value>() {
            Ok(toml) => toml,
            Err(e) => return Err(format!("Error when parsing litmus: {}", e)),
        };

        let name = litmus_toml
            .get("name")
            .and_then(|n| n.as_str().map(str::to_string))
            .ok_or_else(|| "No name found in litmus file".to_string())?;

        let hash = litmus_toml.get("hash").map(|h| h.to_string());

        let symbolic = litmus_toml
            .get("symbolic")
            .and_then(Value::as_array)
            .ok_or("No symbolic addresses found in litmus file")?;
        let symbolic_addrs = symbolic
            .iter()
            .enumerate()
            .map(|(i, sym_addr)| match sym_addr.as_str() {
                Some(sym_addr) => {
                    Ok((sym_addr.to_string(), isa.symbolic_addr_base + (i as u64 * isa.symbolic_addr_stride)))
                }
                None => Err("Symbolic addresses must be strings"),
            })
            .collect::<Result<_, _>>()?;

        let symbolic_locations = parse_symbolic_locations(&litmus_toml)?;

        let threads = litmus_toml.get("thread").and_then(|t| t.as_table()).ok_or("No threads found in litmus file")?;

        let mut inits: Vec<Vec<(u32, u64)>> = threads
            .iter()
            .map(|(_, thread)| parse_thread_inits(thread, &symbolic_addrs, symtab, isa))
            .collect::<Result<_, _>>()?;

        let code: Vec<(ThreadName, &str)> = threads
            .iter()
            .map(|(thread_name, thread)| {
                thread
                    .get("code")
                    .and_then(|code| code.as_str().map(|code| (thread_name.to_string(), code)))
                    .ok_or_else(|| format!("No code found for thread {}", thread_name))
            })
            .collect::<Result<_, _>>()?;
        let (mut assembled, objdump) = assemble(&code, true, isa)?;

        let assembled = assembled
            .drain(..)
            .zip(inits.drain(..))
            .map(|((thread_name, code), init)| (thread_name, init, code))
            .collect();

        let fin = litmus_toml.get("final").ok_or("No final section found in litmus file")?;
        let final_assertion = (match fin.get("assertion").and_then(Value::as_str) {
            Some(assertion) => parse_assertion(assertion).and_then(|s| {
                Prop::from_sexp(&s, &symbolic_addrs, symtab, isa)
                    .ok_or_else(|| "Cannot parse final assertion".to_string())
            }),
            None => Err("No final.assertion found in litmus file".to_string()),
        })?;

        Ok(Litmus {
            name,
            hash,
            symbolic_addrs,
            symbolic_locations,
            assembled,
            objdump,
            final_assertion,
        })
    }

    pub fn from_file<P>(path: P, symtab: &Symtab, isa: &ISAConfig<B>) -> Result<Self, String>
    where
        P: AsRef<Path>,
    {
        let mut contents = String::new();
        match File::open(&path) {
            Ok(mut handle) => match handle.read_to_string(&mut contents) {
                Ok(_) => (),
                Err(e) => return Err(format!("Unexpected failure while reading litmus: {}", e)),
            },
            Err(e) => return Err(format!("Error when loading litmus '{}': {}", path.as_ref().display(), e)),
        };

        Self::parse(&contents, symtab, isa)
    }
}
