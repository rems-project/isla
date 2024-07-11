// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::process::Stdio;
use std::sync::Arc;
use toml::{value::Table, Value};

use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::ir::{IRTypeInfo, Loc, Name, Symtab};
use isla_lib::ir_lexer::new_ir_lexer;
use isla_lib::log;
use isla_lib::memory::Region;
use isla_lib::smt::Solver;
use isla_lib::value_parser::LocParser;
use isla_lib::zencode;

use crate::page_table;
use crate::sandbox::SandboxedCommand;

pub mod exp;
pub mod exp_lexer;
mod format;
lalrpop_mod!(
    #[allow(clippy::all)]
    pub exp_parser,
    "/litmus/exp_parser.rs"
);

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
type SectionName = String;

/// A thread may either be defined by some assembly code, or by a call
/// to an IR function
enum ThreadBody<'a> {
    Code(&'a str),
    Call(Name),
}

/// In addition to the threads, system litmus tests can contain extra
/// sections containing additional code. These are linked at specific
/// addresess. For example we might place a section at VBAR_EL1 for a
/// thread to serve as an exception handler in ARMv8.
struct UnassembledSection<'a> {
    name: &'a str,
    address: u64,
    code: &'a str,
}

static THREAD_PREFIX: &str = "litmus_";

fn validate_section_name(name: &str) -> bool {
    for (i, c) in name.chars().enumerate() {
        if i == 0 && !c.is_ascii_alphabetic() {
            return false;
        }

        if !(c.is_ascii_alphanumeric() || c == '_') {
            return false;
        }
    }

    // Would conflict with the name we use for threads by default
    if name.len() >= THREAD_PREFIX.len() && &name[0..THREAD_PREFIX.len()] == THREAD_PREFIX {
        return false;
    }

    true
}

fn parse_address(addr: &str) -> Result<u64, String> {
    if addr.len() < 2 {
        return Err(format!("Address {} is too short, it must have the form 0xHEX or #xHEX", addr));
    }
    if &addr[0..2] != "0x" && &addr[0..2] != "#x" {
        return Err(format!("Address {} must start with either `0x' or `#x'", addr));
    }
    u64::from_str_radix(&addr[2..], 16).map_err(|_| format!("Cannot parse {} as hexadecimal", addr))
}

enum LinkerLine<'a, 'b> {
    Thread(&'a str),
    Section(&'a UnassembledSection<'b>),
}

/// When we assemble a litmus test, we need to make sure any branch
/// instructions have addresses that will match the location at which
/// we load each thread in memory. To do this we invoke the linker and
/// give it a linker script with the address for each thread in the
/// litmus thread.
fn generate_linker_script<B>(
    threads: &[(ThreadName, ThreadBody<'_>)],
    sections: &[UnassembledSection<'_>],
    isa: &ISAConfig<B>,
) -> String {
    use std::fmt::Write;
    use LinkerLine::*;

    let mut thread_address = isa.thread_base;

    let mut script = String::new();
    writeln!(&mut script, "start = 0;\nENTRY(start);\nSECTIONS\n{{").unwrap();

    let mut t = 0;
    let mut s = 0;

    loop {
        let line = match (threads.get(t), sections.get(s)) {
            // For a non-code thread we don't generate anything, so increment t and try the next thread
            (Some((_, body)), _) if !matches!(body, ThreadBody::Code(_)) => {
                t += 1;
                continue;
            }
            (Some((tid, _)), Some(section)) if thread_address < section.address => Thread(tid),
            (Some(_), Some(section)) => Section(section),
            (Some((tid, _)), None) => Thread(tid),
            (None, Some(section)) => Section(section),
            (None, None) => break,
        };

        match line {
            Thread(tid) => {
                writeln!(
                    &mut script,
                    "  . = 0x{:x};\n  {}{} : {{ *({}{}) }}",
                    thread_address, THREAD_PREFIX, tid, THREAD_PREFIX, tid
                )
                .unwrap();
                thread_address += isa.thread_stride;
                t += 1
            }
            Section(section) => {
                writeln!(&mut script, "  . = 0x{:x};\n  {} : {{ *({}) }}", section.address, section.name, section.name)
                    .unwrap();
                s += 1
            }
        }
    }

    writeln!(&mut script, "}}").unwrap();

    log!(log::LITMUS, &format!("Linker script:\n{}", script));

    script
}

#[derive(Clone, Debug)]
pub struct Objdump {
    /// The output of `objdump` on the assembled binary
    pub objdump: String,
    /// The output of `nm` on the assembled binary
    pub names: String,
}

impl Objdump {
    pub fn empty() -> Self {
        Objdump { objdump: "".to_string(), names: "".to_string() }
    }
}

pub type AssembledThreads = (HashMap<ThreadName, (u64, Vec<u8>)>, Vec<(u64, Vec<u8>)>, Objdump);

#[cfg(feature = "sandbox")]
fn validate_code(code: &str) -> Result<(), String> {
    // We already run in sandbox, but we can additionally rule out any
    // directives
    if code.contains('.') {
        return Err("Invalid assembly in litmus".to_string());
    }

    if code.len() > 1000 {
        return Err("Assembly in litmus thread too long".to_string());
    }

    for c in code.chars() {
        if !c.is_ascii() || (c.is_control() && !c.is_ascii_whitespace()) {
            return Err("Assembly block can contain only ascii text".to_string());
        }
    }

    Ok(())
}

#[cfg(not(feature = "sandbox"))]
fn validate_code(_: &str) -> Result<(), String> {
    Ok(())
}

fn requires_assembly(threads: &[(ThreadName, ThreadBody)]) -> bool {
    for (_, body) in threads.iter() {
        if matches!(body, ThreadBody::Code(_)) {
            return true;
        }
    }
    false
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
    threads: &[(ThreadName, ThreadBody)],
    sections: &[UnassembledSection<'_>],
    reloc: bool,
    isa: &ISAConfig<B>,
) -> Result<AssembledThreads, String> {
    use goblin::Object;

    if !requires_assembly(threads) && sections.is_empty() {
        return Ok((HashMap::new(), Vec::new(), Objdump::empty()));
    }

    let objfile = tmpfile::TmpFile::new();

    let mut assembler = SandboxedCommand::from_tool(&isa.assembler)
        .arg("-o")
        .arg(objfile.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|err| {
            format!("Failed to spawn assembler {}. Got error: {}", &isa.assembler.executable.display(), err)
        })?;

    // Write each thread to the assembler's standard input, in a section called `THREAD_PREFIXN` for each thread `N`
    {
        let stdin = assembler.stdin.as_mut().ok_or_else(|| "Failed to open stdin for assembler".to_string())?;
        for (thread_name, body) in threads.iter() {
            if let ThreadBody::Code(code) = body {
                validate_code(code)?;
                stdin
                    .write_all(format!("\t.section {}{}, \"xa\"\n", THREAD_PREFIX, thread_name).as_bytes())
                    .and_then(|_| stdin.write_all(code.as_bytes()))
                    .map_err(|_| format!("Failed to write to assembler input file {}", objfile.path().display()))?
            }
        }
        for section in sections {
            validate_code(section.code)?;
            if !validate_section_name(section.name) {
                return Err(format!("Section name {} is invalid", section.name));
            };
            stdin
                .write_all(format!("\t.section {}, \"xa\"\n", section.name).as_bytes())
                .and_then(|_| stdin.write_all(section.code.as_bytes()))
                .map_err(|_| format!("Failed to write to assembler input file {}", objfile.path().display()))?
        }
    }

    let output = assembler.wait_with_output().map_err(|_| "Failed to read stdout from assembler".to_string())?;

    if !output.status.success() {
        return Err(format!("Assembler failed with: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let (mut objfile, objdump, names) = if reloc {
        let objfile_reloc = tmpfile::TmpFile::new();
        let linker_script = tmpfile::TmpFile::new();
        {
            let mut fd = File::create(linker_script.path())
                .map_err(|_| "Failed to create temp file for linker script".to_string())?;
            fd.write_all(generate_linker_script(threads, sections, isa).as_bytes())
                .map_err(|_| "Failed to write linker script".to_string())?;
        }

        let linker_status = SandboxedCommand::from_tool(&isa.linker)
            .arg("-T")
            .arg(linker_script.path())
            .arg("-o")
            .arg(objfile_reloc.path())
            .arg(objfile.path())
            .status()
            .map_err(|err| {
                format!("Failed to invoke linker {}. Got error: {}", &isa.linker.executable.display(), err)
            })?;

        // Invoke objdump to get the assembled output in human readable
        // form. If objdump fails for whatever reason, we don't want to
        // consider it a hard error however.
        let objdump = {
            let output = SandboxedCommand::from_tool(&isa.objdump).arg("-D").arg(objfile_reloc.path()).output();

            if let Ok(output) = output {
                String::from_utf8_lossy(if output.status.success() { &output.stdout } else { &output.stderr })
                    .to_string()
            } else {
                format!("Failed to invoke {}", &isa.objdump.executable.display())
            }
        };

        // Invoke nm to get the list of locations in human readable form.
        // This failing is a hard error, as we need the location information.
        let names = SandboxedCommand::from_tool(&isa.nm)
            .arg(objfile_reloc.path())
            .output()
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .map_err(|err| format!("Failed to invoke nm {}. Got error: {}", &isa.nm.executable.display(), err))?;

        if linker_status.success() {
            (objfile_reloc, objdump, names)
        } else {
            return Err(format!("Linker failed with exit code {}", linker_status));
        }
    } else {
        (
            objfile,
            "Objdump not available unless linker was used".to_string(),
            "Names not available unless linker was used".to_string(),
        )
    };

    let buffer = objfile.read_to_end().map_err(|_| "Failed to read generated ELF file".to_string())?;

    // Get the code from the generated ELF's `THREAD_PREFIXN` section for each thread, and for each custom section
    let mut assembled_threads: HashMap<ThreadName, (u64, Vec<u8>)> = HashMap::new();
    let mut assembled_sections: Vec<(u64, Vec<u8>)> = Vec::new();
    match Object::parse(&buffer) {
        Ok(Object::Elf(elf)) => {
            let shdr_strtab = elf.shdr_strtab;
            for section in elf.section_headers {
                if let Some(section_name) = shdr_strtab.get_at(section.sh_name) {
                    for (thread_name, _) in threads.iter() {
                        if section_name == format!("{}{}", THREAD_PREFIX, thread_name) {
                            let offset = section.sh_offset as usize;
                            let size = section.sh_size as usize;
                            assembled_threads.insert(
                                thread_name.to_string(),
                                (section.sh_addr, buffer[offset..(offset + size)].to_vec()),
                            );
                        }
                    }
                    for litmus_section in sections {
                        if section_name == litmus_section.name {
                            let offset = section.sh_offset as usize;
                            let size = section.sh_size as usize;
                            assembled_sections.push((litmus_section.address, buffer[offset..(offset + size)].to_vec()))
                        }
                    }
                }
            }
        }
        Ok(_) => return Err("Generated object was not an ELF file".to_string()),
        Err(err) => return Err(format!("Failed to parse ELF file: {}", err)),
    };

    log!(log::LITMUS, &format!("Objdump:\n{}", objdump));
    log!(log::LITMUS, &format!("Names:\n{}", names));

    Ok((assembled_threads, assembled_sections, Objdump { objdump, names }))
}

/// For error reporting it's very helpful to be able to turn the raw
/// opcodes we work with into actual human-readable assembly. To do
/// this we use a regex to pair up the opcode with it's disassembly in
/// objdump output for the litmus test.
pub fn instruction_from_objdump<'obj>(opcode: &str, objdump: &'obj Objdump) -> Option<String> {
    use regex::Regex;
    let instr_re = Regex::new(&format!(r"[0-9a-zA-Z]+:\s0*{}\s+(.*)", opcode)).unwrap();

    // Find all instructions for an opcode in the objdump output. Return None if
    // for some reason they are non-unique
    // (this could happen if e.g. relocations have not been applied tojumps).
    let mut instr: Option<&'obj str> = None;
    for caps in instr_re.captures_iter(&objdump.objdump) {
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

pub fn opcode_from_objdump<B: BV>(addr: B, objdump: &Objdump) -> Option<B> {
    use regex::Regex;
    let opcode_re = Regex::new(&format!(r"(?m)^\s+{:x}:\s+([0-9a-fA-F]+)\s", addr)).unwrap();

    if let Some(caps) = opcode_re.captures(&objdump.objdump) {
        B::from_str(&format!("0x{}", caps.get(1)?.as_str()))
    } else {
        None
    }
}

fn label_from_nm(label: &str, nm: &str) -> Option<u64> {
    use regex::Regex;
    let nm_re = Regex::new(&format!(r"([0-9a-fA-F]+) t {}", label)).unwrap();
    let c = nm_re.captures(nm)?;
    u64::from_str_radix(c.get(1)?.as_str(), 16).ok()
}

fn label_from_objdump(label: &str, objdump: &Objdump) -> Option<u64> {
    label_from_nm(label, &objdump.names)
}

pub fn assemble_instruction<B>(instr: &str, isa: &ISAConfig<B>) -> Result<Vec<u8>, String> {
    let instr = instr.to_owned() + "\n";
    if let Some((_, bytes)) =
        assemble(&[("single".to_string(), ThreadBody::Code(&instr))], &[], false, isa)?.0.remove("single")
    {
        Ok(bytes.to_vec())
    } else {
        Err(format!("Failed to assemble instruction {}", instr))
    }
}

pub fn parse_constrained_region<B: BV>(
    toml_region: &Value,
    symbolic_addrs: &HashMap<String, u64>,
) -> Result<Region<B>, String> {
    let table = toml_region.as_table().ok_or("Each constrained element must be a TOML table")?;

    let address =
        table.get("address").and_then(Value::as_str).ok_or("constrained element must have a `address` field")?;
    let address = *symbolic_addrs.get(address).ok_or_else(|| "Address is not defined".to_string())?;

    let bytes =
        table.get("bytes").and_then(Value::as_integer).ok_or("constrained element must have a `bytes` field")?;
    let upper = address + (bytes as u64);

    let values =
        table.get("values").and_then(Value::as_array).ok_or("constrained element must have a `values` field")?;
    let values = values
        .iter()
        .map(|v| {
            let value = v.as_str()?;
            match value.parse::<i64>() {
                Ok(n) => Some(n as u64),
                Err(_) => symbolic_addrs.get(value).copied(),
            }
        })
        .collect::<Option<Vec<_>>>()
        .ok_or("Could not parse `values` field")?;

    Ok(Region::Constrained(
        address..upper,
        Arc::new(move |solver: &mut Solver<B>| {
            use isla_lib::smt::smtlib::{bits64, Def, Exp, Ty};
            let v = solver.fresh();
            let exp: Exp<_> = values.iter().fold(Exp::Bool(false), |exp, bits| {
                Exp::Or(
                    Box::new(Exp::Eq(Box::new(Exp::Var(v)), Box::new(bits64(*bits, bytes as u32 * 8)))),
                    Box::new(exp),
                )
            });
            solver.add(Def::DeclareConst(v, Ty::BitVec(bytes as u32 * 8)));
            solver.add(Def::Assert(exp));
            v
        }),
    ))
}

pub fn parse_constrained<B: BV>(toml: &Value, symbolic_addrs: &HashMap<String, u64>) -> Result<Vec<Region<B>>, String> {
    if let Some(value) = toml.get("constrained") {
        let array = value.as_array().ok_or_else(|| "constrained section must be a TOML array".to_string())?;
        Ok(array.iter().map(|v| parse_constrained_region(v, symbolic_addrs)).collect::<Result<_, _>>()?)
    } else {
        Ok(Vec::new())
    }
}

pub fn parse_locations(
    litmus_toml: &Value,
    symbolic_addrs: &HashMap<String, u64>,
) -> Result<HashMap<u64, u64>, String> {
    let location_table = match litmus_toml.get("locations") {
        Some(value) => {
            value.as_table().ok_or_else(|| "[locations] must be a table of <address> = <value> pairs".to_string())?
        }
        // Most litmus tests won't define any symbolic locations.
        None => return Ok(HashMap::new()),
    };

    let mut locations = HashMap::new();
    for (loc, value) in location_table.iter() {
        let addr = *symbolic_addrs.get(loc).ok_or_else(|| "Address is not defined".to_string())?;
        let value = value.as_str().ok_or_else(|| format!("Invalid value for {} in [locations]", loc))?;
        let value = match value.parse::<i64>() {
            Ok(n) => n as u64,
            Err(_) => *symbolic_addrs.get(value).ok_or_else(|| {
                format!("Could not parse location value {} as an integer or address value in [locations]", value)
            })?,
        };
        locations.insert(addr, value);
    }

    Ok(locations)
}

pub fn parse_sizeof_types(litmus_toml: &Value) -> Result<HashMap<String, u32>, String> {
    let sym_types_table = match litmus_toml.get("types") {
        Some(value) => {
            value.as_table().ok_or_else(|| "[types] must be a table of <address> = <type> pairs".to_string())?
        }
        // Most litmus tests won't define any symbolic types.
        None => return Ok(HashMap::new()),
    };

    let mut sym_sizeof = HashMap::new();
    for (sym_type, ty) in sym_types_table {
        let sizeof = match ty.as_str() {
            Some("uint64_t") => 8,
            Some("uint32_t") => 4,
            Some("uint16_t") => 2,
            Some("uint8_t") => 1,
            _ => return Err("Invalid type in litmus [types] table".to_string()),
        };
        sym_sizeof.insert(sym_type.clone(), sizeof);
    }

    Ok(sym_sizeof)
}

pub fn parse_init<B>(
    reg: &str,
    value: &Value,
    symbolic_addrs: &HashMap<String, u64>,
    objdump: &Objdump,
    symtab: &Symtab,
    isa: &ISAConfig<B>,
) -> Result<(Name, u64), String> {
    let reg = match isa.register_renames.get(reg) {
        Some(reg) => *reg,
        None => symtab.get(&zencode::encode(reg)).ok_or_else(|| format!("No register {} in thread init", reg))?,
    };

    let value = value.as_str().ok_or_else(|| "Init value must be a string".to_string())?;

    match symbolic_addrs.get(value) {
        Some(addr) => Ok((reg, *addr)),
        None => {
            if let Some(hex) = value.strip_prefix("0x") {
                match u64::from_str_radix(hex, 16) {
                    Ok(n) => Ok((reg, n)),
                    Err(_) => Err(format!("Cannot parse hexadecimal initial value in litmus: {}", value)),
                }
            } else if value.ends_with(':') {
                match label_from_objdump(&value[0..value.len() - 1], objdump) {
                    Some(addr) => Ok((reg, addr)),
                    None => Err(format!("Could not find label {}", value)),
                }
            } else {
                match value.parse::<i64>() {
                    Ok(n) => Ok((reg, n as u64)),
                    Err(_) => Err(format!("Cannot handle initial value in litmus: {}", value)),
                }
            }
        }
    }
}

pub fn parse_reset_value(toml: &Value, symtab: &Symtab) -> Result<exp::Exp<String>, String> {
    let value_str = toml.as_str().ok_or_else(|| format!("Register reset value must be a string {}", toml))?;

    let lexer = exp_lexer::ExpLexer::new(value_str);
    if let Ok(exp) = exp_parser::ExpParser::new().parse(&HashMap::new(), 4, symtab, &HashMap::new(), lexer) {
        Ok(exp)
    } else {
        Err(format!("Could not parse register value {}", value_str))
    }
}

pub fn parse_reset_registers<B: BV>(
    toml: &Value,
    _symbolic_addrs: &HashMap<String, u64>,
    symtab: &Symtab,
    type_info: &IRTypeInfo,
    isa: &ISAConfig<B>,
) -> Result<HashMap<Loc<Name>, exp::Exp<String>>, String> {
    if let Some(resets) = toml.as_table() {
        resets
            .into_iter()
            .map(|(register, value)| {
                if let Ok(loc) = LocParser::new().parse::<B, _, _>(symtab, type_info, new_ir_lexer(register)) {
                    let loc = match isa.register_renames.get(register) {
                        Some(reg) => Some(Loc::Id(*reg)),
                        None => symtab.get_loc(&loc),
                    };

                    if let Some(loc) = loc {
                        Ok((loc, parse_reset_value(value, symtab)?))
                    } else {
                        Err(format!("Could not find register {} when parsing register reset information", register))
                    }
                } else {
                    Err(format!("Could not parse register {} when parsing register reset information", register))
                }
            })
            .collect()
    } else {
        Err("registers.reset should be a table of <register> = <value> pairs".to_string())
    }
}

struct ThreadInit {
    inits: Vec<(Name, u64)>,
    reset: HashMap<Loc<Name>, exp::Exp<String>>,
    interrupts: Vec<Interrupt>,
}

fn parse_interrupt<B: BV>(
    value: &Value,
    symbolic_addrs: &HashMap<String, u64>,
    objdump: &Objdump,
    symtab: &Symtab,
    type_info: &IRTypeInfo,
    isa: &ISAConfig<B>,
) -> Result<Interrupt, String> {
    let at_str = value
        .get("at")
        .ok_or_else(|| "Interrupt must have an 'at' field".to_string())?
        .as_str()
        .ok_or_else(|| "Interrupt 'at' field must be a string")?;
    let Some(at) = label_from_objdump(at_str, objdump) else {
        return Err("Could not find interrupt 'at' label in threads".to_string());
    };

    let reset = if let Some(value) = value.get("reset") {
        parse_reset_registers(value, symbolic_addrs, symtab, type_info, isa)?
    } else {
        HashMap::default()
    };

    Ok(Interrupt { at, reset })
}

fn parse_thread_initialization<B: BV>(
    thread: &Value,
    symbolic_addrs: &HashMap<String, u64>,
    objdump: &Objdump,
    symtab: &Symtab,
    type_info: &IRTypeInfo,
    isa: &ISAConfig<B>,
) -> Result<ThreadInit, String> {
    let inits = if let Some(value) = thread.get("init") {
        let table =
            value.as_table().ok_or_else(|| "Thread init must be a list of register name/value pairs".to_string())?;
        table
            .iter()
            .map(|(reg, value)| parse_init(reg, value, symbolic_addrs, objdump, symtab, isa))
            .collect::<Result<_, _>>()?
    } else {
        Vec::new()
    };

    let reset = if let Some(reset) = thread.get("reset") {
        parse_reset_registers(reset, symbolic_addrs, symtab, type_info, isa)?
    } else {
        HashMap::new()
    };

    let interrupts = if let Some(value) = thread.get("interrupt") {
        let values = value.as_array().ok_or_else(|| "Thread interrupts must be an array of tables".to_string())?;
        values
            .iter()
            .map(|value| parse_interrupt(value, symbolic_addrs, objdump, symtab, type_info, isa))
            .collect::<Result<_, _>>()?
    } else {
        Vec::new()
    };

    Ok(ThreadInit { inits, reset, interrupts })
}

fn parse_self_modify_region<B: BV>(toml_region: &Value, objdump: &Objdump) -> Result<Region<B>, String> {
    let table = toml_region.as_table().ok_or("Each self_modify element must be a TOML table")?;
    let address =
        table.get("address").and_then(Value::as_str).ok_or("self_modify element must have a `address` field")?;
    let address = label_from_objdump(&address[0..(address.len() - 1)], objdump)
        .ok_or("address not parseable in self_modify element")?;

    let bytes =
        table.get("bytes").and_then(Value::as_integer).ok_or("self_modify element must have a `bytes` field")?;
    let upper = address + (bytes as u64);

    let values =
        table.get("values").and_then(Value::as_array).ok_or("self_modify element must have a `values` field")?;
    let values = values
        .iter()
        .map(|v| v.as_str().and_then(B::from_str).map(|bv| (bv.lower_u64(), bv.len())))
        .collect::<Option<Vec<_>>>()
        .ok_or("Could not parse `values` field")?;

    Ok(Region::Constrained(
        address..upper,
        Arc::new(move |solver: &mut Solver<B>| {
            use isla_lib::smt::smtlib::{bits64, Def, Exp, Ty};
            let v = solver.fresh();
            let exp: Exp<_> = values.iter().fold(Exp::Bool(false), |exp, (bits, len)| {
                Exp::Or(Box::new(Exp::Eq(Box::new(Exp::Var(v)), Box::new(bits64(*bits, *len)))), Box::new(exp))
            });
            solver.add(Def::DeclareConst(v, Ty::BitVec(bytes as u32 * 8)));
            solver.add(Def::Assert(exp));
            v
        }),
    ))
}

fn parse_self_modify<B: BV>(toml: &Value, objdump: &Objdump) -> Result<Vec<Region<B>>, String> {
    if let Some(value) = toml.get("self_modify") {
        let array = value.as_array().ok_or_else(|| "self_modify section must be a TOML array".to_string())?;
        Ok(array.iter().map(|v| parse_self_modify_region(v, objdump)).collect::<Result<_, _>>()?)
    } else {
        Ok(Vec::new())
    }
}

fn parse_extra<'v>(extra: (&'v String, &'v Value)) -> Result<UnassembledSection<'v>, String> {
    let addr =
        extra.1.get("address").and_then(|addr| addr.as_str()).ok_or_else(|| format!("No address in {}", extra.0))?;
    let code = extra.1.get("code").and_then(|code| code.as_str()).ok_or_else(|| format!("No code in {}", extra.0))?;
    Ok(UnassembledSection { name: extra.0, address: parse_address(addr)?, code })
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PageSetupLocation {
    line: usize,
    column: usize,
}

impl PageSetupLocation {
    fn new(source: &str, pos: usize) -> PageSetupLocation {
        // Find all the new lines
        let (source, _) = source.split_at(pos);
        let eol = "\n";
        let mut matches = source.rmatch_indices(eol);
        match matches.next() {
            Some((n, _)) => PageSetupLocation { line: 2 + matches.count(), column: pos - n },
            None => PageSetupLocation { line: 1, column: pos },
        }
    }
}

impl fmt::Display for PageSetupLocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line {} column {}", self.line, self.column)
    }
}

pub fn format_error_page_table_setup<T, E>(source: &str, error: lalrpop_util::ParseError<usize, T, E>) -> String
where
    T: fmt::Display,
    E: fmt::Display,
{
    error.map_location(|pos| PageSetupLocation::new(source, pos)).to_string()
}

#[derive(Clone)]
pub struct Interrupt {
    pub at: u64,
    pub reset: HashMap<Loc<Name>, exp::Exp<String>>,
}

#[derive(Clone)]
pub struct AssembledThread {
    pub name: ThreadName,
    pub address: u64,
    pub inits: Vec<(Name, u64)>,
    pub reset: HashMap<Loc<Name>, exp::Exp<String>>,
    pub interrupts: Vec<Interrupt>,
    pub code: Vec<u8>,
    pub source: String,
}

impl fmt::Debug for AssembledThread {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AssembledThread").field("name", &self.name).field("code", &self.code).finish()
    }
}

#[derive(Clone)]
pub struct IRThread {
    pub name: ThreadName,
    pub inits: Vec<(Name, u64)>,
    pub reset: HashMap<Loc<Name>, exp::Exp<String>>,
    pub call: Name,
}

impl fmt::Debug for IRThread {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IRThread").field("name", &self.name).field("call", &self.call).finish()
    }
}

/// We have to different types of Threads, either a thread in memory
/// that was assembled from some code, or a thread where we directly
/// call an IR function.
#[derive(Clone, Debug)]
pub enum Thread {
    Assembled(AssembledThread),
    IR(IRThread),
}

impl Thread {
    pub fn reset(&self) -> &HashMap<Loc<Name>, exp::Exp<String>> {
        match self {
            Thread::Assembled(t) => &t.reset,
            Thread::IR(t) => &t.reset,
        }
    }

    pub fn inits(&self) -> &[(Name, u64)] {
        match self {
            Thread::Assembled(t) => &t.inits,
            Thread::IR(t) => &t.inits,
        }
    }

    pub fn interrupts(&self) -> &[Interrupt] {
        match self {
            Thread::Assembled(t) => &t.interrupts,
            Thread::IR(_) => &[],
        }
    }
}

#[derive(Debug, Clone)]
pub struct AssembledSection {
    pub name: SectionName,
    pub address: u64,
    pub bytes: Vec<u8>,
    pub source: String,
}

#[derive(Debug, Clone)]
pub struct LitmusGraphOpts {
    pub force_show_events: Option<Vec<String>>,
    pub shows: Option<Vec<String>>,
}

#[derive(Debug)]
pub struct Litmus<B> {
    pub arch: String,
    pub name: String,
    pub hash: Option<String>,
    pub symbolic_addrs: HashMap<String, u64>,
    pub locations: HashMap<u64, u64>,
    pub sizeof: HashMap<String, u32>,
    pub page_table_setup_source: String,
    pub page_table_setup: Vec<page_table::setup::Constraint>,
    pub threads: Vec<Thread>,
    pub sections: Vec<AssembledSection>,
    pub self_modify_regions: Vec<Region<B>>,
    pub objdump: Objdump,
    pub final_assertion: exp::Exp<String>,
    pub graph_opts: LitmusGraphOpts,
}

impl<B: BV> Litmus<B> {
    pub fn log(&self) {
        log!(log::LITMUS, &format!("Litmus test name: {}", self.name));
        log!(log::LITMUS, &format!("Litmus test hash: {:?}", self.hash));
        log!(log::LITMUS, &format!("Litmus test symbolic addresses: {:?}", self.symbolic_addrs));
        log!(log::LITMUS, &format!("Litmus test data: {:#?}", self.threads));
        log!(log::LITMUS, &format!("Litmus test final assertion: {:?}", self.final_assertion));
    }

    pub fn parse(contents: &str, symtab: &Symtab, type_info: &IRTypeInfo, isa: &ISAConfig<B>) -> Result<Self, String> {
        let litmus_toml = match contents.parse::<Value>() {
            Ok(toml) => toml,
            Err(e) => return Err(format!("Error when parsing litmus: {}", e)),
        };

        let arch = litmus_toml
            .get("arch")
            .and_then(|n| n.as_str().map(str::to_string))
            .unwrap_or_else(|| "unknown".to_string());

        let name = litmus_toml
            .get("name")
            .and_then(|n| n.as_str().map(str::to_string))
            .ok_or_else(|| "No name found in litmus file".to_string())?;

        let hash = litmus_toml.get("hash").map(|h| h.to_string());

        let symbolic = litmus_toml
            .get("symbolic")
            .and_then(Value::as_array)
            .ok_or("No symbolic addresses found in litmus file")?;
        let mut symbolic_addrs: HashMap<String, u64> = symbolic
            .iter()
            .enumerate()
            .map(|(i, sym_addr)| match sym_addr.as_str() {
                Some(sym_addr) => {
                    Ok((sym_addr.to_string(), isa.symbolic_addr_base + (i as u64 * isa.symbolic_addr_stride)))
                }
                None => Err("Symbolic addresses must be strings"),
            })
            .collect::<Result<_, _>>()?;

        symbolic_addrs.insert("page_table_base".to_string(), isa.page_table_base);
        symbolic_addrs.insert("s2_page_table_base".to_string(), isa.s2_page_table_base);

        let locations = parse_locations(&litmus_toml, &symbolic_addrs)?;
        let sizeof = parse_sizeof_types(&litmus_toml)?;

        let (page_table_setup, page_table_setup_source) = if let Some(setup) = litmus_toml.get("page_table_setup") {
            if litmus_toml.get("locations").is_some() {
                return Err("Cannot have a page_table_setup and locations in the same test".to_string());
            }
            if let Some(litmus_setup) = setup.as_str() {
                let setup = format!("{}{}", isa.default_page_table_setup, litmus_setup);
                let lexer = page_table::setup_lexer::SetupLexer::new(&setup);
                (
                    page_table::setup_parser::SetupParser::new().parse(isa, lexer).map_err(|error| {
                        format_error_page_table_setup(
                            litmus_setup,
                            error.map_location(|pos| pos - isa.default_page_table_setup.len()),
                        )
                    })?,
                    litmus_setup.to_string(),
                )
            } else {
                return Err("page_table_setup must be a string".to_string());
            }
        } else {
            (Vec::new(), "".to_string())
        };

        let threads = litmus_toml.get("thread").and_then(|t| t.as_table()).ok_or("No threads found in litmus file")?;

        let mut thread_bodies: Vec<(ThreadName, ThreadBody)> = threads
            .iter()
            .map(|(thread_name, thread)| match thread.get("code") {
                Some(code) => code
                    .as_str()
                    .map(|code| (thread_name.to_string(), ThreadBody::Code(code)))
                    .ok_or_else(|| "thread code must be a string".to_string()),
                None => match thread.get("call") {
                    Some(call) => {
                        let call = call.as_str().ok_or_else(|| "Thread call must be a string".to_string())?;
                        let call = symtab
                            .get(&zencode::encode(call))
                            .ok_or_else(|| format!("Could not find function {}", call))?;
                        Ok((thread_name.to_string(), ThreadBody::Call(call)))
                    }
                    None => Err(format!("No code or call found for thread {}", thread_name)),
                },
            })
            .collect::<Result<_, _>>()?;

        let empty_table = toml::value::Map::new();
        let sections: &Table = litmus_toml.get("section").and_then(|t| t.as_table()).unwrap_or(&empty_table);
        let mut sections: Vec<UnassembledSection<'_>> = sections.iter().map(parse_extra).collect::<Result<_, _>>()?;
        sections.sort_unstable_by_key(|section| section.address);

        let (mut assembled, mut assembled_sections, objdump) = assemble(&thread_bodies, &sections, true, isa)?;

        let sections = assembled_sections
            .drain(..)
            .zip(sections.drain(..))
            .map(|((address, bytes), unassembled)| AssembledSection {
                name: unassembled.name.to_string(),
                address,
                bytes,
                source: unassembled.code.to_string(),
            })
            .collect();

        let mut inits: Vec<ThreadInit> = threads
            .iter()
            .map(|(_, thread)| parse_thread_initialization(thread, &symbolic_addrs, &objdump, symtab, type_info, isa))
            .collect::<Result<_, _>>()?;

        let threads: Vec<Thread> = thread_bodies
            .drain(..)
            .zip(inits.drain(..))
            .map(|((name, body), init)| match body {
                ThreadBody::Code(source) => {
                    let (address, code) =
                        assembled.remove(&name).ok_or(format!("Thread {} was not found in assembled threads", name))?;
                    Ok(Thread::Assembled(AssembledThread {
                        name,
                        address,
                        inits: init.inits,
                        reset: init.reset,
                        interrupts: init.interrupts,
                        code,
                        source: source.to_string(),
                    }))
                }
                ThreadBody::Call(call) => Ok(Thread::IR(IRThread { name, inits: init.inits, reset: init.reset, call })),
            })
            .collect::<Result<_, String>>()?;

        let mut self_modify_regions = parse_self_modify::<B>(&litmus_toml, &objdump)?;
        let mut constrained_regions = parse_constrained::<B>(&litmus_toml, &symbolic_addrs)?;
        self_modify_regions.append(&mut constrained_regions);

        let fin = litmus_toml.get("final").ok_or("No final section found in litmus file")?;
        let final_assertion = (match fin.get("assertion").and_then(Value::as_str) {
            Some(assertion) => {
                let lexer = exp_lexer::ExpLexer::new(assertion);
                exp_parser::ExpParser::new()
                    .parse(&sizeof, isa.default_sizeof, symtab, &isa.register_renames, lexer)
                    .map_err(|error| error.to_string())
            }
            None => Err("No final.assertion found in litmus file".to_string()),
        })?;

        let meta = litmus_toml.get("meta");

        let graph_opts_force_show_events = meta
            .and_then(|m| m.get("graph"))
            .and_then(|g| g.get("force_show_events"))
            .and_then(|t| t.as_array())
            .and_then(|a| a.iter().map(|v| v.as_str().map(|s| s.to_string())).collect());

        let graph_opts_shows = meta
            .and_then(|m| m.get("graph"))
            .and_then(|g| g.get("shows"))
            .and_then(|t| t.as_array())
            .and_then(|a| a.iter().map(|v| v.as_str().map(|s| s.to_string())).collect());

        let graph_opts = LitmusGraphOpts { force_show_events: graph_opts_force_show_events, shows: graph_opts_shows };

        Ok(Litmus {
            arch,
            name,
            hash,
            symbolic_addrs,
            locations,
            sizeof,
            page_table_setup_source,
            page_table_setup,
            threads,
            sections,
            self_modify_regions,
            objdump,
            final_assertion,
            graph_opts,
        })
    }

    pub fn latex(&self, output: &mut dyn Write, symtab: &Symtab) -> Result<(), Box<dyn Error>> {
        let id = self.latex_id();
        format::litmus_latex(output, self, &id, true, symtab)
    }

    pub fn from_file<P>(path: P, symtab: &Symtab, type_info: &IRTypeInfo, isa: &ISAConfig<B>) -> Result<Self, String>
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

        Self::parse(&contents, symtab, type_info, isa)
    }

    pub fn latex_id(&self) -> String {
        let mut name: String = self.name.clone();
        let replacements = [
            ("-", ""),
            ("_", ""),
            ("+", "plus"),
            (".", "dot"),
            ("=", "equals"),
            ("0", "zero"),
            ("1", "one"),
            ("2", "two"),
            ("3", "three"),
            ("4", "four"),
            ("5", "five"),
        ];

        for (a, b) in &replacements {
            name = name.replace(a, b);
        }

        name
    }
}
