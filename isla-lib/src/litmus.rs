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
use std::process::{Command, Stdio};
use toml::Value;

use crate::config::ISAConfig;
use crate::log;

/// We have a special purpose temporary file module which is used to
/// create the output file for each assembler/linker invocation. Each
/// call to new just creates a new file name using our PID and a
/// unique counter. This file isn't opened until we read it, after the
/// assembler has created the object file. Dropping the `TmpFile`
/// removes the file if it exists.
mod tmpfile {
    use std::env;
    use std::fs::{remove_file, OpenOptions};
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
fn generate_linker_script(threads: &[(ThreadName, &str)], isa: &ISAConfig) -> String {
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
/// `ISAConfig` on this code. The generated ELF is then read in and
/// the assembled code is returned as a vector of bytes corresponding
/// to it's section in the ELF file as given by the thread name. If
/// `reloc` is true, then we will also invoke the linker to place each
/// thread's section at the correct address.
fn assemble(
    threads: &[(ThreadName, &str)],
    reloc: bool,
    isa: &ISAConfig,
) -> Result<Vec<(ThreadName, Vec<u8>)>, String> {
    use goblin::Object;

    let objfile = tmpfile::TmpFile::new();

    let mut assembler = Command::new(&isa.assembler)
        .arg("-o")
        .arg(objfile.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
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

    let _ = assembler.wait_with_output().or_else(|_| Err("Failed to read stdout from assembler".to_string()))?;

    let mut objfile = if reloc {
        let objfile_reloc = tmpfile::TmpFile::new();
        let linker_script = tmpfile::TmpFile::new();
        {
            let mut fd = File::create(linker_script.path())
                .or_else(|_| Err("Failed to create temp file for linker script".to_string()))?;
            fd.write_all(generate_linker_script(threads, isa).as_bytes())
                .or_else(|_| Err("Failed to write linker script".to_string()))?;
        }

        let linker_status = Command::new(&isa.linker)
            .arg("-T")
            .arg(linker_script.path())
            .arg("-o")
            .arg(objfile_reloc.path())
            .arg(objfile.path())
            .status()
            .or_else(|err| Err(format!("Failed to invoke linker {}. Got error: {}", &isa.linker.display(), err)))?;

        if linker_status.success() {
            objfile_reloc
        } else {
            return Err(format!("Linker failed with exit code {}", linker_status));
        }
    } else {
        objfile
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

    Ok(assembled)
}

pub fn assemble_instruction(instr: &str, isa: &ISAConfig) -> Result<Vec<u8>, String> {
    let instr = instr.to_owned() + "\n";
    if let [(_, bytes)] = assemble(&[("single".to_string(), &instr)], false, isa)?.as_slice() {
        Ok(bytes.to_vec())
    } else {
        Err(format!("Failed to assemble instruction {}", instr))
    }
}

pub struct Litmus {
    pub name: String,
    pub hash: Option<String>,
    pub assembled: Vec<(ThreadName, Vec<u8>)>,
}

pub fn collect_instrs(instrs: &mut HashMap<String, Vec<u8>>, code: &str, isa: &ISAConfig) -> Result<(), String> {
    for instr in code.trim().split('\n') {
        let opcode = assemble_instruction(instr, isa)?;
        instrs.insert(instr.trim().to_string(), opcode);
    }
    Ok(())
}

impl Litmus {
    pub fn log(&self) {
        log!(log::LITMUS, &format!("Litmus test name: {}", self.name));
        log!(log::LITMUS, &format!("Litmus test hash: {:?}", self.hash));
        log!(log::LITMUS, &format!("Litmus test data: {:#?}", self.assembled));
    }

    fn parse(contents: &str, isa: &ISAConfig) -> Result<Self, String> {
        let litmus_toml = match contents.parse::<Value>() {
            Ok(toml) => toml,
            Err(e) => return Err(format!("Error when parsing litmus: {}", e)),
        };

        let name = litmus_toml.get("name").ok_or("No name found in litmus file")?;

        let hash = litmus_toml.get("hash").map(|h| h.to_string());

        let threads = litmus_toml.get("thread").and_then(|t| t.as_table()).ok_or("No threads found in litmus file")?;

        let code: Vec<(ThreadName, &str)> = threads
            .iter()
            .map(|(thread_name, thread)| {
                thread
                    .get("code")
                    .and_then(|code| code.as_str().map(|code| (thread_name.to_string(), code)))
                    .ok_or_else(|| format!("No code found for thread {}", thread_name))
            })
            .collect::<Result<_, _>>()?;
        let assembled = assemble(&code, true, isa)?;

        Ok(Litmus { name: name.to_string(), hash, assembled })
    }

    pub fn from_file<P>(path: P, isa: &ISAConfig) -> Result<Self, String>
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

        Self::parse(&contents, isa)
    }
}
