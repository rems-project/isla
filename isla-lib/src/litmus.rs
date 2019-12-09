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

use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::process::{Command, Stdio};
use toml::map::Map;
use toml::Value;

use crate::config::ISAConfig;

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
            remove_file(&self.path);
        }
    }
}

/// This function takes some assembly code, which should ideally be formatted as instructions
/// separated by a newline and a tab (\n\t), and invokes the assembler provided in the ISAConfig on
/// this code. The generated ELF is then read in and the assembled code is returned as a vector of
/// bytes corresponding to it's section in the ELF file.
fn assemble(code: &str, isa: &ISAConfig) -> Result<Vec<u8>, String> {
    use goblin::{error, Object};

    let mut tmpfile = tmpfile::TmpFile::new();

    let mut assembler = Command::new(&isa.assembler)
        .arg("-o")
        .arg(tmpfile.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .or_else(|err| Err(format!("Failed to spawn assembler {}. Got error: {}", &isa.assembler.display(), err)))?;

    // Write the code to the assembler's standard input, in a section called 'litmus'
    {
        let stdin = assembler.stdin.as_mut().ok_or("Failed to open stdin for assembler".to_string())?;
        stdin
            .write_all(b"\t.section litmus\n")
            .and_then(|_| stdin.write_all(code.as_bytes()))
            .or_else(|_| Err(format!("Failed to write to assembler input file {}", tmpfile.path().display())))?
    }

    let _ = assembler.wait_with_output().or(Err("Failed to read stdout from assembler".to_string()))?;

    let buffer = tmpfile.read_to_end().or(Err("Failed to read generated ELF file".to_string()))?;

    // Get the code from the generated ELF's litmus section
    let mut assembled: Option<&[u8]> = None;
    match Object::parse(&buffer) {
        Ok(Object::Elf(elf)) => {
            let shdr_strtab = elf.shdr_strtab;
            for section in elf.section_headers {
                match shdr_strtab.get(section.sh_name) {
                    Some(Ok("litmus")) => {
                        let offset = section.sh_offset as usize;
                        let size = section.sh_size as usize;
                        assembled = Some(&buffer[offset..(offset + size)])
                    }
                    _ => (),
                }
            }
        }
        Ok(_) => return Err("Generated object was not an ELF file".to_string()),
        Err(err) => return Err(format!("Failed to parse ELF file: {}", err)),
    };

    match assembled {
        Some(code) => Ok(code.to_vec()),
        None => Err("Could not find section with litmus thread in ELF file".to_string()),
    }
}

pub struct Litmus {
    name: String,
}

impl Litmus {
    fn parse(contents: &str, isa: &ISAConfig) -> Result<Self, String> {
        let litmus_toml = match contents.parse::<Value>() {
            Ok(toml) => toml,
            Err(e) => return Err(format!("Error when parsing litmus: {}", e)),
        };

        let threads = litmus_toml.get("thread").and_then(|t| t.as_table()).ok_or("No threads found in litmus file")?;
        for (tid, thread) in threads.iter() {
            let code =
                thread.get("code").and_then(|code| code.as_str()).ok_or(format!("No code found for thread {}", tid))?;
            assemble(code, isa)?;
            println!("{}", tid)
        }

        Ok(Litmus { name: "Litmus".to_string() })
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
