use crate::extract_state;

use std::convert::TryFrom;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::Write;
use std::path::Path;

#[derive(Debug)]
pub enum HarnessError {
    TooHard(String),
}
impl fmt::Display for HarnessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#?}", self)
    }
}
impl Error for HarnessError {}

pub fn make_file(base_name: String, initial_state: extract_state::InitialState, entry_reg: u32, exit_reg: u32) -> Result<(), Box<dyn std::error::Error>> {
    let mut asm_file = File::create(Path::new(&(base_name.clone() + ".s")))
        .expect("Unable to create .s file");
    let mut ld_file = File::create(Path::new(&(base_name.clone() + ".ld")))
        .expect("Unable to create .ld file");

    writeln!(ld_file, "SECTIONS {{")?;

    let mut name = 0;
    for (region, contents) in initial_state.memory.iter() {
        writeln!(ld_file, ".data{0} {1:#010x} : {{ *(data{0}) }}", name, region.start)?;
        writeln!(asm_file, ".section data{}, #alloc, #write", name)?;
        for byte in contents {
            writeln!(asm_file, "\t.byte {:#04x}", byte)?;
        }
        name += 1;
    }

    name = 0;
    for (region, contents) in initial_state.code.iter() {
        writeln!(ld_file, ".text{0} {1:#010x} : {{ *(text{0}) }}", name, region.start)?;
        writeln!(asm_file, ".section text{}, #alloc, #execinstr", name)?;
        if name == 0 {
            writeln!(asm_file, "test_start:")?;
        }
        for word in contents.chunks(4) {
            writeln!(asm_file, "\t.inst {:#010x}", u32::from_le_bytes(TryFrom::try_from(word)?))?;
        }
        name += 1;
    }
   
    writeln!(ld_file, ".text  0x10300000 : {{ *(.text) }}")?;
    writeln!(ld_file, "}}")?;
    writeln!(ld_file, "ENTRY(preamble)")?;
    writeln!(ld_file, "trickbox = 0x13000000;")?;

    writeln!(asm_file, ".text")?;
    writeln!(asm_file, ".global preamble")?;
    writeln!(asm_file, "preamble:")?;
    for (reg, value) in initial_state.gprs {
        writeln!(asm_file, "\tldr x{}, ={:#010x}", reg, value)?;
    }
    writeln!(asm_file, "\tldr x{}, =test_start", entry_reg)?;
    writeln!(asm_file, "\tldr x{}, =finish", exit_reg)?;
    writeln!(asm_file, "\tbr x{}", entry_reg)?;
    writeln!(asm_file, "finish:")?;
    writeln!(asm_file, "\tmov x0, #4")?;
    writeln!(asm_file, "\tldr x1, =trickbox")?;
    writeln!(asm_file, "\tstr x0, [x1]")?;

    Ok(())
}
