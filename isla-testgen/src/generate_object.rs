use crate::extract_state;

use std::convert::TryFrom;
use std::fs::File;
use std::io::Write;
use std::path::Path;

pub fn make_file(base_name: String, initial_state: extract_state::InitialState) -> Result<(), Box<dyn std::error::Error>> {
    let mut asm_file = File::create(Path::new(&(base_name.clone() + ".s")))
        .expect("Unable to create .s file");
    let mut ld_file = File::create(Path::new(&(base_name.clone() + ".ld")))
        .expect("Unable to create .ld file");

    writeln!(ld_file, "SECTIONS {{")?;

    // TODO: either support multiple regions properly, or restrict the initial state to just one.
    let mut name = 0;
    for (region, contents) in initial_state.memory.iter() {
        writeln!(ld_file, ".data {:#010x} : {{ *(.data) }}", region.start)?;
        writeln!(asm_file, ".data")?;
        for byte in contents {
            writeln!(asm_file, "\t.byte {:#04x}", byte)?;
        }
        name += 1;
    }

    name = 0;
    for (region, contents) in initial_state.code.iter() {
        writeln!(ld_file, ".text {:#010x} : {{ *(.text) }}", region.start)?;
        writeln!(asm_file, ".text")?;
        for word in contents.chunks(4) {
            writeln!(asm_file, "\t.inst {:#010x}", u32::from_le_bytes(TryFrom::try_from(word)?))?;
        }
//        object.declare_with(format!("code{}", name), Decl::function(), contents.clone())?;
        name += 1;
    }
   
    writeln!(ld_file, "}}")?;

    Ok(())
}
