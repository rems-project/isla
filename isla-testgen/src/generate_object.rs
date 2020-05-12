use crate::extract_state;

use isla_lib::config::ISAConfig;

use std::convert::TryFrom;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::process::Command;

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

fn write_bytes(asm_file: &mut File, bytes: &Vec<u8>) -> Result<(), Box<dyn std::error::Error>> {
    for line in bytes.chunks(16) {
        write!(asm_file, "\t.byte")?;
        let mut byte_iter = line.iter();
        if let Some(byte) = byte_iter.next() {
            write!(asm_file, " {:#04x}", byte)?;
            for byte in byte_iter {
                write!(asm_file, ", {:#04x}", byte)?;
            }
        }
        writeln!(asm_file, "")?;
    }
    Ok(())
}

pub fn make_asm_files(
    base_name: String,
    pre_post_states: extract_state::PrePostStates,
    entry_reg: u32,
    exit_reg: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut asm_file = File::create(Path::new(&(base_name.clone() + ".s"))).expect("Unable to create .s file");
    let mut ld_file = File::create(Path::new(&(base_name.clone() + ".ld"))).expect("Unable to create .ld file");

    writeln!(ld_file, "SECTIONS {{")?;

    let mut name = 0;
    for (region, contents) in pre_post_states.pre_memory.iter() {
        writeln!(ld_file, ".data{0} {1:#010x} : {{ *(data{0}) }}", name, region.start)?;
        writeln!(asm_file, ".section data{}, #alloc, #write", name)?;
        write_bytes(&mut asm_file, contents)?;
        name += 1;
    }
    writeln!(ld_file, ".data {:#010x} : {{ *(data) }}", 0x00100000u64)?; /* TODO: parametrise */
    name = 0;
    for (_region, contents) in pre_post_states.post_memory.iter() {
        writeln!(asm_file, ".data")?;
        writeln!(asm_file, "check_data{}:", name)?;
        write_bytes(&mut asm_file, contents)?;
        name += 1;
    }

    name = 0;
    for (region, contents) in pre_post_states.code.iter() {
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
    for (reg, value) in pre_post_states.pre_gprs {
        writeln!(asm_file, "\tldr x{}, ={:#010x}", reg, value)?;
    }
    writeln!(asm_file, "\tmov x{}, #{:#010x}", entry_reg, pre_post_states.pre_nzcv << 28)?;
    writeln!(asm_file, "\tmsr nzcv, x{}", entry_reg)?;
    writeln!(asm_file, "\tldr x{}, =test_start", entry_reg)?;
    writeln!(asm_file, "\tldr x{}, =finish", exit_reg)?;
    writeln!(asm_file, "\tbr x{}", entry_reg)?;
    writeln!(asm_file, "finish:")?;
    /* Check the processor flags before they're trashed */
    if pre_post_states.post_nzcv_mask == 0 {
        writeln!(asm_file, "\t/* No processor flags to check */")?;
    } else {
        writeln!(asm_file, "\t/* Check processor flags */")?;
        writeln!(asm_file, "\tmrs x{}, nzcv", entry_reg)?;
        writeln!(asm_file, "\tubfx x{0}, x{0}, #28, #4", entry_reg)?;
        writeln!(asm_file, "\tand x{0}, x{0}, #{1:#03x}", entry_reg, pre_post_states.post_nzcv_mask)?;
        writeln!(asm_file, "\tcmp x{}, #{:#03x}", entry_reg, pre_post_states.post_nzcv_value)?;
        writeln!(asm_file, "\tb.ne comparison_fail")?;
    }
    writeln!(asm_file, "\t/* Check registers */")?;
    for (reg, value) in pre_post_states.post_gprs {
        writeln!(asm_file, "\tldr x{}, ={:#010x}", entry_reg, value)?;
        writeln!(asm_file, "\tcmp x{}, x{}", entry_reg, reg)?;
        writeln!(asm_file, "\tb.ne comparison_fail")?;
    }
    writeln!(asm_file, "\t/* Check memory */")?;
    let mut name = 0;
    for (region, _contents) in pre_post_states.post_memory.iter() {
        writeln!(asm_file, "\tldr x0, ={:#010x}", region.start)?;
        writeln!(asm_file, "\tldr x1, =check_data{}", name)?;
        writeln!(asm_file, "\tldr x2, ={:#010x}", region.end)?;
        writeln!(asm_file, "check_data_loop{}:", name)?;
        writeln!(asm_file, "\tldrb w3, [x0], #1")?;
        writeln!(asm_file, "\tldrb w4, [x1], #1")?;
        writeln!(asm_file, "\tcmp x3, x4")?;
        writeln!(asm_file, "\tb.ne comparison_fail")?;
        writeln!(asm_file, "\tcmp x0, x2")?;
        writeln!(asm_file, "\tb.ne check_data_loop{}", name)?;
        name += 1;
    }
    writeln!(asm_file, "\t/* Done, print message */")?;
    writeln!(asm_file, "\tldr x0, =ok_message")?;
    writeln!(asm_file, "\tb write_tube")?;
    writeln!(asm_file, "comparison_fail:")?;
    writeln!(asm_file, "\tldr x0, =fail_message")?;
    writeln!(asm_file, "write_tube:")?;
    writeln!(asm_file, "\tldr x1, =trickbox")?;
    writeln!(asm_file, "write_tube_loop:")?;
    writeln!(asm_file, "\tldrb w2, [x0], #1")?;
    writeln!(asm_file, "\tstrb w2, [x1]")?;
    writeln!(asm_file, "\tb write_tube_loop")?;

    writeln!(asm_file, "ok_message:")?;
    writeln!(asm_file, "\t.ascii \"OK\\n\\004\"")?;
    writeln!(asm_file, "fail_message:")?;
    writeln!(asm_file, "\t.ascii \"FAILED\\n\\004\"")?;

    Ok(())
}

pub fn build_elf_file<B>(isa: &ISAConfig<B>, base_name: String) {
    let assembler_result = Command::new(&isa.assembler)
        .args(&["-o", &(base_name.clone() + ".o"), &(base_name.clone() + ".s")])
        .status()
        .expect("Failed to run assembler");

    if !assembler_result.success() {
        panic!("Assembler returned bad result code: {}", assembler_result);
    }

    let linker_result = Command::new(&isa.linker)
        .args(&[
            "-o",
            &(base_name.clone() + ".elf"),
            "-T",
            &(base_name.clone() + ".ld"),
            "-n",
            &(base_name.clone() + ".o"),
        ])
        .status()
        .expect("Failed to run linker");

    if !linker_result.success() {
        panic!("Linker returned bad result code: {}", linker_result);
    }
}
