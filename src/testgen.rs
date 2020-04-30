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

use isla_axiomatic::litmus::assemble_instruction;
use isla_lib::config::ISAConfig;
use isla_lib::init::{initialize_architecture, Initialized};
use rand::Rng;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::process::exit;

use isla_lib::concrete::{B64, BV};
use isla_lib::ir::*;
use isla_lib::memory::Memory;
use isla_lib::simplify::write_events;
use isla_lib::smt::Event;

use isla_testgen::asl_tag_files;
use isla_testgen::execution::*;
use isla_testgen::extract_state;
use isla_testgen::generate_object;

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn parse_instruction_masks(little_endian: bool, args: &Vec<String>) -> Vec<(&str, Option<u32>)> {
    let mut iter = args.iter().peekable();
    let mut v: Vec<(&str, Option<u32>)> = vec![];
    loop {
        let s = match iter.next() {
            None => break,
            Some(s) => s,
        };
        let p = iter.peek();
        let p = p.map(|r| *r);
        let m: Option<u32> = match p {
            None => None,
            Some(s) => {
                if s.starts_with("mask:") {
                    iter.next();
                    match u32::from_str_radix(&s[5..], 16) {
                        Ok(m) => Some(if little_endian { u32::from_le(m) } else { u32::from_be(m) }),
                        Err(e) => {
                            eprintln!("Could not parse mask: {}", e);
                            exit(1)
                        }
                    }
                } else {
                    None
                }
            }
        };
        v.push((s, m));
    }
    v
}

fn instruction_opcode(
    hex: bool,
    little_endian: bool,
    encodings: &asl_tag_files::Encodings,
    isa_config: &ISAConfig<B64>,
    instruction: &str,
) -> (B64, bool) {
    let (opcode, random) = if instruction == "_" {
        let (opcode, description) = encodings.random(asl_tag_files::Encoding::A64);
        println!("Instruction {:#010x}: {}", opcode, description);
        (opcode.to_le_bytes(), true)
    } else if hex {
        println!("Instruction {}", instruction);
        match u32::from_str_radix(&instruction, 16) {
            Ok(opcode) => (opcode.to_le_bytes(), false),
            Err(e) => {
                eprintln!("Could not parse instruction: {}", e);
                exit(1)
            }
        }
    } else {
        println!("Instruction {}", instruction);
        match assemble_instruction(&instruction, &isa_config) {
            Ok(bytes) => {
                let mut opcode: [u8; 4] = Default::default();
                opcode.copy_from_slice(&bytes);
                (opcode, false)
            }
            Err(msg) => {
                eprintln!("Could not assemble instruction: {}", msg);
                exit(1);
            }
        }
    };
    (B64::from_u32(if little_endian { u32::from_le_bytes(opcode) } else { u32::from_be_bytes(opcode) }), random)
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optopt("e", "endianness", "instruction encoding endianness (little default)", "big/little");
    opts.optflag("x", "hex", "parse instruction as hexadecimal opcode, rather than assembly");
    opts.optopt("T", "tag-file", "parse instruction encodings from tag file", "<file>");
    opts.optflag("", "events", "dump final events");
    opts.optflag("", "all-events", "dump events for every behaviour");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse(&mut hasher, &opts);

    let CommonOpts { num_threads, mut arch, symtab, isa_config } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let encodings = match matches.opt_str("tag-file") {
        Some(name) => asl_tag_files::read_tag_file(&name),
        None => asl_tag_files::Encodings::default(),
    };

    let register_types: HashMap<Name, Ty<Name>> = arch
        .iter()
        .filter_map(|d| match d {
            Def::Register(reg, ty) => Some((*reg, ty.clone())),
            _ => None,
        })
        .collect();

    let Initialized { regs, mut lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    lets.insert(ELF_ENTRY, UVal::Init(Val::I128(isa_config.thread_base as i128)));

    let little_endian = match matches.opt_str("endianness").as_ref().map(String::as_str) {
        Some("little") | None => true,
        Some("big") => false,
        Some(_) => {
            eprintln!("--endianness argument must be one of either `big` or `little`");
            exit(1)
        }
    };

    let dump_events = matches.opt_present("events");
    let dump_all_events = matches.opt_present("all-events");

    let symbolic_regions = [0x1000..0x2000];
    let symbolic_code_regions = [isa_config.thread_base..isa_config.thread_top];
    let mut memory = Memory::new();
    for r in &symbolic_regions {
        memory.add_symbolic_region(r.clone());
    }
    for r in &symbolic_code_regions {
        memory.add_symbolic_code_region(r.clone());
    }
    memory.log();

    let instructions = parse_instruction_masks(little_endian, &matches.free);

    let (frame, checkpoint) = init_model(&shared_state, lets, regs, &memory);
    let (mut frame, mut checkpoint, init_regs) = setup_init_regs(&shared_state, frame, checkpoint);

    let mut opcode_vars = vec![];

    let mut opcode_index = 0;
    let mut rng = rand::thread_rng();
    for (instruction, opcode_mask) in instructions {
        let mut random_attempts_left = 4;
        loop {
            let (opcode, repeat) =
                instruction_opcode(matches.opt_present("hex"), little_endian, &encodings, &isa_config, instruction);
            let mask_str = match opcode_mask {
                None => "none".to_string(),
                Some(m) => format!("{:#010x}", m),
            };
            eprintln!("opcode: {:#010x}  mask: {}", opcode.bits, mask_str);
            let (opcode_var, op_checkpoint) =
                setup_opcode(&shared_state, &frame, opcode, opcode_mask, checkpoint.clone());
            let mut continuations =
                run_model_instruction(num_threads, &shared_state, &frame, op_checkpoint, opcode_var, dump_all_events);
            let num_continuations = continuations.len();
            if num_continuations > 0 {
                let (f, c) = continuations.remove(rng.gen_range(0, num_continuations));
                eprintln!("{} successful execution(s)", num_continuations);
                opcode_vars.push((format!("opcode {}", opcode_index), RegSource::Symbolic(opcode_var)));
                opcode_index += 1;
                frame = f;
                checkpoint = c;
                break;
            } else {
                eprintln!("No successful executions");
                if repeat {
                    random_attempts_left -= 1;
                    if random_attempts_left == 0 {
                        eprintln!("Retried too many times");
                        exit(1);
                    }
                } else {
                    eprintln!("Unable to continue");
                    exit(1);
                }
            }
        }
    }

    let (entry_reg, exit_reg, checkpoint) = finalize(&shared_state, &frame, checkpoint);

    eprintln!("Complete");

    if dump_events {
        use isla_lib::simplify::simplify;
        let trace = checkpoint.trace().as_ref().expect("No trace!");
        let mut events = simplify(trace);
        let events: Vec<Event<B64>> = events.drain(..).map({ |ev| ev.clone() }).rev().collect();
        write_events(&mut std::io::stdout(), &events, &shared_state.symtab);
    }

    println!("Initial state:");
    interrogate_model(checkpoint.clone(), opcode_vars.iter().chain(init_regs.iter())).unwrap();

    println!("Sample final state:");
    interrogate_model(checkpoint.clone(), regs_for_state(&shared_state, frame).iter()).unwrap();

    println!("Initial state extracted from events:");
    let initial_state = extract_state::interrogate_model(
        checkpoint.clone(),
        &shared_state,
        &register_types,
        &symbolic_regions,
        &symbolic_code_regions,
    )
    .expect("Error extracting state");
    generate_object::make_asm_files(String::from("test"), initial_state, entry_reg, exit_reg)
        .expect("Error generating object file");
    generate_object::build_elf_file(&isa_config, String::from("test"));

    0
}
