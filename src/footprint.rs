// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
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

use crossbeam::queue::SegQueue;
use sha2::{Digest, Sha256};
use std::convert::TryInto;
use std::process::exit;
use std::sync::Arc;
use std::time::Instant;

use isla_axiomatic::footprint_analysis::footprint_analysis;
use isla_axiomatic::litmus::assemble_instruction;
use isla_lib::concrete::{bitvector64::B64, BV};
use isla_lib::executor;
use isla_lib::executor::{LocalFrame, TaskState};
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::memory::Memory;
use isla_lib::smt::{EvPath, Event};
use isla_lib::zencode;
use isla_lib::{simplify, simplify::WriteOpts};

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

pub fn hex_bytes(s: &str) -> Result<Vec<u8>, std::num::ParseIntError> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16)).collect()
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.reqopt("i", "instruction", "display footprint of instruction", "<instruction>");
    opts.optopt("e", "endianness", "instruction encoding endianness (default: little)", "big/little");
    opts.optflag("d", "dependency", "view instruction dependency info");
    opts.optflag("x", "hex", "parse instruction as hexadecimal opcode, rather than assembly");
    opts.optflag("s", "simplify", "simplify instruction footprint");
    opts.optopt("f", "function", "use a custom footprint function", "<identifer>");
    opts.optflag("c", "continue-on-error", "continue generating traces upon encountering an error");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse(&mut hasher, &opts);
    let CommonOpts { num_threads, mut arch, symtab, isa_config } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    let little_endian = match matches.opt_str("endianness").as_deref() {
        Some("little") | None => true,
        Some("big") => false,
        Some(_) => {
            eprintln!("--endianness argument must be one of either `big` or `little`");
            exit(1)
        }
    };

    let instruction = matches.opt_str("instruction").unwrap();

    let opcode = if matches.opt_present("hex") {
        match hex_bytes(&instruction) {
            Ok(opcode) => opcode,
            Err(e) => {
                eprintln!("Could not parse hexadecimal opcode: {}", e);
                exit(1)
            }
        }
    } else {
        match assemble_instruction(&instruction, &isa_config) {
            Ok(opcode) => opcode,
            Err(msg) => {
                eprintln!("{}", msg);
                return 1;
            }
        }
    };

    if opcode.len() > 8 {
        eprintln!("Currently instructions greater than 8 bytes in length are not supported");
        return 1;
    }

    let opcode = if opcode.len() == 2 {
        let opcode: Box<[u8; 2]> = opcode.into_boxed_slice().try_into().unwrap();
        B64::from_u16(if little_endian { u16::from_le_bytes(*opcode) } else { u16::from_be_bytes(*opcode) })
    } else if opcode.len() == 4 {
        let opcode: Box<[u8; 4]> = opcode.into_boxed_slice().try_into().unwrap();
        B64::from_u32(if little_endian { u32::from_le_bytes(*opcode) } else { u32::from_be_bytes(*opcode) })
    } else {
        B64::from_bytes(&opcode)
    };

    eprintln!("opcode: {}", opcode);

    let mut memory = Memory::new();
    memory.add_zero_region(0x0..0xffff_ffff_ffff_ffff);

    let footprint_function = match matches.opt_str("function") {
        Some(id) => zencode::encode(&id),
        None => "zisla_footprint".to_string(),
    };

    let function_id = shared_state.symtab.lookup(&footprint_function);
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task_state = TaskState::new();
    let task = LocalFrame::new(function_id, args, Some(&[Val::Bits(opcode)]), instrs)
        .add_lets(&lets)
        .add_regs(&regs)
        .set_memory(memory)
        .task(0, &task_state);

    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(num_threads, None, vec![task], &shared_state, queue.clone(), &executor::trace_collector);
    eprintln!("Execution took: {}ms", now.elapsed().as_millis());

    let mut paths = Vec::new();
    let rk_ifetch = shared_state.enum_member(isa_config.ifetch_read_kind).expect("Invalid ifetch read kind");

    loop {
        match queue.pop() {
            Ok(Ok((_, mut events))) if matches.opt_present("dependency") => {
                let mut events: EvPath<B64> = events
                    .drain(..)
                    .rev()
                    .filter(|ev| {
                        (ev.is_memory() && !ev.has_read_kind(rk_ifetch))
                            || ev.is_smt()
                            || ev.is_instr()
                            || ev.is_cycle()
                            || ev.is_write_reg()
                    })
                    .collect();
                simplify::remove_unused(&mut events);
                paths.push(events)
            }
            Ok(Ok((_, mut events))) => {
                if matches.opt_present("simplify") {
                    simplify::hide_initialization(&mut events);
                    simplify::remove_unused(&mut events);
                }
                let events: Vec<Event<B64>> = events.drain(..).rev().collect();
                let stdout = std::io::stdout();
                let mut handle = stdout.lock();
                let write_opts = WriteOpts { define_enum: !matches.opt_present("simplify"), ..WriteOpts::default() };
                simplify::write_events_with_opts(&mut handle, &events, &shared_state.symtab, &write_opts).unwrap();
            }
            // Error during execution
            Ok(Err(msg)) => {
                eprintln!("{}", msg);
                if !matches.opt_present("continue-on-error") {
                    return 1;
                }
            }
            // Empty queue
            Err(_) => break,
        }
    }

    if matches.opt_present("dependency") {
        match footprint_analysis(num_threads, &[paths], &lets, &regs, &shared_state, &isa_config, None) {
            Ok(footprints) => {
                for (_, footprint) in footprints {
                    {
                        let stdout = std::io::stdout();
                        let mut handle = stdout.lock();
                        let _ = footprint.pretty(&mut handle, &shared_state.symtab);
                    }
                }
            }
            Err(footprint_error) => {
                eprintln!("{:?}", footprint_error);
                return 1;
            }
        }
    }

    0
}
