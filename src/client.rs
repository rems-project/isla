// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
// Copyright (c) 2020 Thibaut Pérami
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
use isla_lib::source_loc::SourceLoc;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::io::prelude::*;
use std::os::unix::net::UnixStream;
use std::process::exit;
use std::sync::Arc;

use isla_axiomatic::litmus::assemble_instruction;
use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::executor::{LocalFrame, TaskState};
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::register::RegisterBindings;
use isla_lib::simplify::write_events;
use isla_lib::smt::{smtlib, Checkpoint, Event, Solver};
use isla_lib::{executor, simplify, smt};

mod opts;
use opts::CommonOpts;

enum Answer<'a> {
    Error,
    Version(&'a [u8]),
    StartTraces,
    Trace(bool, &'a [u8]),
    EndTraces,
    Segments(&'a [u8]),
}

fn read_message<R: Read>(reader: &mut R) -> std::io::Result<String> {
    let mut length_buf: [u8; 4] = [0; 4];
    reader.read_exact(&mut length_buf)?;
    // Use i32 because OCaml doesn't have a u32 type in its stdlib
    let length = i32::from_le_bytes(length_buf);

    let mut buf = vec![0; usize::try_from(length).expect("message length invalid")];
    reader.read_exact(&mut buf)?;
    Ok(String::from_utf8_lossy(&buf).to_string())
}

fn write_slice<W: Write>(writer: &mut W, message: &[u8]) -> std::io::Result<()> {
    let length: [u8; 4] = i32::to_le_bytes(i32::try_from(message.len()).expect("message length invalid"));
    writer.write_all(&length)?;
    writer.write_all(message)?;
    Ok(())
}

fn write_answer<W: Write>(writer: &mut W, message: Answer) -> std::io::Result<()> {
    // The writing done here must match the parsing of IslaServer.read_basic_answer
    // in ReadDwarf
    match message {
        Answer::Error => {
            writer.write_all(&[0])?;
            Ok(())
        }
        Answer::Version(ver) => {
            writer.write_all(&[1])?;
            write_slice(writer, ver)?;
            Ok(())
        }
        Answer::StartTraces => {
            writer.write_all(&[2])?;
            Ok(())
        }
        Answer::Trace(b, trc) => {
            writer.write_all(&[3, u8::from(b)])?;
            write_slice(writer, trc)?;
            Ok(())
        }
        Answer::EndTraces => {
            writer.write_all(&[4])?;
            Ok(())
        }
        Answer::Segments(s) => {
            writer.write_all(&[5])?;
            write_slice(writer, s)?;
            Ok(())
        }
    }
}

#[derive(Clone, Debug)]
enum InstructionSegment<B> {
    Concrete(B),
    Symbolic(String, u32),
}

impl<B> From<B> for InstructionSegment<B> {
    fn from(value: B) -> Self {
        Self::Concrete(value)
    }
}

fn instruction_to_val<B: BV>(opcode: &[InstructionSegment<B>], solver: &mut Solver<B>, buf: &mut dyn Write) -> Val<B> {
    match opcode {
        [InstructionSegment::Concrete(bv)] => Val::Bits(*bv),
        _ => {
            write!(buf, "(segments").unwrap();
            let mut var_map = HashMap::new();
            let val = Val::MixedBits(
                opcode
                    .iter()
                    .map(|segment| match segment {
                        InstructionSegment::Concrete(bv) => BitsSegment::Concrete(*bv),
                        InstructionSegment::Symbolic(name, size) => {
                            if let Some((size2, v)) = var_map.get(name) {
                                if size == size2 {
                                    BitsSegment::Symbolic(*v)
                                } else {
                                    panic!(
                                        "{} appears in instruction with different sizes, {} and {}",
                                        name, size, size2
                                    )
                                }
                            } else {
                                let v = solver.declare_const(smtlib::Ty::BitVec(*size), SourceLoc::unknown());
                                write!(buf, "\n  (|{}| {} v{})", name, size, v).unwrap();
                                var_map.insert(name, (*size, v));
                                BitsSegment::Symbolic(v)
                            }
                        }
                    })
                    .collect(),
            );
            writeln!(buf, ")").unwrap();
            val
        }
    }
}

fn execute_opcode(
    stream: &mut UnixStream,
    opcode: &[InstructionSegment<B64>],
    num_threads: usize,
    shared_state: &SharedState<B64>,
    register_state: &RegisterBindings<B64>,
    letbindings: &Bindings<B64>,
) -> std::io::Result<Result<(), String>> {
    let mut segments_buf = Vec::new();
    let (initial_checkpoint, opcode_val) = {
        let solver_cfg = smt::Config::new();
        let solver_ctx = smt::Context::new(solver_cfg);
        let mut solver = Solver::new(&solver_ctx);
        let opcode_val = instruction_to_val(&opcode, &mut solver, &mut segments_buf);
        (smt::checkpoint(&mut solver), opcode_val)
    };

    if !segments_buf.is_empty() {
        write_answer(stream, Answer::Segments(&segments_buf))?;
    }

    let function_id = shared_state.symtab.lookup("zisla_client");
    let (args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task_state = TaskState::new();
    let task = LocalFrame::new(function_id, args, ret_ty, Some(&[opcode_val]), instrs)
        .add_lets(letbindings)
        .add_regs(register_state)
        .task_with_checkpoint(0, &task_state, initial_checkpoint);

    let queue = Arc::new(SegQueue::new());

    // This is for signalling that the answer will have multiple messages in the bool+trace format
    write_answer(stream, Answer::StartTraces)?;

    executor::start_multi(
        num_threads,
        None,
        vec![task],
        shared_state,
        queue.clone(),
        &executor::trace_result_collector,
    );

    Ok(loop {
        match queue.pop() {
            Some(Ok((_, result, mut events))) => {
                simplify::hide_initialization(&mut events);
                simplify::remove_unused(&mut events);
                simplify::propagate_forwards_used_once(&mut events);
                simplify::commute_extract(&mut events);
                simplify::eval(&mut events);

                let mut buf = Vec::new();
                let events: Vec<Event<B64>> = events.drain(..).rev().collect();
                write_events(&mut buf, &events, &shared_state.symtab);
                write_answer(stream, Answer::Trace(result, &buf))?;
            }
            Some(Err(msg)) => break Err(msg.to_string()),
            None => {
                write_answer(stream, Answer::EndTraces)?;
                break Ok(());
            }
        }
    })
}

fn interact(
    stream: &mut UnixStream,
    num_threads: usize,
    shared_state: &SharedState<B64>,
    register_state: &RegisterBindings<B64>,
    letbindings: &Bindings<B64>,
    isa_config: &ISAConfig<B64>,
) -> std::io::Result<Result<(), String>> {
    Ok(loop {
        // The parsing done here should match IslaServer.string_of_request of ReadDwarf
        let message = read_message(stream)?;
        let tmessage = message.trim();
        match *tmessage.splitn(2, ' ').collect::<Vec<&str>>().as_slice() {
            ["version"] => {
                // Protocol : Send a version answer
                write_answer(stream, Answer::Version(env!("ISLA_VERSION").as_ref()))?;
            }

            ["stop"] => {
                // Protocol : Send nothing and shutdown
                break Ok(());
            }

            ["execute", instruction] => {
                // Protocol : Send StartTraces then any number of Trace then StopTraces
                let Some(opcode): Option<Vec<_>> = instruction
                    .split_ascii_whitespace()
                    .map(|s| {
                        B64::from_str(s).map(InstructionSegment::Concrete).or_else(|| {
                            let mut it = s.split(':');
                            let name = it.next()?;
                            let size = it.next()?;
                            size.parse().ok().map(|size| InstructionSegment::Symbolic(name.to_string(), size))
                        })
                    })
                    .collect()
                else {
                    break Err(format!("Could not parse opcode {}", &instruction));
                };

                match execute_opcode(
                    stream,
                    &opcode,
                    num_threads,
                    shared_state,
                    register_state,
                    letbindings,
                )? {
                    Ok(()) => continue,
                    Err(msg) => {
                        eprintln!("{}", msg);
                        write_answer(stream, Answer::Error)?;
                        continue;
                    }
                }
            }

            ["execute_asm", instruction] => {
                // Protocol : Send StartTraces then any number of Trace then StopTraces
                if let Ok(bytes) = assemble_instruction(instruction, isa_config) {
                    let mut opcode: [u8; 4] = Default::default();
                    opcode.copy_from_slice(&bytes);
                    let opcode = B64::from_u32(u32::from_le_bytes(opcode));
                    match execute_opcode(
                        stream,
                        &[opcode.into()],
                        num_threads,
                        shared_state,
                        register_state,
                        letbindings,
                    )? {
                        Ok(()) => continue,
                        Err(msg) => {
                            eprintln!("{}", msg);
                            write_answer(stream, Answer::Error)?;
                            continue;
                        }
                    }
                } else {
                    break Err(format!("Could not parse opcode {}", &instruction));
                }
            }

            _ => break Err("Invalid command".to_string()),
        }
    })
}

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.reqopt("", "socket", "connect to server at location", "<path>");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse(&mut hasher, &opts);
    let CommonOpts { num_threads, mut arch, symtab, isa_config, source_path: _ } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    let socket_path = matches.opt_str("socket").unwrap();
    let mut stream = match UnixStream::connect(&socket_path) {
        Ok(stream) => stream,
        Err(e) => {
            eprintln!("Could not connect to socket {}: {:?}", socket_path, e);
            return 1;
        }
    };

    match interact(&mut stream, num_threads, &shared_state, &regs, &lets, &isa_config) {
        Ok(Ok(())) => 0,
        Ok(Err(isla_error)) => {
            eprintln!("{}", isla_error);
            write_answer(&mut stream, Answer::Error).unwrap();
            1
        }
        Err(io_error) => {
            eprintln!("{}", io_error);
            2
        }
    }
}
