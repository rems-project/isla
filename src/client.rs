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
use sha2::{Digest, Sha256};
use std::convert::TryFrom;
use std::io::prelude::*;
use std::os::unix::net::UnixStream;
use std::process::exit;
use std::sync::Arc;

use isla_axiomatic::litmus::assemble_instruction;
use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::executor;
use isla_lib::executor::{LocalFrame, TaskId, TaskState};
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::register::RegisterBindings;
use isla_lib::simplify::write_events;
use isla_lib::smt::Event;

mod opts;
use opts::CommonOpts;

enum Answer<'a> {
    Error,
    Version(&'a [u8]),
    StartTraces,
    Trace(bool, &'a [u8]),
    EndTraces,
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
    }
}

fn execute_opcode(
    stream: &mut UnixStream,
    opcode: B64,
    num_threads: usize,
    shared_state: &SharedState<B64>,
    register_state: &RegisterBindings<B64>,
    letbindings: &Bindings<B64>,
) -> std::io::Result<Result<(), String>> {
    let function_id = shared_state.symtab.lookup("zisla_client");
    let (args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task_state = TaskState::new();
    let task = LocalFrame::new(function_id, args, ret_ty, Some(&[Val::Bits(opcode)]), instrs)
        .add_lets(letbindings)
        .add_regs(register_state)
        .task(TaskId::fresh(), &task_state);

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
                let mut buf = Vec::new();
                let events: Vec<Event<B64>> = events.drain(..).rev().collect();
                write_events(&mut buf, &events, shared_state);
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
                write_answer(stream, Answer::Version(isla_lib::ISLA_VERSION.as_ref()))?;
            }

            ["stop"] => {
                // Protocol : Send nothing and shutdown
                break Ok(());
            }

            ["execute", instruction] => {
                // Protocol : Send StartTraces then any number of Trace then StopTraces
                if let Ok(opcode) = u32::from_str_radix(instruction, 16) {
                    let opcode = B64::from_u32(opcode);
                    match execute_opcode(stream, opcode, num_threads, shared_state, register_state, letbindings)? {
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

            ["execute_asm", instruction] => {
                // Protocol : Send StartTraces then any number of Trace then StopTraces
                if let Ok(bytes) = assemble_instruction(instruction, isa_config) {
                    let mut opcode: [u8; 4] = Default::default();
                    opcode.copy_from_slice(&bytes);
                    let opcode = B64::from_u32(u32::from_le_bytes(opcode));
                    match execute_opcode(stream, opcode, num_threads, shared_state, register_state, letbindings)? {
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
    let CommonOpts { num_threads, mut arch, symtab, type_info, isa_config, source_path: _ } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);
    let use_model_reg_init = !matches.opt_present("no-model-reg-init");

    let Initialized { regs, lets, shared_state } = initialize_architecture(
        &mut arch,
        symtab,
        type_info,
        &isa_config,
        AssertionMode::Optimistic,
        use_model_reg_init,
    );

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
