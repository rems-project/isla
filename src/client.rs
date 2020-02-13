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

use crossbeam::queue::SegQueue;
use sha2::{Digest, Sha256};
use std::convert::TryFrom;
use std::io::prelude::*;
use std::os::unix::net::UnixStream;
use std::process::exit;
use std::sync::Arc;
use std::time::Instant;

use isla_lib::concrete::{B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::executor;
use isla_lib::executor::LocalFrame;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::litmus::assemble_instruction;
use isla_lib::simplify::write_events;
use isla_lib::smt::Event;

mod opts;
use opts::CommonOpts;

fn read_message<R: Read>(reader: &mut R) -> std::io::Result<String> {
    let mut length_buf: [u8; 4] = [0; 4];
    reader.read_exact(&mut length_buf)?;
    // Use i32 because OCaml doesn't have a u32 type in its stdlib
    let length = i32::from_le_bytes(length_buf);

    let mut buf = vec![0; usize::try_from(length).expect("message length invalid")];
    reader.read_exact(&mut buf)?;
    Ok(String::from_utf8_lossy(&buf).to_string())
}

fn write_message<W: Write>(writer: &mut W, message: &[u8]) -> std::io::Result<()> {
    let length: [u8; 4] = i32::to_le_bytes(i32::try_from(message.len()).expect("message length invalid"));
    writer.write_all(&length)?;
    writer.write_all(message)?;
    Ok(())
}

fn execute_opcode(
    stream: &mut UnixStream,
    opcode: B64,
    num_threads: usize,
    shared_state: &SharedState<B64>,
    register_state: &Bindings<B64>,
    letbindings: &Bindings<B64>,
) -> std::io::Result<Result<(), String>> {
    let function_id = shared_state.symtab.lookup("zisla_footprint");
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task = LocalFrame::new(args, Some(&[Val::Bits(opcode)]), instrs)
        .add_lets(&letbindings)
        .add_regs(&register_state)
        .task(0);

    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(num_threads, vec![task], &shared_state, queue.clone(), &executor::trace_result_collector);
    eprintln!("Execution took: {}ms", now.elapsed().as_millis());

    Ok(loop {
        match queue.pop() {
            Ok(Ok((_, result, mut events))) => {
                let mut buf = Vec::new();
                let events: Vec<Event<B64>> = events.drain(..).rev().collect();
                write_events(&mut buf, &events, &shared_state.symtab);
                write!(&mut buf, "{}", result)?;
                write_message(stream, &buf)?
            }
            Ok(Err(msg)) => break Err(msg),
            Err(_) => {
                write_message(stream, b"done")?;
                break Ok(());
            }
        }
    })
}

fn interact(
    stream: &mut UnixStream,
    num_threads: usize,
    shared_state: &SharedState<B64>,
    register_state: &Bindings<B64>,
    letbindings: &Bindings<B64>,
    isa_config: &ISAConfig<B64>,
) -> std::io::Result<Result<(), String>> {
    Ok(loop {
        let message = read_message(stream)?;
        match *message.splitn(2, ' ').collect::<Vec<&str>>().as_slice() {
            ["version", _] => {
                write_message(stream, env!("GIT_COMMIT").as_bytes())?;
            }

            ["execute", instruction] => {
                if let Ok(opcode) = u32::from_str_radix(&instruction, 64) {
                    let opcode = B64::from_u32(opcode);
                    match execute_opcode(stream, opcode, num_threads, shared_state, register_state, letbindings)? {
                        Ok(()) => continue,
                        Err(msg) => break Err(msg),
                    }
                } else {
                    break Err(format!("Could not parse opcode {}", &instruction));
                }
            }

            ["execute_asm", instruction] => {
                if let Ok(bytes) = assemble_instruction(&instruction, &isa_config) {
                    let mut opcode: [u8; 4] = Default::default();
                    opcode.copy_from_slice(&bytes);
                    let opcode = B64::from_u32(u32::from_le_bytes(opcode));
                    match execute_opcode(stream, opcode, num_threads, shared_state, register_state, letbindings)? {
                        Ok(()) => continue,
                        Err(msg) => break Err(msg),
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
    let CommonOpts { num_threads, mut arch, symtab, isa_config } =
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
            1
        }
        Err(io_error) => {
            eprintln!("{}", io_error);
            2
        }
    }
}
