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
use std::collections::HashMap;
use std::convert::TryFrom;
use std::io::prelude::*;
use std::os::unix::net::UnixStream;
use std::process::exit;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use isla_lib::concrete::Sbits;
use isla_lib::config::ISAConfig;
use isla_lib::executor;
use isla_lib::executor::Frame;
use isla_lib::init::initialize_letbindings;
use isla_lib::ir::*;
use isla_lib::litmus::assemble_instruction;
use isla_lib::memory::Memory;
use isla_lib::smt::Checkpoint;

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

fn write_message<W: Write>(writer: &mut W, message: &str) -> std::io::Result<()> {
    let length: [u8; 4] = i32::to_le_bytes(i32::try_from(message.len()).expect("message length invalid"));
    writer.write_all(&length)?;
    writer.write_all(message.as_bytes())?;
    Ok(())
}

fn execute_opcode(
    stream: &mut UnixStream,
    opcode: Sbits,
    num_threads: usize,
    shared_state: &SharedState,
    register_state: &Bindings,
    letbindings: &Mutex<Bindings>,
) -> std::io::Result<Result<(), String>> {
    let function_id = shared_state.symtab.lookup("zisla_footprint");
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task = {
        let lets = letbindings.lock().unwrap();
        (
            Frame::call(args, &[Val::Bits(opcode)], register_state.clone(), lets.clone(), Memory::new(), instrs),
            Checkpoint::new(),
            None,
        )
    };

    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(num_threads, task, &shared_state, queue.clone(), &executor::trace_collector);
    eprintln!("Execution took: {}ms", now.elapsed().as_millis());

    Ok(loop {
        match queue.pop() {
            Ok(Ok(trace)) => write_message(stream, &trace)?,
            Ok(Err(msg)) => break Err(msg),
            Err(_) => {
                write_message(stream, "done")?;
                break Ok(());
            }
        }
    })
}

fn interact(
    stream: &mut UnixStream,
    num_threads: usize,
    shared_state: &SharedState,
    register_state: &Bindings,
    letbindings: &Mutex<Bindings>,
    isa_config: &ISAConfig,
) -> std::io::Result<Result<(), String>> {
    Ok(loop {
        let message = read_message(stream)?;
        match *message.splitn(2, ' ').collect::<Vec<&str>>().as_slice() {
            ["execute", instruction] => {
                if let Ok(opcode) = u32::from_str_radix(&instruction, 64) {
                    let opcode = Sbits::from_u32(opcode);
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
                    let opcode = Sbits::from_u32(u32::from_le_bytes(opcode));
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

    let (matches, arch) = opts::parse(&opts);
    let CommonOpts { num_threads, mut arch, symtab, isa_config } = opts::parse_with_arch(&opts, &matches, &arch);

    insert_primops(&mut arch, AssertionMode::Optimistic);

    let register_state = initial_register_state(&arch, &isa_config.default_registers);
    let letbindings = Mutex::new(HashMap::new());
    let shared_state = Arc::new(SharedState::new(symtab, &arch));

    initialize_letbindings(&arch, &shared_state, &register_state, &letbindings);

    let socket_path = matches.opt_str("socket").unwrap();
    let mut stream = match UnixStream::connect(&socket_path) {
        Ok(stream) => stream,
        Err(e) => {
            eprintln!("Could not connect to socket {}: {:?}", socket_path, e);
            return 1;
        }
    };

    match interact(&mut stream, num_threads, &shared_state, &register_state, &letbindings, &isa_config) {
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
