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
use std::process::exit;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use isla_lib::ast::*;
use isla_lib::concrete::Sbits;
use isla_lib::executor;
use isla_lib::executor::Frame;
use isla_lib::init;
use isla_lib::litmus::assemble_instruction;
use isla_lib::smt::Checkpoint;

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

#[allow(clippy::mutex_atomic)]
fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.reqopt("i", "instruction", "display footprint of instruction", "instruction");
    opts.optopt("e", "endianness", "instruction encoding endianness (little default)", "big/little");
    opts.optflag("x", "hex", "parse instruction as hexadecimal opcode, rather than assembly");

    let (matches, arch) = opts::parse(&opts);
    let CommonOpts { num_threads, mut arch, symtab, isa_config } = opts::parse_with_arch(&opts, &matches, &arch);

    insert_primops(&mut arch, AssertionMode::Optimistic);

    let register_state = initial_register_state(&arch);
    let letbindings = Mutex::new(HashMap::new());
    let shared_state = Arc::new(SharedState::new(symtab, &arch));

    init::initialize_letbindings(&arch, &shared_state, &register_state, &letbindings);

    let little_endian = match matches.opt_str("endianness").as_ref().map(String::as_str) {
        Some("little") | None => true,
        Some("big") => false,
        Some(_) => {
            eprintln!("--endianness argument must be one of either `big` or `little`");
            exit(1)
        }
    };

    let instruction = matches.opt_str("instruction").unwrap();

    let opcode = if matches.opt_present("hex") {
        match u32::from_str_radix(&instruction, 16) {
            Ok(opcode) => opcode.to_le_bytes(),
            Err(e) => {
                eprintln!("Could not parse instruction: {}", e);
                exit(1)
            }
        }
    } else {
        match assemble_instruction(&instruction, &isa_config) {
            Ok(bytes) => {
                let mut opcode: [u8; 4] = Default::default();
                opcode.copy_from_slice(&bytes);
                opcode
            }
            Err(msg) => {
                eprintln!("{}", msg);
                return 1;
            }
        }
    };

    let opcode = Sbits::from_u32(if little_endian { u32::from_le_bytes(opcode) } else { u32::from_be_bytes(opcode) });
    eprintln!("opcode: {:#010x}", opcode.bits);

    let function_id = shared_state.symtab.lookup("zisla_footprint");
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task = {
        let lets = letbindings.lock().unwrap();
        (Frame::call(args, &[Val::Bits(opcode)], register_state.clone(), lets.clone(), instrs), Checkpoint::new(), None)
    };

    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(num_threads, task, &shared_state, queue.clone(), &executor::trace_collector);
    eprintln!("Execution took: {}ms", now.elapsed().as_millis());

    loop {
        match queue.pop() {
            Ok(Some(trace)) => println!("{}", trace),
            // Error during execution
            Ok(None) => break 1,
            // Empty queue
            Err(_) => break 0,
        }
    }
}
