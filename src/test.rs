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
use std::sync::Arc;
use std::time::Instant;

use isla_lib::executor;
use isla_lib::executor::LocalFrame;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::litmus::Litmus;
use isla_lib::log;
use isla_lib::memory::Memory;

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.reqopt("l", "litmus", "load a litmus file", "<file>");

    let (matches, arch) = opts::parse(&opts);
    let CommonOpts { num_threads, mut arch, symtab, isa_config } = opts::parse_with_arch(&opts, &matches, &arch);

    let Initialized { regs, mut lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    let litmus = match Litmus::from_file(matches.opt_str("litmus").unwrap(), &isa_config) {
        Ok(litmus) => litmus,
        Err(e) => {
            eprintln!("{}", e);
            return 1;
        }
    };

    let mut memory = Memory::new();
    memory.add_concrete_region(isa_config.thread_base..isa_config.thread_top, HashMap::new());

    let mut current_base = isa_config.thread_base;
    for (thread, code) in litmus.assembled.iter() {
        log!(log::VERBOSE, &format!("Thread {} @ 0x{:x}", thread, current_base));
        for (i, byte) in code.iter().enumerate() {
            memory.write_byte(current_base + i as u64, *byte)
        }
        current_base += isa_config.thread_stride
    }

    litmus.log();
    memory.log();

    let function_id = shared_state.symtab.lookup("zmain");
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    lets.insert(ELF_ENTRY, UVal::Init(Val::I128(isa_config.thread_base as i128)));
    let tasks: Vec<_> = litmus
        .assembled
        .iter()
        .enumerate()
        .map(|(i, _)| {
            let address = isa_config.thread_base + (isa_config.thread_stride * i as u64);
            lets.insert(ELF_ENTRY, UVal::Init(Val::I128(address as i128)));
            LocalFrame::new(args, Some(&[Val::Unit]), instrs)
                .add_lets(&lets)
                .add_regs(&regs)
                .set_memory(memory.clone())
                .task()
        })
        .collect();

    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(num_threads, tasks, &shared_state, queue.clone(), &executor::trace_collector);
    eprintln!("Execution took: {}ms", now.elapsed().as_millis());

    loop {
        match queue.pop() {
            Ok(Ok(_trace)) => (),
            // Error during execution
            Ok(Err(msg)) => {
                eprintln!("{}", msg);
                break 1;
            }
            // Empty queue
            Err(_) => break 0,
        }
    }
}
