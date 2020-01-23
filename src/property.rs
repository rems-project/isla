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

use std::collections::HashMap;
use std::process::exit;
use std::sync::{Arc, Mutex};

use isla_lib::ir::*;
use isla_lib::executor;
use isla_lib::executor::Frame;
use isla_lib::init;
use isla_lib::smt::Checkpoint;
use isla_lib::zencode;

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
    opts.reqopt("p", "property", "check property in architecture", "<id>");
    opts.optflag("", "optimistic", "assume assertions succeed");

    let (matches, arch) = opts::parse(&opts);
    let CommonOpts { num_threads, mut arch, symtab, initial_registers, .. } = opts::parse_with_arch(&opts, &matches, &arch);

    let assertion_mode =
        if matches.opt_present("optimistic") { AssertionMode::Optimistic } else { AssertionMode::Pessimistic };

    let property = zencode::encode(&matches.opt_str("property").unwrap());

    insert_primops(&mut arch, assertion_mode);

    let register_state = initial_register_state(&arch, initial_registers);
    let letbindings = Mutex::new(HashMap::new());
    let shared_state = Arc::new(SharedState::new(symtab, &arch));

    init::initialize_letbindings(&arch, &shared_state, &register_state, &letbindings);

    let function_id = shared_state.symtab.lookup(&property);
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task = {
        let lets = letbindings.lock().unwrap();
        (Frame::new(args, register_state.clone(), lets.clone(), instrs), Checkpoint::new(), None)
    };
    let result = Arc::new(Mutex::new(true));

    executor::start_multi(num_threads, task, &shared_state, result.clone(), &executor::all_unsat_collector);

    let b = result.lock().unwrap();
    if *b {
        println!("ok");
        0
    } else {
        println!("fail");
        1
    }
}
