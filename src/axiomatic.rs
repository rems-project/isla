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

use sha2::{Digest, Sha256};
use crossbeam::queue::SegQueue;
use std::path::PathBuf;
use std::process;
use std::time::Instant;

use isla_axiomatic::run_litmus;
use isla_axiomatic::litmus::Litmus;
use isla_cat::cat;
use isla_lib::log;
use isla_lib::concrete::B64;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    process::exit(code)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum AxResult {
    Allowed,
    Forbidden,
    Error,
}

fn isla_main() -> i32 {
    use AxResult::*;
    let now = Instant::now();

    let mut opts = opts::common_opts();
    opts.reqopt("l", "litmus", "load a litmus file", "<file>");
    opts.reqopt("m", "model", "Memory model in cat format", "<path>");
    opts.reqopt("", "cache", "instruction encoding endianness (little default)", "<path>");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse(&mut hasher, &opts);
    let CommonOpts { num_threads, mut arch, symtab, isa_config } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let arch_hash = hasher.result();
    log!(log::VERBOSE, &format!("Archictecture + config hash: {:x}", arch_hash));
    log!(log::VERBOSE, &format!("Parsing took: {}ms", now.elapsed().as_millis()));

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    let cache = PathBuf::from(matches.opt_str("cache").unwrap());
    if !cache.is_dir() {
        eprintln!("Invalid cache directory");
        return 1
    }

    let litmus = match Litmus::from_file(matches.opt_str("litmus").unwrap(), &shared_state.symtab, &isa_config) {
        Ok(litmus) => litmus,
        Err(e) => {
            eprintln!("{}", e);
            return 1;
        }
    };

    let cat = match cat::load_cat(&matches.opt_str("model").unwrap()) {
        Ok(mut cat) => {
            cat.unshadow(&mut cat::Shadows::new());
            let mut tcx = cat::initial_tcx(isa_config.barriers.values().map(String::clone));
            match cat::infer_cat(&mut tcx, cat) {
                Ok(cat) => cat,
                Err(e) => {
                    eprintln!("Type error in cat: {:?}\n", e);
                    return 1;
                }
            }
        }
        Err(e) => {
            eprintln!("Error in cat file: {}\n", e);
            return 1;
        }
    };

    let result_queue = SegQueue::new();

    let _run_info = run_litmus::smt_output_per_candidate::<B64, _, _, ()>(
        num_threads,
        &litmus,
        &cat,
        regs,
        lets,
        &shared_state,
        &isa_config,
        &cache,
        &|_exec, _footprints, z3_output| {
            if z3_output.starts_with("sat") {
                result_queue.push(Allowed);
                eprintln!("Allowed")
            } else if z3_output.starts_with("unsat") {
                result_queue.push(Forbidden);
                eprintln!("Forbidden")
            } else {
                result_queue.push(Error);
                eprintln!("Error")
            }
            Ok(())
        },
    )
    .unwrap();

    let mut results: Vec<AxResult> = Vec::new();
    loop {
        match result_queue.pop() {
            Ok(result) => results.push(result),
            Err(_) => break,
        }
    }

    if results.contains(&Error) {
        println!("{} Error {}ms", litmus.name, now.elapsed().as_millis());
    } else if results.contains(&Allowed) {
        println!("{} Allowed {}ms", litmus.name, now.elapsed().as_millis());
    } else if results.contains(&Forbidden) {
        println!("{} Forbidden {}ms", litmus.name, now.elapsed().as_millis());
    }

    0
}
