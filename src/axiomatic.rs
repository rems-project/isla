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
use serde::de::DeserializeOwned;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::env;
use std::error::Error;
use std::fs;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::process;
use std::process::Command;
use std::sync::Arc;
use std::time::Instant;

use isla_cat::cat;
use isla_cat::smt::compile_cat;

use isla_axiomatic::axiomatic::model::Model;
use isla_axiomatic::axiomatic::relations;
use isla_axiomatic::axiomatic::run_litmus;
use isla_axiomatic::axiomatic::{AxEvent, ExecutionInfo, Pairs};
use isla_axiomatic::footprint_analysis::footprint_analysis;
use isla_axiomatic::sexp::SexpVal;
use isla_axiomatic::litmus::{instruction_from_objdump, Litmus};
use isla_axiomatic::smt_events::smt_of_candidate;
use isla_lib::log;
use isla_lib::concrete::{B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::serialize as ir_serialize;
use isla_lib::ir::*;
use isla_lib::memory::Memory;
use isla_lib::simplify::{write_events_with_opts, WriteOpts};
use isla_lib::smt::smtlib;
use isla_lib::smt::Event;

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
    
    let run_info = run_litmus::litmus_per_candidate(
        num_threads,
        &litmus,
        regs,
        lets,
        &shared_state,
        &isa_config,
        &cache,
        &|tid, candidate, footprints| {
            let exec = ExecutionInfo::from(&candidate, &shared_state).unwrap();

            let mut path = env::temp_dir();
            path.push(format!("isla_candidate_{}_{}.smt2", process::id(), tid));

            // Create the SMT file with all the thread traces and the cat model.
            {
                let mut fd = File::create(&path).unwrap();
                writeln!(&mut fd, "(set-option :produce-models true)");

                let mut enums = HashSet::new();
                for thread in candidate {
                    for event in *thread {
                        if let Event::Smt(smtlib::Def::DefineEnum(_, size)) = event {
                            enums.insert(*size);
                        }
                    }
                }

                for size in enums {
                    write!(&mut fd, "(declare-datatypes ((Enum{} 0)) ((", size).unwrap();
                    for i in 0..size {
                        write!(&mut fd, "(e{}_{})", size, i).unwrap()
                    }
                    writeln!(&mut fd, ")))").unwrap()
                }

                for thread in candidate {
                    write_events_with_opts(&mut fd, thread, &shared_state.symtab, &WriteOpts::smtlib()).unwrap()
                }

                // We want to make sure we can extract the values read and written by the model if they are
                // symbolic. Therefore we declare new variables that are guaranteed to appear in the generated model.
                for (name, event) in exec.events.iter().map(|ev| (&ev.name, ev.base)) {
                    match event {
                        Event::ReadMem { value, address, bytes, .. }
                        | Event::WriteMem { data: value, address, bytes, .. } => {
                            if let Val::Symbolic(v) = value {
                                writeln!(&mut fd, "(declare-const |{}:value| (_ BitVec {}))", name, bytes * 8).unwrap();
                                writeln!(&mut fd, "(assert (= |{}:value| v{}))", name, v).unwrap();
                            }
                            if let Val::Symbolic(v) = address {
                                // TODO handle non 64-bit physical addresses
                                writeln!(&mut fd, "(declare-const |{}:address| (_ BitVec 64))", name).unwrap();
                                writeln!(&mut fd, "(assert (= |{}:address| v{}))", name, v).unwrap();
                            }
                        }
                        _ => (),
                    }
                }

                smt_of_candidate(&mut fd, &exec, &litmus, footprints, &shared_state, &isa_config);

                compile_cat(&mut fd, &cat);

                writeln!(&mut fd, "(check-sat)");
                writeln!(&mut fd, "(get-model)");
            }

            let z3 = Command::new("z3").arg(&path).output().expect("Failed to execute z3");

            let z3_output = std::str::from_utf8(&z3.stdout).expect("z3 output was not utf-8 encoded");

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
