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
use isla_axiomatic::run_litmus;
use isla_axiomatic::axiomatic::{AxEvent, ExecutionInfo, Pairs};
use isla_axiomatic::footprint_analysis::footprint_analysis;
use isla_axiomatic::sexp::SexpVal;
use isla_axiomatic::litmus::{instruction_from_objdump, Litmus};
use isla_axiomatic::smt_events::smt_of_candidate;
use isla_lib::concrete::{B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::serialize as ir_serialize;
use isla_lib::ir::*;
use isla_lib::memory::Memory;
use isla_lib::simplify::{write_events_with_opts, WriteOpts};
use isla_lib::smt::smtlib;
use isla_lib::smt::Event;

use getopts::Options;
mod request;
use request::{JsEvent, JsGraph, JsRelation, JsSet, Request, Response};


static THREADS: usize = 4;
static LIMIT_MEM_BYTES: u64 = 2048 * 1024 * 1024;
static LIMIT_CPU_SECONDS: u64 = 60;

fn setrlimit(resource: libc::__rlimit_resource_t, soft: u64, hard: u64) -> std::io::Result<()> {
    assert!(std::mem::size_of::<libc::rlim_t>() == 8);

    let ret = unsafe {
        libc::setrlimit(resource, &libc::rlimit { rlim_cur: soft as libc::rlim_t, rlim_max: hard as libc::rlim_t })
    };

    if ret == 0 {
        Ok(())
    } else {
        Err(std::io::Error::last_os_error())
    }
}

fn limit() -> std::io::Result<()> {
    setrlimit(libc::RLIMIT_AS, LIMIT_MEM_BYTES, LIMIT_MEM_BYTES)?;
    setrlimit(libc::RLIMIT_CPU, LIMIT_CPU_SECONDS, LIMIT_CPU_SECONDS)
}

/// Main just sets resource limits then calls handle_request to do the
/// actual work.
fn main() {
    if let Err(_) = limit() {
        eprintln!("Failed to set resource limits");
        std::process::exit(1)
    }

    let response = match handle_request() {
        Ok(resp) => match serde_json::to_vec(&resp) {
            Ok(resp) => resp,
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(1)
            }
        },
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1)
        }
    };

    unsafe { isla_lib::smt::finalize_solver() };

    let stdout = std::io::stdout();
    let mut handle = stdout.lock();
    handle.write_all(&response).unwrap()
}

fn deserialize_from_stdin<T: DeserializeOwned>() -> Option<T> {
    let stdin = std::io::stdin();
    let handle = stdin.lock();
    bincode::deserialize_from(handle).ok()
}

static ARCH_WHITELIST: [&str; 1] = ["aarch64"];

/// The error handling scheme is as follows. If we have an expected
/// error condition (i.e. a flaw in the user input), then that is
/// returned normally as part of the response using
/// Response::Error. This function either panics or returns Err on
/// unexpected errors.
fn handle_request() -> Result<Response, Box<dyn Error>> {
    let args: Vec<String> = std::env::args().collect();
    let mut opts = Options::new();
    opts.reqopt("", "resources", "path to resource files", "<path>");
    opts.reqopt("", "cache", "path to a cache directory", "<path>");

    let matches = opts.parse(&args[1..])?;

    // Log absolutely everything
    isla_lib::log::set_flags(0xffff_ffff);

    // The main server process sends the json from the AJAX request to
    // us via stdin. It should never be invalid.
    let req = deserialize_from_stdin::<Request>().expect("Invalid arguments");

    // Check that the request architecture is valid
    if !ARCH_WHITELIST.contains(&req.arch.as_str()) {
        panic!("Invalid architecture in request");
    }

    let resources = PathBuf::from(matches.opt_str("resources").unwrap());
    if !resources.is_dir() {
        panic!("Invalid resources directory");
    }

    let cache = PathBuf::from(matches.opt_str("cache").unwrap());
    if !cache.is_dir() {
        panic!("Invalid cache directory");
    }

    let now = Instant::now();

    let config_file = resources.join(format!("{}.toml", req.arch));
    let symtab_file = resources.join(format!("{}.symtab", req.arch));
    let ir_file = resources.join(format!("{}.irx", req.arch));

    let strings: Vec<String> = bincode::deserialize(&fs::read(&symtab_file)?)?;
    let symtab = Symtab::from_raw_table(&strings);

    let mut ir: Vec<Def<u32, B64>> = ir_serialize::deserialize(&fs::read(&ir_file)?).expect("Failed to deserialize IR");

    let isa_config: ISAConfig<B64> = ISAConfig::parse(&fs::read_to_string(&config_file)?, &symtab)?;

    eprintln!("Loaded architecture in: {}ms", now.elapsed().as_millis());

    let litmus = match Litmus::parse(&req.litmus, &symtab, &isa_config) {
        Ok(litmus) => litmus,
        Err(e) => return Ok(Response::Error { message: format!("Failed to process litmus file:\n{}\n", e) }),
    };
    litmus.log();

    let now = Instant::now();

    let parse_cat = match cat::ParseCat::from_string(&req.cat) {
        Ok(parse_cat) => parse_cat,
        Err(e) => {
            return Ok(Response::Error { message: format!("Parse error in cat: {}\n", e) });
        }
    };

    let cat = match cat::resolve_includes(&[], parse_cat) {
        Ok(mut cat) => {
            cat.unshadow(&mut cat::Shadows::new());
            let mut tcx = cat::initial_tcx(isa_config.barriers.values().map(String::clone));
            match cat::infer_cat(&mut tcx, cat) {
                Ok(cat) => cat,
                Err(e) => {
                    return Ok(Response::Error { message: format!("Type error in cat: {:?}\n", e) });
                }
            }
        }
        Err(e) => {
            return Ok(Response::Error { message: format!("Error in cat file: {}\n", e) });
        }
    };

    eprintln!("Parsed user input in: {}us", now.elapsed().as_micros());

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut ir, symtab, &isa_config, AssertionMode::Optimistic);

    let graph_queue = SegQueue::new();

    let run_info = run_litmus::smt_output_per_candidate(
        THREADS,
        &litmus,
        &cat,
        regs,
        lets,
        &shared_state,
        &isa_config,
        &cache,
        &|exec, footprints, z3_output| {
            if z3_output.starts_with("sat") {
                let mut event_names: Vec<&str> = exec.events.iter().map(|ev| ev.name.as_ref()).collect();
                event_names.push("IW");
                let model_buf = &z3_output[3..];
                let mut model = Model::<B64>::parse(&event_names, model_buf).expect("Failed to parse model");

                // We want to collect all the relations that were found by the SMT solver as part of the
                // model, as well as the addr/data/ctrl etc raltions we passed as input to the solver so we
                // can send them back to the client to be drawn.
                let mut relations: Vec<JsRelation> = Vec::new();

                let footprint_relations: [(&str, relations::DepRel<B64>); 3] =
                    [("addr", relations::addr), ("data", relations::data), ("ctrl", relations::ctrl)];

                for (name, rel) in footprint_relations.iter() {
                    let edges: Vec<(&AxEvent<B64>, &AxEvent<B64>)> = Pairs::from_slice(&exec.events)
                        .filter(|(ev1, ev2)| rel(ev1, ev2, &exec.thread_opcodes, footprints))
                        .collect();
                    relations.push(JsRelation {
                        name: name.to_string(),
                        edges: edges.iter().map(|(from, to)| (from.name.clone(), to.name.clone())).collect(),
                    })
                }

                let builtin_relations = vec!["rf", "co"];

                for rel in cat.relations().iter().chain(builtin_relations.iter()) {
                    let edges = model.interpret_rel(rel, &event_names).expect("Failed to interpret model");
                    eprintln!("{}: {:#?}", rel, edges);
                    relations.push(JsRelation {
                        name: rel.to_string(),
                        edges: edges.iter().map(|(from, to)| (from.to_string(), to.to_string())).collect(),
                    })
                }

                // Now we want to get the memory read and write values for each event
                let mut rw_values: HashMap<String, String> = HashMap::new();

                for event in exec.events.iter() {
                    fn interpret(
                        model: &mut Model<B64>,
                        ev: &str,
                        prefix: &str,
                        value: &Val<B64>,
                        bytes: u32,
                        address: &Val<B64>,
                    ) -> String {
                        let value = if value.is_symbolic() {
                            model
                                .interpret(&format!("{}:value", ev), &[])
                                .map(SexpVal::into_int_string)
                                .unwrap_or_else(|err| "?".to_string())
                        } else {
                            value.as_bits().map(|bv| bv.signed().to_string()).unwrap_or_else(|| "?".to_string())
                        };

                        let address = if address.is_symbolic() {
                            model
                                .interpret(&format!("{}:address", ev), &[])
                                .map(SexpVal::into_truncated_string)
                                .unwrap_or_else(|_| "?".to_string())
                        } else {
                            address.as_bits().map(|bv| format!("#x{:x}", bv.bits())).unwrap_or_else(|| "?".to_string())
                        };

                        format!("{} {} ({}): {}", prefix, address, bytes, value)
                    }

                    match event.base {
                        Event::ReadMem { value, address, bytes, .. } => {
                            rw_values.insert(
                                event.name.clone(),
                                interpret(&mut model, &event.name, "R", value, *bytes, address),
                            );
                        }
                        Event::WriteMem { data, address, bytes, .. } => {
                            rw_values.insert(
                                event.name.clone(),
                                interpret(&mut model, &event.name, "W", data, *bytes, address),
                            );
                        }
                        _ => (),
                    }
                }

                eprintln!("{:#?}", rw_values);

                graph_queue.push(JsGraph {
                    events: exec
                        .events
                        .iter()
                        .map(|ev| JsEvent::from_axiomatic(ev, &litmus.objdump, &mut rw_values))
                        .collect(),
                    sets: vec![],
                    relations,
                    show: vec![],
                });

                eprintln!("sat in: {}ms", now.elapsed().as_millis());
                Ok(())
            } else if z3_output.starts_with("unsat") {
                eprintln!("unsat in: {}ms", now.elapsed().as_millis());
                Ok(())
            } else {
                Err("z3_error".to_string())
            }
        },
    )
    .unwrap();

    let mut graphs: Vec<JsGraph> = Vec::new();
    loop {
        match graph_queue.pop() {
            Ok(graph) => graphs.push(graph),
            Err(_) => break,
        }
    }

    Ok(Response::Done {
        graphs,
        objdump: litmus.objdump,
        candidates: i32::try_from(run_info.candidates).expect("Candidates did not fit in i32"),
    })
}
