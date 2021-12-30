// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
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
use serde::de::DeserializeOwned;
use std::borrow::Cow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::convert::TryFrom;
use std::error::Error;
use std::fmt;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::Stdio;
use std::time::Instant;

use isla_cat::cat;

use isla_axiomatic::cat_config::tcx_from_config;
use isla_axiomatic::graph::{graph_from_z3_output, GraphOpts, GraphValueNames};
use isla_axiomatic::litmus::Litmus;
use isla_axiomatic::page_table::{name_initial_walk_bitvectors, VirtualAddress};
use isla_axiomatic::run_litmus;
use isla_axiomatic::run_litmus::LitmusRunOpts;
use isla_axiomatic::sandbox::SandboxedCommand;
use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::serialize as ir_serialize;
use isla_lib::ir::*;

use getopts::Options;
mod request;
use request::{JsGraph, JsRelation, Request, Response};

static THREADS: usize = 2;
static LIMIT_MEM_BYTES: u64 = 2048 * 1024 * 1024;
static LIMIT_CPU_SECONDS: u64 = 300;

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

#[derive(Debug)]
enum WebError {
    Z3Error(String),
    GraphError,
}

impl fmt::Display for WebError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            WebError::Z3Error(msg) => write!(f, "Z3 error: {}", msg),
            WebError::GraphError => write!(f, "Graph error"),
        }
    }
}

impl Error for WebError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// Main just sets resource limits then calls handle_request to do the
/// actual work.
fn main() {
    if limit().is_err() {
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

static ARCH_WHITELIST: [&str; 4] = ["aarch64", "aarch64-vmsa", "riscv32", "riscv64"];

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
    opts.optopt("", "litmus-convert", "path of .litmus to .toml file converter", "<path>");

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

    let mut cache = PathBuf::from(matches.opt_str("cache").unwrap());
    cache.push(&req.arch);
    fs::create_dir_all(&cache).expect("Failed to create cache directory if missing");
    if !cache.is_dir() {
        panic!("Invalid cache directory");
    }

    let now = Instant::now();

    let config_file = resources.join(format!("{}.toml", req.arch));
    let footprint_config_file = resources.join(format!("{}-footprint.toml", req.arch));
    let symtab_file = resources.join(format!("{}.symtab", req.arch));
    let ir_file = resources.join(format!("{}.irx", req.arch));

    let (strings, files): (Vec<String>, Vec<String>) = bincode::deserialize(&fs::read(&symtab_file)?)?;
    let symtab = Symtab::from_raw_table(&strings, &files);

    let mut ir: Vec<Def<Name, B64>> =
        ir_serialize::deserialize(&fs::read(&ir_file)?).expect("Failed to deserialize IR");

    let isa_config: ISAConfig<B64> = ISAConfig::parse(&fs::read_to_string(&config_file)?, &symtab)?;
    let footprint_config: ISAConfig<B64> = ISAConfig::parse(&fs::read_to_string(&footprint_config_file)?, &symtab)?;

    eprintln!("Loaded architecture in: {}ms", now.elapsed().as_millis());

    let litmus_text = if req.litmus_format == "toml" {
        Cow::Borrowed(req.litmus.as_str())
    } else if req.litmus_format == "litmus" {
        if let Some(converter_path) = matches.opt_str("litmus-convert").map(PathBuf::from) {
            let mut converter = SandboxedCommand::new(converter_path)
                .arg("--stdin")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()?;

            let stdin = converter.stdin.as_mut().unwrap();
            stdin.write_all(req.litmus.as_bytes())?;

            let output = converter.wait_with_output()?;

            if output.status.success() {
                Cow::Owned(dbg!(String::from_utf8_lossy(&output.stdout).to_string()))
            } else {
                panic!(".litmus converter failed!")
            }
        } else {
            panic!(".litmus file given with no converter!")
        }
    } else {
        return Ok(Response::Error { message: format!("Unrecognised litmus file format") });
    };

    let litmus = match Litmus::parse(&litmus_text, &symtab, &isa_config) {
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
            let mut tcx = tcx_from_config(&isa_config);
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

    let mut footprint_ir = ir.clone();

    let Initialized { regs: fregs, lets: flets, shared_state: fshared_state } =
        initialize_architecture(&mut footprint_ir, symtab.clone(), &footprint_config, AssertionMode::Optimistic);

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut ir, symtab, &isa_config, AssertionMode::Optimistic);

    let litmus_opts = LitmusRunOpts {
        num_threads: THREADS,
        timeout: None,
        ignore_ifetch: req.ignore_ifetch,
        exhaustive: req.exhaustive,
        armv8_page_tables: req.armv8_page_tables,
        merge_translations: if req.merge_translations { Some(req.merge_split_stages) } else { None },
        remove_uninteresting_translates: if req.remove_uninteresting { Some(true) } else { None },
    };

    let graph_opts = GraphOpts {
        compact: false,
        smart_layout: true,
        show_regs: HashSet::new(),
        flatten: false,
        debug: false,
        show_all_reads: true,
        shows: None,
        padding: None,
        force_show_events: None,
        force_hide_events: None,
        squash_translation_labels: false,
        control_delimit: true,
    };

    let graph_queue = SegQueue::new();

    let run_result = run_litmus::smt_output_per_candidate(
        "web",
        &litmus_opts,
        &litmus,
        &graph_opts,
        &cat,
        regs,
        lets,
        &shared_state,
        &isa_config,
        fregs,
        flets,
        &fshared_state,
        &footprint_config,
        &[],
        Some("(then dt2bv qe simplify bv)"),
        &cache,
        &|exec, memory, all_addrs, tables, footprints, z3_output| {
            if z3_output.starts_with("sat") {
                let mut names = GraphValueNames {
                    s1_ptable_names: HashMap::new(),
                    s2_ptable_names: HashMap::new(),
                    pa_names: HashMap::new(),
                    ipa_names: HashMap::new(),
                    va_names: HashMap::new(),
                    value_names: HashMap::new(),
                    addr_names: HashMap::new(),
                };

                // collect names from translation-table-walks for each VA
                for (table_name, (base, kind)) in tables {
                    for (va_name, va) in &litmus.symbolic_addrs {
                        name_initial_walk_bitvectors(
                            if kind == &"stage 1" {
                                &mut names.s1_ptable_names
                            } else if kind == &"stage 2" {
                                &mut names.s2_ptable_names
                            } else {
                                panic!("unknown table kind (must be stage 1 or stage 2)")
                            },
                            va_name,
                            VirtualAddress::from_u64(*va),
                            table_name,
                            *base,
                            memory,
                        )
                    }
                }

                // collect names for each IPA/PA variable in the pagetable
                for (name, val) in all_addrs {
                    if name.starts_with("pa") {
                        names.pa_names.insert(B64::new(*val, 64), name.clone());
                    } else if name.starts_with("ipa") {
                        names.ipa_names.insert(B64::new(*val, 64), name.clone());
                    } else {
                        names.va_names.insert(B64::new(*val, 64), name.clone());
                    }
                }

                match graph_from_z3_output(
                    &exec,
                    names,
                    footprints,
                    z3_output,
                    &litmus,
                    &cat,
                    !req.ignore_ifetch,
                    &graph_opts,
                    &shared_state.symtab,
                ) {
                    Ok(graph) => {
                        let dot = format!("{}", graph);
                        let (prefix, suffix) = dot.split_once('\x1D').ok_or_else(|| WebError::GraphError)?;
                        let (relations_string, suffix) =
                            suffix.split_once('\x1D').ok_or_else(|| WebError::GraphError)?;

                        let mut relations = Vec::new();
                        for relation in relations_string[1..].split('\x1E') {
                            let (name, dot) = relation.split_once('\x1F').ok_or_else(|| WebError::GraphError)?;
                            relations.push(JsRelation { name: name.to_string(), dot: dot.to_string() })
                        }

                        graph_queue.push(JsGraph { prefix: prefix.to_string(), relations, suffix: suffix.to_string() });
                        Ok(())
                    }
                    Err(_) => Ok(()),
                }
            } else if z3_output.starts_with("unsat") {
                eprintln!("unsat in: {}ms", now.elapsed().as_millis());
                Ok(())
            } else {
                // Z3 may spit out a lot of output, so we just return
                // the first line which will typically be an error
                // message in this case.
                Err(WebError::Z3Error(z3_output.lines().next().unwrap_or("No output").to_string()))
            }
        },
    );

    Ok(match run_result {
        Ok(run_info) => {
            let mut graphs: Vec<JsGraph> = Vec::new();
            while let Some(graph) = graph_queue.pop() {
                graphs.push(graph)
            }

            Response::Done {
                graphs,
                objdump: litmus.objdump,
                candidates: i32::try_from(run_info.candidates).expect("Candidates did not fit in i32"),
                shows: cat.shows(),
            }
        }
        Err(run_error) => Response::Error { message: format!("{}", run_error) },
    })
}
