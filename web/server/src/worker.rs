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
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

use isla_cat::cat;
use isla_lib::concrete::{B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::executor;
use isla_lib::executor::LocalFrame;
use isla_lib::footprint_analysis::footprint_analysis;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::serialize as ir_serialize;
use isla_lib::ir::*;
use isla_lib::litmus::Litmus;
use isla_lib::log;
use isla_lib::memory::Memory;
use isla_lib::smt::Event;

use getopts::Options;
mod request;
use request::Request;

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

fn main() {
    if let Err(_) = limit() {
        eprintln!("Failed to set resource limits");
        std::process::exit(1)
    }

    let code = isla_main();

    unsafe { isla_lib::smt::finalize_solver() };
    std::process::exit(code)
}

fn deserialize_from_stdin<T: DeserializeOwned>() -> Option<T> {
    let stdin = std::io::stdin();
    let handle = stdin.lock();
    bincode::deserialize_from(handle).ok()
}

static ARCH_WHITELIST: [&str; 1] = ["aarch64"];

fn isla_main() -> i32 {
    let args: Vec<String> = std::env::args().collect();
    let mut opts = Options::new();
    opts.reqopt("", "resources", "path to resource files", "<path>");
    opts.reqopt("", "cache", "path to a cache directory", "<path>");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Argument error: {}", e);
            return 1;
        }
    };

    // Log absolutely everything
    isla_lib::log::set_flags(0xffff_ffff);

    // The main server process sends the json from the AJAX request to
    // us via stdin.
    let req = match deserialize_from_stdin::<Request>() {
        Some(req) => req,
        None => return 1,
    };

    // Check that the request architecture is valid
    if !ARCH_WHITELIST.contains(&req.arch.as_str()) {
        eprintln!("Invalid architecture in request");
        return 1;
    }

    let resources = PathBuf::from(matches.opt_str("resources").unwrap());
    if !resources.is_dir() {
        eprintln!("Invalid resources directory");
        return 1;
    }

    let cache = PathBuf::from(matches.opt_str("cache").unwrap());
    if !cache.is_dir() {
        eprintln!("Invalid cache directory");
        return 1;
    }

    let now = Instant::now();

    let config_file = resources.join(format!("{}.toml", req.arch));
    let symtab_file = resources.join(format!("{}.symtab", req.arch));
    let ir_file = resources.join(format!("{}.irx", req.arch));

    let strings = match fs::read(&symtab_file) {
        Ok(bytes) => match bincode::deserialize::<Vec<String>>(&bytes) {
            Ok(strings) => strings,
            Err(e) => {
                eprintln!("Failed to parse symbol table: {}", e);
                return 1;
            }
        },
        Err(e) => {
            eprintln!("Failed to read symbol table: {}", e);
            return 1;
        }
    };
    let symtab = Symtab::from_raw_table(&strings);

    let mut ir: Vec<Def<u32, B64>> = match fs::read(&ir_file) {
        Ok(bytes) => match ir_serialize::deserialize(&bytes) {
            Some(ir) => ir,
            None => {
                eprintln!("Failed to parse IR");
                return 1;
            }
        },
        Err(e) => {
            eprintln!("Failed to read IR: {}", e);
            return 1;
        }
    };

    let isa_config: ISAConfig<B64> = match fs::read_to_string(&config_file) {
        Ok(contents) => match ISAConfig::parse(&contents, &symtab) {
            Ok(isa_config) => isa_config,
            Err(e) => {
                eprintln!("{}", e);
                return 1;
            }
        },
        Err(e) => {
            eprintln!("Failed to read configuration: {}", e);
            return 1;
        }
    };

    println!("Loaded architecture in: {}ms", now.elapsed().as_millis());

    let litmus = match Litmus::parse(&req.litmus, &symtab, &isa_config) {
        Ok(litmus) => litmus,
        Err(e) => {
            eprintln!("{}", e);
            return 1;
        }
    };
    litmus.log();

    let now = Instant::now();

    let parse_cat = match cat::ParseCat::from_string(&req.cat) {
        Ok(parse_cat) => parse_cat,
        Err(e) => {
            eprintln!("{}", e);
            return 1;
        }
    };

    let cat = match cat::resolve_includes(&[], parse_cat) {
        Ok(cat) => {
            let mut tcx = cat::initial_tcx(isa_config.fences.iter().map(String::clone));
            match cat::infer_cat(&mut tcx, cat) {
                Ok(cat) => cat,
                Err(e) => {
                    eprintln!("Type error in cat: {:?}", e);
                    return 1;
                }
            }
        }
        Err(e) => {
            eprintln!("{}", e);
            return 1;
        }
    };

    println!("Parsed user input in: {}us", now.elapsed().as_micros());

    let Initialized { regs, mut lets, shared_state } =
        initialize_architecture(&mut ir, symtab, &isa_config, AssertionMode::Optimistic);

    let mut memory = Memory::new();
    memory.add_concrete_region(isa_config.thread_base..isa_config.thread_top, HashMap::new());

    let mut current_base = isa_config.thread_base;
    for (thread, _, code) in litmus.assembled.iter() {
        log!(log::VERBOSE, &format!("Thread {} @ 0x{:x}", thread, current_base));
        for (i, byte) in code.iter().enumerate() {
            memory.write_byte(current_base + i as u64, *byte)
        }
        current_base += isa_config.thread_stride
    }
    memory.log();

    let function_id = shared_state.symtab.lookup("zmain");
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let tasks: Vec<_> = litmus
        .assembled
        .iter()
        .enumerate()
        .map(|(i, (_, inits, _))| {
            let address = isa_config.thread_base + (isa_config.thread_stride * i as u64);
            lets.insert(ELF_ENTRY, UVal::Init(Val::I128(address as i128)));
            let mut regs = regs.clone();
            for (reg, value) in inits {
                regs.insert(*reg, UVal::Init(Val::Bits(B64::from_u64(*value))));
            }
            LocalFrame::new(args, Some(&[Val::Unit]), instrs)
                .add_lets(&lets)
                .add_regs(&regs)
                .set_memory(memory.clone())
                .task(i)
        })
        .collect();

    let mut thread_buckets: Vec<Vec<Vec<Event<B64>>>> = vec![Vec::new(); tasks.len()];
    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(THREADS, tasks, &shared_state, queue.clone(), &executor::trace_collector);
    log!(log::VERBOSE, &format!("Symbolic execution took: {}ms", now.elapsed().as_millis()));

    let rk_ifetch = match shared_state.enum_member("Read_ifetch") {
        Some(rk) => rk,
        None => {
            eprintln!("No `Read_ifetch' read kind found in specified architecture!");
            return 1;
        }
    };

    loop {
        match queue.pop() {
            Ok(Ok((task_id, mut events))) => {
                let events: Vec<Event<B64>> = events
                    .drain(..)
                    .rev()
                    .filter(|ev| {
                        (ev.is_memory() && !ev.has_read_kind(rk_ifetch))
                            || ev.is_smt()
                            || ev.is_instr()
                            || ev.is_cycle()
                            || ev.is_write_reg()
                    })
                    .collect();
                let mut events = isla_lib::simplify::remove_unused(events.to_vec());
                for event in events.iter_mut() {
                    isla_lib::simplify::renumber_event(event, task_id as u32, thread_buckets.len() as u32)
                }

                thread_buckets[task_id].push(events)
            }
            // Error during execution
            Ok(Err(msg)) => {
                eprintln!("{}", msg);
                return 1;
            }
            // Empty queue
            Err(_) => break,
        }
    }

    let footprints =
        footprint_analysis(THREADS, &thread_buckets, &lets, &regs, &shared_state, &isa_config, cache).unwrap();

    println!("Hello, World: {:?}", req);
    0
}
