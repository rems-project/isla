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

use getopts::Options;
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::process::exit;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use isla_lib::ast;
use isla_lib::ast::*;
use isla_lib::ast_lexer;
use isla_lib::ast_parser;
use isla_lib::config::ISAConfig;
use isla_lib::executor;
use isla_lib::executor::Frame;
use isla_lib::litmus::Litmus;
use isla_lib::log::*;
use isla_lib::smt::Checkpoint;
use isla_lib::type_check;
use isla_lib::zencode;

fn print_usage(opts: Options, code: i32) -> ! {
    let brief = "Usage: isla [options]";
    print!("{}", opts.usage(&brief));
    exit(code)
}

fn load_ir(file: &str) -> std::io::Result<Vec<ast::Def<String>>> {
    let mut file = File::open(file)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    let lexer = ast_lexer::Lexer::new(&contents);
    match ast_parser::AstParser::new().parse(lexer) {
        Ok(ir) => Ok(ir),
        Err(parse_error) => {
            println!("Parse error: {}", parse_error);
            exit(1)
        }
    }
}

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn isla_main() -> i32 {
    let args: Vec<String> = env::args().collect();
    let mut opts = Options::new();
    opts.optopt("t", "threads", "use this many worker threads", "N");
    opts.optopt("l", "litmus", "load this litmus file", "FILE");
    opts.optflag("", "optimistic", "assume assertions succeed");
    opts.reqopt("a", "arch", "load architecture file", "FILE");
    opts.optopt("c", "config", "load config for architecture", "FILE");
    opts.reqopt("p", "property", "check property in architecture", "ID");
    opts.optflag("h", "help", "print this help message");
    opts.optflagmulti("v", "verbose", "print verbose output");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            println!("{}", f);
            print_usage(opts, 1)
        }
    };

    if matches.opt_present("help") {
        print_usage(opts, 0)
    }

    set_verbosity(matches.opt_count("verbose"));

    let assertion_mode =
        if matches.opt_present("optimistic") { AssertionMode::Optimistic } else { AssertionMode::Pessimistic };

    let now = Instant::now();
    let arch = {
        let file = matches.opt_str("arch").unwrap();
        match load_ir(&file) {
            Ok(contents) => contents,
            Err(f) => {
                println!("Error when loading architecture: {}", f);
                return 1;
            }
        }
    };
    let mut symtab = Symtab::new();
    log(0, &format!("Interning... ({}ms)", now.elapsed().as_millis()));
    let mut arch = symtab.intern_defs(&arch);
    log(0, "Inserting primops...");
    insert_primops(&mut arch, assertion_mode);
    log(0, "Checking arch...");
    type_check::check(&mut arch);

    let isa_config = if let Some(file) = matches.opt_str("config") {
        match ISAConfig::from_file(file, &symtab) {
            Ok(isa_config) => isa_config,
            Err(e) => {
                eprintln!("{}", e);
                exit(1)
            }
        }
    } else {
        ISAConfig::new(&symtab)
    };

    let litmus = match Litmus::from_file(&matches.opt_str("litmus").expect("No litmus"), &isa_config) {
        Ok(litmus) => litmus,
        Err(e) => {
            eprintln!("{}", e);
            exit(1)
        }
    };

    let register_state = Mutex::new(initial_register_state(&arch));
    let shared_state = Arc::new(SharedState::new(symtab, &arch));

    log(0, &format!("Loaded arch in {}ms", now.elapsed().as_millis()));

    let property = zencode::encode(&matches.opt_str("property").unwrap());

    let num_threads = match matches.opt_get_default("threads", num_cpus::get()) {
        Ok(t) => t,
        Err(f) => {
            println!("Could not parse --threads option: {}", f);
            print_usage(opts, 1)
        }
    };

    for def in arch.iter() {
        if let Def::Let(bindings, setup) = def {
            let vars: Vec<_> = bindings.iter().map(|(id, ty)| (*id, ty)).collect();
            let task = {
                let regs = register_state.lock().unwrap();
                (Frame::new(&vars, regs.clone(), setup), Checkpoint::new(), None)
            };

            executor::start_single(
                task,
                &shared_state,
                &register_state,
                &move |_tid, result, shared_state, _solver, register_state| match result {
                    Ok((_, frame)) => {
                        for (id, _) in bindings.iter() {
                            let symbol = zencode::decode(shared_state.symtab.to_str(*id));
                            match frame.vars.get(id) {
                                Some(value) => {
                                    let mut state = register_state.lock().unwrap();
                                    state.insert(*id, value.clone());
                                    let symbol = zencode::decode(shared_state.symtab.to_str(*id));
                                    log_from(0, 0, &format!("{} = {:?}", symbol, value));
                                }
                                None => log_from(0, 0, &format!("No value for symbol {}", symbol)),
                            }
                        }
                    }
                    Err(err) => log_from(0, 0, &format!("Failed to evaluate letbinding: {:?}", err)),
                },
            );
        }
    }

    log(0, &format!("Initialized letbindings in {}ms", now.elapsed().as_millis()));

    let function_id = shared_state.symtab.lookup(&property);
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task = {
        let regs = register_state.lock().unwrap();
        (Frame::new(args, regs.clone(), instrs), Checkpoint::new(), None)
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
