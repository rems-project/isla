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

use getopts::{Matches, Options};
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::prelude::*;
use std::process::exit;

use isla_lib::concrete::BV;
use isla_lib::config::ISAConfig;
use isla_lib::ir;
use isla_lib::ir::*;
use isla_lib::ir::linearize::linearize;
use isla_lib::ir_parser;
use isla_lib::lexer;
use isla_lib::log;
use isla_lib::value_parser;
use isla_lib::zencode;

fn tool_name() -> Option<String> {
    match std::env::current_exe() {
        Ok(path) => Some(path.components().last()?.as_os_str().to_str()?.to_string()),
        Err(_) => None,
    }
}

pub fn print_usage(opts: &Options, code: i32) -> ! {
    let tool = match tool_name() {
        Some(name) => name,
        None => "[tool]".to_string(),
    };
    let brief = format!("Usage: {} [options]", tool);
    eprint!("{}", opts.usage(&brief));
    exit(code)
}

pub fn common_opts() -> Options {
    let mut opts = Options::new();
    opts.optopt("t", "threads", "use this many worker threads", "<n>");
    opts.reqopt("a", "arch", "load architecture file", "<file>");
    opts.optopt("c", "config", "load custom config for architecture", "<file>");
    opts.optmulti("r", "register", "set a register", "<register>=<value>");
    opts.optflag("h", "help", "print this help message");
    opts.optflag("v", "verbose", "print verbose output");
    opts.optopt("d", "debug", "set debugging flags", "<flags>");
    opts.optopt("L", "linearize", "rewrite function into linear form", "<id>");
    opts.optmulti("", "probe", "trace specified function calls or location assignments", "<id>");
    opts
}

fn parse_ir<B>(contents: &str) -> Vec<ir::Def<String, B>> {
    let lexer = lexer::Lexer::new(&contents);
    match ir_parser::IrParser::new().parse(lexer) {
        Ok(ir) => ir,
        Err(parse_error) => {
            eprintln!("Parse error: {}", parse_error);
            exit(1)
        }
    }
}

fn load_ir<B>(hasher: &mut Sha256, file: &str) -> std::io::Result<Vec<ir::Def<String, B>>> {
    let mut file = File::open(file)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    hasher.input(&contents);
    Ok(parse_ir(&contents))
}

pub struct CommonOpts<'ir, B> {
    pub num_threads: usize,
    pub arch: Vec<Def<Name, B>>,
    pub symtab: Symtab<'ir>,
    pub isa_config: ISAConfig<B>,
}

pub fn parse<B>(hasher: &mut Sha256, opts: &Options) -> (Matches, Vec<Def<String, B>>) {
    let args: Vec<String> = std::env::args().collect();

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

    let debug_opts = matches.opt_str("debug").unwrap_or_else(|| "".to_string());
    let logging_flags = (if matches.opt_present("verbose") { log::VERBOSE } else { 0u32 })
        | (if debug_opts.contains('f') { log::FORK } else { 0u32 })
        | (if debug_opts.contains('m') { log::MEMORY } else { 0u32 })
        | (if debug_opts.contains('l') { log::LITMUS } else { 0u32 })
        | (if debug_opts.contains('p') { log::PROBE } else { 0u32 });
    log::set_flags(logging_flags);

    let arch = {
        let file = matches.opt_str("arch").unwrap();
        match load_ir(hasher, &file) {
            Ok(contents) => contents,
            Err(f) => {
                eprintln!("Error when loading architecture: {}", f);
                exit(1)
            }
        }
    };

    (matches, arch)
}

pub fn parse_with_arch<'ir, B: BV>(
    hasher: &mut Sha256,
    opts: &Options,
    matches: &Matches,
    arch: &'ir [Def<String, B>],
) -> CommonOpts<'ir, B> {
    let num_threads = match matches.opt_get_default("threads", num_cpus::get()) {
        Ok(t) => t,
        Err(f) => {
            eprintln!("Could not parse --threads option: {}", f);
            print_usage(opts, 1)
        }
    };

    let mut symtab = Symtab::new();
    let mut arch = symtab.intern_defs(&arch);

    let mut isa_config = if let Some(file) = matches.opt_str("config") {
        match ISAConfig::from_file(hasher, file, &symtab) {
            Ok(isa_config) => isa_config,
            Err(e) => {
                eprintln!("{}", e);
                exit(1)
            }
        }
    } else {
        match ISAConfig::new(&symtab) {
            Ok(isa_config) => isa_config,
            Err(e) => {
                eprintln!("{}", e);
                exit(1)
            }
        }
    };

    matches.opt_strs("probe").iter().for_each(|arg| {
        if let Some(id) = symtab.get(&zencode::encode(&arg)) {
            isa_config.probes.insert(id);
        } else {
            // Also allow raw names, such as throw_location
            if let Some(id) = symtab.get(&arg) {
                isa_config.probes.insert(id);
            } else {
                eprintln!("Function {} does not exist in the specified architecture", arg);
                exit(1)
            }
        }
    });

    matches.opt_strs("register").iter().for_each(|arg| {
        let lexer = lexer::Lexer::new(&arg);
        match value_parser::AssignParser::new().parse(lexer) {
            Ok((reg, value)) => {
                if let Some(reg) = symtab.get(&zencode::encode(&reg)) {
                    isa_config.default_registers.insert(reg, value);
                } else {
                    eprintln!("Register {} does not exist in the specified architecture", reg);
                    exit(1)
                }
            }
            Err(_) => {
                eprintln!("Could not parse register assignment: {}", arg);
                exit(1)
            }
        }
    });

    matches.opt_strs("linearize").iter().for_each(|id| {
        let linear = symtab.lookup(&zencode::encode(&id));
    
        for def in arch.iter_mut() {
            if let Def::Fn(f, _, body) = def {
                if *f == linear {
                    *body = linearize(body.to_vec(), &Ty::Bool, &mut symtab)
                }
            }
        }
    });

    CommonOpts { num_threads, arch, symtab, isa_config }
}
