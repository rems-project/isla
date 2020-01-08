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

use getopts::{Options, Matches};
use std::fs::File;
use std::io::prelude::*;
use std::process::exit;

use isla_lib::ast;
use isla_lib::ast::*;
use isla_lib::ast_lexer;
use isla_lib::ast_parser;
use isla_lib::config::ISAConfig;
use isla_lib::log;

fn tool_name() -> Option<String> {
    match std::env::current_exe() {
        Ok(path) => Some(path.components().last()?.as_os_str().to_str()?.to_string()),
        Err(_) => None,
    }
}

fn print_usage(opts: &Options, code: i32) -> ! {
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
    opts.optopt("t", "threads", "use this many worker threads", "N");
    opts.optopt("l", "litmus", "load this litmus file", "FILE");
    opts.optopt("a", "arch", "load architecture file", "FILE");
    opts.optopt("c", "config", "load config for architecture", "FILE");
    opts.optflag("h", "help", "print this help message");
    opts.optflagmulti("v", "verbose", "print verbose output");
    opts
}

fn parse_ir(contents: &str) -> Vec<ast::Def<String>> {
    let lexer = ast_lexer::Lexer::new(&contents);
    match ast_parser::AstParser::new().parse(lexer) {
        Ok(ir) => ir,
        Err(parse_error) => {
            eprintln!("Parse error: {}", parse_error);
            exit(1)
        }
    }
}

fn default_ir() -> Vec<ast::Def<String>> {
    parse_ir(include_str!("../default.ir"))
}

fn load_ir(file: &str) -> std::io::Result<Vec<ast::Def<String>>> {
    let mut file = File::open(file)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(parse_ir(&contents))
}

pub struct CommonOpts<'ir> {
    pub num_threads: usize,
    pub arch: Vec<Def<u32>>,
    pub symtab: Symtab<'ir>,
    pub isa_config: ISAConfig,
}

pub fn parse(opts: &Options) -> (Matches, Vec<Def<String>>) {
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

    log::set_verbosity(matches.opt_count("verbose"));

    let arch = {
        if let Some(file) = matches.opt_str("arch") {
            match load_ir(&file) {
                Ok(contents) => contents,
                Err(f) => {
                    eprintln!("Error when loading architecture: {}", f);
                    exit(1)
                }
            }
        } else {
            default_ir()
        }
    };

    (matches, arch)
}

pub fn parse_with_arch<'ir>(opts: &Options, matches: &Matches, arch: &'ir [Def<String>]) -> CommonOpts<'ir> {
    let num_threads = match matches.opt_get_default("threads", num_cpus::get()) {
        Ok(t) => t,
        Err(f) => {
            eprintln!("Could not parse --threads option: {}", f);
            print_usage(opts, 1)
        }
    };

    let mut symtab = Symtab::new();
    let arch = symtab.intern_defs(&arch);

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

    return CommonOpts {
        num_threads,
        arch,
        symtab,
        isa_config,
    }
}
