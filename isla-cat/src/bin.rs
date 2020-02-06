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

//! This crate implements a library for compiling cat files as used by
//! herdtools7 into SMTLIB defintions that can be used by an SMT
//! solver such as z3.
//!
//! There are some restrictions on the cat files we can support -
//! roughly speaking, we support the subset of cat that defines
//! relations and sets over events which is easily translated into
//! first-order SMT definitions.

#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate lazy_static;

lalrpop_mod!(
    #[allow(clippy::all)]
    cat_parser
);

mod cat;
mod cat_lexer;
mod smt;

use std::env;
use std::io;
use std::process::exit;

static USAGE: &str = "\n\nusage: cat2smt <model.cat> <fences>,\n\n  e.g. cat2smt aarch64.cat DMB.ISH ISB";

fn main() {
    let mut args = env::args().skip(1);
    let cat_file = match args.next() {
        Some(file) => file,
        None => {
            eprintln!("No .cat file provided!{}", USAGE);
            exit(1)
        }
    };

    let cat = match cat::load_cat(&cat_file) {
        Ok(cat) => cat,
        Err(e) => {
            eprintln!("Error when loading cat: {}{}", e, USAGE);
            exit(1)
        }
    };

    let mut tcx = cat::initial_tcx(args);
    let cat = match cat::infer_cat(&mut tcx, cat) {
        Ok(cat) => cat,
        Err(e) => {
            eprintln!("Type error in cat: {}{}", e, USAGE);
            exit(1);
        }
    };

    let result = {
        let stdout = io::stdout();
        let mut handle = stdout.lock();
        smt::compile_cat(&mut handle, &cat)
    };
    match result {
        Ok(()) => (),
        Err(e) => {
            eprintln!("Failed to compile cat: {:?}", e);
            exit(1);
        }
    }
}
