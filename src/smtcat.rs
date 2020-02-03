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

use std::env;
use std::process::exit;

use isla_cat::cat::{infer_cat, initial_tcx, load_cat};

fn main() {
    let mut args: Vec<String> = env::args().collect();
    args.remove(0);

    for arg in args {
        let cat = match load_cat(&arg) {
            Ok(cat) => cat,
            Err(e) => {
                eprintln!("Could not load cat '{}': {}", arg, e);
                exit(1)
            }
        };

        let mut fences: Vec<String> = vec![
            "DMB.ISH",
            "DMB.ISHLD",
            "DMB.ISHST",
            "DSB.ISH",
            "DSB.ISHLD",
            "DSB.ISHST",
            "DMB.SY",
            "DMB.ST",
            "DMB.LD",
            "DSB.SY",
            "DSB.ST",
            "DSB.LD",
            "DMB.OSH",
            "DSB.OSH",
            "DMB.OSHLD",
            "DSB.OSHLD",
            "DMB.OSHST",
            "DSB.OSHST",
            "ISB",
            "A",
            "L",
            "Q",
            "NoRet",
        ]
        .drain(..)
        .map(|f| f.to_string())
        .collect();
        let mut tcx = initial_tcx(fences.drain(..));

        match infer_cat(&mut tcx, cat) {
            Ok(cat) => {
                println!("{:?}", cat);
                exit(0)
            }
            Err(e) => {
                eprintln!("Type error in cat '{}': {:?}", arg, e);
                exit(1)
            }
        }
    }
}
