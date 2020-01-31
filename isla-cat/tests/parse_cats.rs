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

extern crate isla_cat;

use isla_cat::cat::{load_cat, ParseCat};

fn test_parse(arch: &str) {
    match ParseCat::from_file(format!("tests/{}.cat", arch)) {
        Ok(_) => (),
        Err(e) => panic!(e),
    }
}

#[test]
fn test_parse_aarch64() {
    test_parse("aarch64")
}

#[test]
fn test_parse_ppc() {
    test_parse("ppc")
}

#[test]
fn test_parse_riscv() {
    test_parse("riscv")
}

#[test]
fn test_parse_riscv_defs() {
    test_parse("riscv-defs")
}

#[test]
fn test_parse_x86tso() {
    test_parse("x86tso")
}

#[test]
fn test_load_cat() {
    match load_cat("tests/aarch64.cat") {
        Ok(_) => (),
        Err(e) => panic!(e),
    }
}
