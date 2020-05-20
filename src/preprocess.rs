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
use std::error::Error;
use std::fs::File;
use std::io::Write;

use isla_lib::concrete::{bitvector64::B64, BV};
use isla_lib::ir;
use isla_lib::ir::{Def, Name, Symtab};

mod opts;
use opts::CommonOpts;

fn write_output<B: BV>(output: &str, arch: Vec<Def<Name, B>>, symtab: &Symtab) -> Result<(), Box<dyn Error>> {
    let mut arch_file = File::create(format!("{}.irx", output))?;
    arch_file.write_all(&ir::serialize::serialize(arch).expect("Failed to serialize architecture"))?;

    let mut symtab_file = File::create(format!("{}.symtab", output))?;
    symtab_file.write_all(&bincode::serialize(&symtab.to_raw_table())?)?;

    Ok(())
}

fn main() {
    let mut opts = opts::common_opts();
    opts.reqopt("o", "output", "output name for processed architecture and symbol table info", "<file>");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse::<B64>(&mut hasher, &opts);
    let CommonOpts { arch, symtab, .. } = opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let output = matches.opt_str("output").unwrap();

    if let Err(e) = write_output(&output, arch, &symtab) {
        eprintln!("Error: {}", e);
        std::process::exit(1)
    }
}
