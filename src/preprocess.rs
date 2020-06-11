// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
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
