// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
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

//! This module defines all the Sail primitives for working with
//! floating point numbers.  Internally Isla uses the same
//! representation for floating points that Z3/SMTLIB uses, which
//! allows floating point numbers with arbitrary exponent and
//! significand widths. However, in Sail we want to ensure we can use
//! SoftFloat for emulation, so we restrict the primitives here to 16,
//! 32, 64, and 128-bit variants, prefixed either `fp16`, `fp32`,
//! `fp64`, and `fp128` respectively, as these are supported by
//! SoftFloat. Functions just prefixed with `fp_` work with any input
//! width.
//!
//! Using floating point types requires that the Solver is
//! instantiated with the `ALL` theory rather than just
//! bitvectors+datatypes as per usual.

use std::collections::HashMap;

use crate::bitvector::BV;
use crate::error::ExecError;
use crate::executor::LocalFrame;
use crate::ir::Val;
use crate::smt::*;
use crate::source_loc::SourceLoc;

use super::Variadic;

fn read_mem<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[2].clone(), args[3].clone(), solver, false, ReadOpts::default())
}

fn read_mem_ifetch<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[2].clone(), args[3].clone(), solver, false, ReadOpts::ifetch())
}

fn read_mem_exclusive<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[2].clone(), args[3].clone(), solver, false, ReadOpts::exclusive())
}

pub fn variadic_primops<B: BV>() -> HashMap<String, Variadic<B>> {
    let mut primops = HashMap::new();
    primops.insert("read_mem".to_string(), read_mem as Variadic<B>);
    primops.insert("read_mem_ifetch".to_string(), read_mem_ifetch as Variadic<B>);
    primops.insert("read_mem_exclusive".to_string(), read_mem_exclusive as Variadic<B>);
    primops
}