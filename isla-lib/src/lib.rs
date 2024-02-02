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

#![allow(clippy::implicit_hasher)]

#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate lazy_static;

#[macro_use]
pub mod log;

lalrpop_mod!(#[allow(clippy::all)] pub ir_parser);
lalrpop_mod!(#[allow(clippy::all)] pub value_parser);
lalrpop_mod!(#[allow(clippy::all)] pub smt_parser);

pub mod bitvector;
pub mod cache;
pub mod config;
pub mod error;
pub mod executor;
pub mod fraction;
pub mod init;
pub mod ir;
pub mod ir_lexer;
pub mod lexer;
pub mod memory;
pub mod primop;
pub mod primop_util;
mod probe;
pub mod register;
pub mod simplify;
pub mod smt;
pub mod source_loc;
pub mod trace;
pub mod zencode;

pub const ISLA_VERSION: &str = env!("ISLA_VERSION");
