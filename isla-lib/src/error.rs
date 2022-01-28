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

use std::error::Error;
use std::fmt;

use crate::ir::source_loc::SourceLoc;

#[derive(Debug)]
pub enum ExecError {
    Type(String, SourceLoc),
    VariableNotFound(String),
    Unimplemented,
    AssertionFailed(String),
    Overflow,
    /// SMTLIB only supports fixed-length bitvectors. This error is
    /// raised if a bitvector width would become symbolic.
    SymbolicLength(&'static str, SourceLoc),
    /// Returned when there is no symbolic representation for a
    /// specific type. Certain types like strings are always assumed
    /// to be concrete.
    NoSymbolicType,
    /// Used for cases that should be unreachable (i.e. are definite
    /// errors).
    Unreachable(String),
    /// Used when we try to access memory that does not have any
    /// defined semantics.
    Unmapped,
    BadRead(&'static str),
    BadWrite(&'static str),
    NoElfEntry,
    OutOfBounds(&'static str),
    MatchFailure,
    Timeout,
    Dead,
    Exit,
    NoModel,
    Z3Error(String),
    Z3Unknown,
    /// Execution stopped because this function is in the stop_functions set
    Stopped(String),
}

impl fmt::Display for ExecError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Error for ExecError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}
