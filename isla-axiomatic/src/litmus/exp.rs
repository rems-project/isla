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

use isla_lib::ir::{Name, Val, Reset};
use isla_lib::error::ExecError;
use isla_lib::concrete::BV;
use isla_lib::smt::Solver;

use std::fmt;
use std::sync::Arc;

pub enum ExpParseError {
    Lex { pos: usize },
    Int { error: std::num::ParseIntError },
    NoRegister { name: String },
    NoAddress { name: String },
}

impl fmt::Display for ExpParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ExpParseError::*;
        match self {
            Lex { pos } => write!(f, "Lexical error at position: {}", pos),
            Int { error } => write!(f, "{}", error),
            NoRegister { name } => write!(f, "No register {} in architecture", name),
            NoAddress { name } => write!(f, "No address {} in litmus file", name),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Loc {
    Register { reg: Name, thread_id: usize },
    LastWriteTo { address: u64, bytes: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exp {
    EqLoc(Loc, Box<Exp>),
    True,
    False,
    Id(String),
    Bin(String),
    Hex(String),
    Nat(u64),
    And(Vec<Exp>),
    Or(Vec<Exp>),
    Not(Box<Exp>),
    App(String, Vec<Exp>),
    Implies(Box<Exp>, Box<Exp>),
}

pub fn eval<B: BV>(exp: &Exp, _solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    match exp {
        Exp::EqLoc(_, _) => Err(ExecError::Unimplemented),
        Exp::True => Ok(Val::Bool(true)),
        Exp::False => Ok(Val::Bool(false)),
        _ => Err(ExecError::Unimplemented),
    }
}

pub fn reset_eval<B: BV>(exp: &Exp) -> Reset<B> {
    let exp = exp.clone();
    Arc::new(move |solver| {
        eval(&exp, solver)
    })
}

/*
pub enum Ty {
    BitVec(u32),
    Bool,
}

pub enum TyError {
    TyError
}

fn infer(exp: &Exp) -> Result<Ty, TyError> {
    use Exp::*;
    match exp {
        EqLoc(loc, exp) => {
            let ty = infer_loc(loc)?;
            let _: () = check(exp, &ty)?;
            Ok(Ty::Bool)
        },
        True | False => Ok(Ty::Bool),
        _ => Ok(Ty::Bool),
    }
}

fn check(exp: &Exp, ty: &Ty) -> Result<(), TyError> {
    Ok(())
}

fn infer_loc(loc: &Loc) -> Result<Ty, TyError> {
    Ok(Ty::Bool)
}
*/
