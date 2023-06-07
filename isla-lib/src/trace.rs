// BSD 2-Clause License
//
// Copyright (c) 2019-2023 Alasdair Armstrong
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

//! This module contains various utility functions for operating on event traces.

use std::borrow::Borrow;
use std::collections::HashMap;

use crate::bitvector::BV;
use crate::ir::{RegisterField, Val};
use crate::smt::smtlib::{self, Def, Exp};
use crate::smt::{Event, Sym};

pub enum RegisterValue<B> {
    Symbolic(Exp<Sym>),
    Concrete(Val<B>),
}

/// Compute the initial register state from a trace.
pub fn initial_register_state<B: BV, E: Borrow<Event<B>>>(events: &[E]) -> Vec<(RegisterField, RegisterValue<B>)> {
    use Event::*;

    let mut decls: HashMap<Sym, &smtlib::Ty> = HashMap::default();
    let mut defs: HashMap<Sym, &Exp<Sym>> = HashMap::default();
    let mut regs = Vec::new();

    for event in events.iter() {
        match event.borrow() {
            Smt(Def::DeclareConst(v, ty), ..) => {
                decls.insert(*v, ty);
            }
            Smt(Def::DefineConst(v, exp), ..) => {
                defs.insert(*v, exp);
            }

            AssumeReg(reg, accessor, value) | WriteReg(reg, accessor, value) => {
                let reg_field = (reg.clone(), accessor.clone());
                match value {
                    Val::Symbolic(v) => {
                        regs.push((reg_field, RegisterValue::Symbolic(Exp::Var(*v).clone_expand(&defs))))
                    }
                    _ => regs.push((reg_field, RegisterValue::Concrete(value.clone()))),
                }
            }

            // The register inititalization occurs in cycle 0, so once we find cycle 1, stop.
            Cycle => break,
            _ => continue,
        }
    }

    regs
}
