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
use std::collections::{HashMap, HashSet};

use crate::bitvector::BV;
use crate::ir::{RegisterField, Val};
use crate::smt::smtlib::{self, Def, Exp};
use crate::smt::{Event, Sym};

pub enum RegisterValue<B> {
    Symbolic(Exp<Sym>),
    // Concrete may be a little misleading here, as only the structure
    // of the value needs to be concrete, i.e. we could have a struct
    // with some symbolic fields.
    Concrete(Val<B>),
}

/// A struct representing the initial register state from a
/// trace. Note that this type is a bit more complex than simply a map
/// from registers to values, as we allow symbolic states. For
/// example, we might have a test that says something like register X1
/// contains an aligned address within a range, and X2 contains an
/// aligned address within the same range but in a different page.
pub struct RegisterState<B> {
    pub values: Vec<(RegisterField, RegisterValue<B>)>,
    pub decls: HashMap<Sym, smtlib::Ty>,
    // A Val in RegisterValue::Concrete may refer to SMTLIB definitions.
    pub defs: HashMap<Sym, Exp<Sym>>,
    pub asserts: Vec<Exp<Sym>>,
}

/// Compute the initial register state from a trace.
pub fn initial_register_state<B: BV, E: Borrow<Event<B>>>(events: &[E]) -> RegisterState<B> {
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
                let reg_field = (*reg, accessor.clone());
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

    // Now we find all the symbolic variables used the register values
    // so we can find any relevant assertions
    let mut symbolic_vars: HashSet<Sym, ahash::RandomState> = HashSet::default();
    for (_, value) in regs.iter() {
        match value {
            RegisterValue::Symbolic(exp) => exp.collect_variables(&mut symbolic_vars),
            RegisterValue::Concrete(value) => value.collect_symbolic_variables(&mut symbolic_vars),
        }
    }

    let mut used_defs: HashMap<Sym, Exp<Sym>> = HashMap::default();
    for (v, exp) in defs.iter() {
        if symbolic_vars.contains(v) {
            used_defs.insert(*v, (*exp).clone_expand(&defs));
        }
    }

    let mut asserts: Vec<Exp<Sym>> = Vec::new();
    {
        let mut found: HashSet<usize> = HashSet::default();
        let mut repeat = true;
        while repeat {
            repeat = false;
            for (n, event) in events.iter().enumerate() {
                match event.borrow() {
                    Smt(Def::Assert(exp), ..) if !found.contains(&n) => {
                        let assert_vars = exp.variables();
                        if symbolic_vars.intersection(&exp.variables()).next().is_some() {
                            asserts.push(exp.clone_expand(&defs));
                            found.insert(n);
                            repeat = true;
                            symbolic_vars.extend(assert_vars.difference(&symbolic_vars).copied().collect::<Vec<_>>())
                        }
                    }
                    Cycle => break,
                    _ => continue,
                }
            }
        }
    }

    let mut used_decls: HashMap<Sym, smtlib::Ty> = HashMap::new();
    for (v, ty) in decls.iter() {
        if symbolic_vars.contains(v) {
            used_decls.insert(*v, (*ty).clone());
        }
    }

    RegisterState { values: regs, decls: used_decls, defs: used_defs, asserts }
}
