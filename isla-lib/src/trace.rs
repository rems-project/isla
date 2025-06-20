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

use crate::bitvector::{b129::B129, BV};
use crate::error::ExecError;
use crate::ir::{RegisterField, Val};
use crate::primop;
use crate::smt::smtlib::{self, Def, Exp, Ty};
use crate::smt::{Config, Context, Event, Model, ModelVal, Solver, Sym};
use crate::source_loc::SourceLoc;

/// A struct representing the initial register state from a
/// trace. Note that this type is a bit more complex than simply a map
/// from registers to values, as we allow symbolic states. For
/// example, we might have a test that says something like register X1
/// contains an aligned address within a range, and X2 contains an
/// aligned address within the same range but in a different page.
pub struct RegisterState<B> {
    pub values: Vec<(RegisterField, Val<B>)>,
    pub decls: HashMap<Sym, smtlib::Ty>,
    // A Val in RegisterValue::Concrete may refer to SMTLIB definitions.
    pub defs: Vec<(Sym, Exp<Sym>)>,
    pub asserts: Vec<Exp<Sym>>,
}

impl<B: BV> RegisterState<B> {
    /// Compute the initial register state from a trace.
    pub fn from_events<E: Borrow<Event<B>>>(events: &[E]) -> Self {
        use Event::*;

        let mut decls: HashMap<Sym, smtlib::Ty> = HashMap::default();
        let mut defs: Vec<(Sym, Exp<Sym>)> = Vec::new();
        let mut regs = Vec::new();
        let mut asserts: Vec<Exp<Sym>> = Vec::new();

        for event in events.iter() {
            match event.borrow() {
                Smt(Def::DeclareConst(v, ty), ..) => {
                    decls.insert(*v, ty.clone());
                }

                Smt(Def::DefineConst(v, exp), ..) => {
                    defs.push((*v, exp.clone()));
                }

                Smt(Def::Assert(exp), ..) => asserts.push(exp.clone()),

                AssumeReg(reg, accessor, value) | WriteReg(reg, accessor, value) => {
                    let reg_field = (*reg, accessor.clone());
                    regs.push((reg_field, value.clone()))
                }

                // The register inititalization occurs in cycle 0, so once we find cycle 1, stop.
                Cycle => break,

                _ => continue,
            }
        }

        RegisterState { values: regs, decls, defs, asserts }
    }

    pub fn model(&self) -> Result<HashMap<Sym, Exp<Sym>>, ExecError> {
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);

        let mut solver: Solver<B129> = Solver::new(&ctx);
        for (v, ty) in self.decls.iter() {
            solver.add(Def::DeclareConst(*v, ty.clone()))
        }
        for (v, exp) in self.defs.iter() {
            solver.add(Def::DefineConst(*v, exp.clone()))
        }
        for exp in self.asserts.iter() {
            solver.add(Def::Assert(exp.clone()));
        }

        solver.check_sat(SourceLoc::unknown());
        let mut model = Model::new(&solver);

        let mut vars = HashSet::default();
        for (_, value) in self.values.iter() {
            value.collect_symbolic_variables(&mut vars)
        }

        let mut interpreted = HashMap::new();

        for v in vars.drain() {
            match model.get_var(v)? {
                ModelVal::Arbitrary(ty) => {
                    match ty {
                        Ty::Bool => interpreted.insert(v, Exp::Bool(false)),
                        Ty::BitVec(n) => interpreted.insert(v, primop::smt_zeros(n as i128)),
                        _ => panic!("Invalid type found in register state model"),
                    };
                }
                ModelVal::Exp(exp) => {
                    assert!(exp.variables().is_empty());
                    interpreted.insert(v, exp);
                }
            }
        }

        Ok(interpreted)
    }
}
