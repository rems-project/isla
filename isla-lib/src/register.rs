// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
// Copyright (c) 2020 Dhruv Makwana
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

//! This model implements a map type [RegisterBindings], from register
//! names to their values. For sequentially consistent registers like
//! GPRs (X1, X2, etc. in Arm), this is equivalent to a simple
//! key-value map from register names to their values. System
//! registers on the other hand, may require a slightly more relaxed
//! semantics depending on the model.
//!
//! For these registers, we keep track of three things:
//!
//! 1. The last written value
//! 2. The last read value
//! 3. The set of all written values
//!
//! Additionally, all registers may be in an unitialised state.
//!
//! The semantics is as follows:
//!
//! * When we _read_ from a register, return the last read value if
//!   one exists. Otherwise return a symbolic value representing
//!   non-deterministic choice between all previously written values,
//!   and set the last read value to be this value.  If the register
//!   is uninitialised when we read it, we initialise it to an
//!   symbolic unknown value of the correct type, setting both the
//!   last read value and the last written value to that unknown
//!   value.
//!
//! * When we _write_ to a register we simply store the value as the
//!   last written value. We also set the last read value to the last
//!   written value: this is so registers appear to behave as regular
//!   variables within a single instruction, i.e.
//!   ```sail
//!   R = 0x0;
//!   print_bits("R = ", R);
//!   R = 0x1;
//!   print_bits("R = ", R);
//!   ```
//!   will print `R = 0x0` then `R = 0x1`, rather than `R = 0x0` twice.
//!
//! There are two additional operations. We can _forget_ the last
//! read, which allows another previously written value to be read by
//! subsequent reads. We can also _synchronize_ the register which
//! removes all the previously written values except the last, and
//! clears the last read value, forcing subsequent reads to see the
//! last written value.

use ahash;
use std::collections::{hash_map, HashMap, HashSet};

use crate::bitvector::BV;
use crate::error::ExecError;
use crate::ir::*;
use crate::primop_util::{ite_choice, symbolic};
use crate::smt::{Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;

#[derive(Clone)]
enum RelaxedVal<'ir, B> {
    Uninit(&'ir Ty<Name>),
    Init { last_write: Val<B>, last_read: Option<Val<B>>, old_writes: Vec<Val<B>> },
}

#[derive(Clone)]
pub struct Register<'ir, B> {
    relaxed: bool,
    value: RelaxedVal<'ir, B>,
}

impl<'ir, B: BV> RelaxedVal<'ir, B> {
    fn unwrap_last_write(&self) -> &Val<B> {
        if let RelaxedVal::Init { last_write, .. } = self {
            last_write
        } else {
            panic!("unwrap called on uninitialized relaxed value!")
        }
    }

    // Returns the value, which could be any value written,
    // initializing it if needed. Guarantees that repeated calls to
    // value in between calls to synchronize or forget_last_read will
    // return the same value.
    fn read<'a>(
        &'a mut self,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<&'a Val<B>, ExecError> {
        match self {
            RelaxedVal::Uninit(ty) => {
                let sym = symbolic(ty, shared_state, solver, info)?;
                *self = RelaxedVal::Init { last_write: sym.clone(), last_read: Some(sym), old_writes: Vec::new() };
                Ok(self.unwrap_last_write())
            }
            RelaxedVal::Init { last_read: Some(v), .. } => Ok(v),
            RelaxedVal::Init { last_read, last_write, old_writes } => {
                let value = ite_choice(last_write, old_writes, solver, info)?;
                *last_read = Some(value);
                Ok(last_read.as_ref().unwrap())
            }
        }
    }

    // Read the last written value
    fn read_last<'a>(
        &'a mut self,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<&'a Val<B>, ExecError> {
        match self {
            RelaxedVal::Uninit(ty) => {
                let sym = symbolic(ty, shared_state, solver, info)?;
                *self = RelaxedVal::Init { last_write: sym, last_read: None, old_writes: Vec::new() };
                Ok(self.unwrap_last_write())
            }
            RelaxedVal::Init { last_write, .. } => Ok(last_write),
        }
    }

    // When synchronization is performed on a relaxed value (e.g. by
    // an ISB in ARM), the last written value becomes the only value.
    fn synchronize(&mut self) {
        match self {
            RelaxedVal::Uninit(_) => (),
            RelaxedVal::Init { last_read, last_write: _, old_writes } => {
                *old_writes = Vec::new();
                *last_read = None
            }
        }
    }

    // Forget the last value read to the value, allowing read to
    // return any written value once again.
    fn forget_last_read(&mut self) {
        match self {
            RelaxedVal::Uninit(_) => (),
            RelaxedVal::Init { last_read, .. } => *last_read = None,
        }
    }

    fn write(&mut self, value: Val<B>) {
        match self {
            RelaxedVal::Uninit(_) => {
                *self = RelaxedVal::Init { last_write: value.clone(), last_read: Some(value), old_writes: Vec::new() };
            }
            RelaxedVal::Init { last_write, last_read, old_writes } => {
                old_writes.push(last_write.clone());
                *last_read = Some(value.clone());
                *last_write = value
            }
        }
    }

    fn write_last(&mut self, value: Val<B>) {
        match self {
            RelaxedVal::Uninit(_) => {
                *self = RelaxedVal::Init { last_write: value, last_read: None, old_writes: Vec::new() };
            }
            RelaxedVal::Init { last_write, .. } => *last_write = value,
        }
    }
}

impl<'ir, B: BV> Register<'ir, B> {
    pub fn read<'a>(
        &'a mut self,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<&'a Val<B>, ExecError> {
        if self.relaxed {
            self.value.read(shared_state, solver, info)
        } else {
            self.value.read_last(shared_state, solver, info)
        }
    }

    pub fn collect_symbolic_variables(&self, vars: &mut HashSet<Sym, ahash::RandomState>) {
        if let RelaxedVal::Init { last_write, last_read, old_writes } = &self.value {
            last_write.collect_symbolic_variables(vars);
            if let Some(last_read) = last_read {
                last_read.collect_symbolic_variables(vars)
            }
            for write in old_writes {
                write.collect_symbolic_variables(vars)
            }
        }
    }

    /// Read the last written value to the register if it is
    /// initialized. Returns None if the register is uninitialized.
    pub fn read_last_if_initialized(&self) -> Option<&Val<B>> {
        match &self.value {
            RelaxedVal::Init { last_write, .. } => Some(last_write),
            RelaxedVal::Uninit(_) => None,
        }
    }

    pub fn write(&mut self, value: Val<B>) {
        if self.relaxed {
            self.value.write(value)
        } else {
            self.value.write_last(value)
        }
    }

    pub fn synchronize(&mut self) {
        if self.relaxed {
            self.value.synchronize()
        }
    }

    pub fn forget_last_read(&mut self) {
        if self.relaxed {
            self.value.forget_last_read()
        }
    }
}

#[derive(Clone)]
pub struct RegisterBindings<'ir, B> {
    map: HashMap<Name, Register<'ir, B>, ahash::RandomState>,
}

/// An iterator over registers in a [RegisterBindings]
pub struct Iter<'a, 'ir, B> {
    iterator: hash_map::Iter<'a, Name, Register<'ir, B>>,
}

impl<'ir, B: BV> RegisterBindings<'ir, B> {
    pub fn new() -> Self {
        RegisterBindings { map: HashMap::default() }
    }

    pub fn insert(&mut self, id: Name, relaxed: bool, v: UVal<'ir, B>) {
        match v {
            UVal::Uninit(ty) => {
                self.map.insert(id, Register { relaxed, value: RelaxedVal::Uninit(ty) });
            }
            UVal::Init(value) => {
                self.map.insert(
                    id,
                    Register {
                        relaxed,
                        value: RelaxedVal::Init { last_write: value, last_read: None, old_writes: Vec::new() },
                    },
                );
            }
        }
    }

    pub fn insert_register(&mut self, id: Name, v: Register<'ir, B>) {
        self.map.insert(id, v);
    }

    pub fn get<'a>(
        &'a mut self,
        id: Name,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<Option<&'a Val<B>>, ExecError> {
        if let Some(reg) = self.map.get_mut(&id) {
            let val = reg.read(shared_state, solver, info)?;
            Ok(Some(val))
        } else {
            Ok(None)
        }
    }

    // A non-modifying way to inspect a register
    pub fn get_last_if_initialized(&self, id: Name) -> Option<&Val<B>> {
        if let Some(reg) = self.map.get(&id) {
            if let Some(val) = reg.read_last_if_initialized() {
                Some(val)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn forget_last_reads(&mut self) {
        for reg in self.map.values_mut() {
            reg.forget_last_read()
        }
    }

    pub fn synchronize(&mut self) {
        for reg in self.map.values_mut() {
            reg.synchronize()
        }
    }

    pub fn synchronize_register(&mut self, id: Name) {
        if let Some(reg) = self.map.get_mut(&id) {
            reg.synchronize()
        }
    }

    pub fn contains_key(&self, id: Name) -> bool {
        self.map.contains_key(&id)
    }

    pub fn assign(&mut self, id: Name, v: Val<B>, shared_state: &SharedState<'ir, B>) {
        if let Some(reg) = self.map.get_mut(&id) {
            reg.write(v)
        } else {
            let symbol = zencode::decode(shared_state.symtab.to_str(id));
            panic!("No relaxed value {} ({:?})", symbol, id)
        }
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, 'ir, B> {
        Iter { iterator: self.map.iter() }
    }
}

impl<'ir, B: BV> Default for RegisterBindings<'ir, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, 'ir, B: BV> Iterator for Iter<'a, 'ir, B> {
    type Item = (&'a Name, &'a Register<'ir, B>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}

impl<'a, 'ir, B: BV> IntoIterator for &'a RegisterBindings<'ir, B> {
    type Item = (&'a Name, &'a Register<'ir, B>);
    type IntoIter = Iter<'a, 'ir, B>;

    fn into_iter(self) -> Self::IntoIter {
        Iter { iterator: self.map.iter() }
    }
}
