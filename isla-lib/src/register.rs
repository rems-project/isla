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

use std::collections::{hash_map, HashMap};

use crate::bitvector::BV;
use crate::error::ExecError;
use crate::ir::source_loc::SourceLoc;
use crate::ir::*;
use crate::primop_util::{ite_choice, symbolic};
use crate::smt::Solver;
use crate::zencode;

#[derive(Clone)]
enum RelaxedVal<'ir, B> {
    Uninit(&'ir Ty<Name>),
    Init {
        last_write: Val<B>,
        last_read: Option<Val<B>>,
        old_writes: Vec<Val<B>>
    }
}

#[derive(Clone)]
pub struct Register<'ir, B> {
    relaxed: bool,
    value: RelaxedVal<'ir, B>,
}

impl<'ir, B: BV> RelaxedVal<'ir, B> {
    // Returns the value, which could be any value written,
    // initializing it if needed. Guarantees that repeated calls to
    // value in between calls to synchronize or forget_last_read will
    // return the same value.
    fn read(&mut self, shared_state: &SharedState<'ir, B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
        match self {
            RelaxedVal::Uninit(ty) => {
                let sym = symbolic(ty, shared_state, solver, info)?;
                *self = RelaxedVal::Init { last_write: sym.clone(), last_read: None, old_writes: Vec::new() };
                Ok(sym)
            }
            RelaxedVal::Init { last_read: Some(v), .. } => Ok(v.clone()),
            RelaxedVal::Init { last_read, last_write, old_writes } => {
                let value = ite_choice(last_write, old_writes, solver, info)?;
                *last_read = Some(value.clone());
                Ok(value)
            }
        }
    }

    // Read the last written value
    fn read_last(&mut self, shared_state: &SharedState<'ir, B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
        match self {
            RelaxedVal::Uninit(ty) => {
                let sym = symbolic(ty, shared_state, solver, info)?;
                *self = RelaxedVal::Init { last_write: sym.clone(), last_read: None, old_writes: Vec::new() };
                Ok(sym)
            }
            RelaxedVal::Init { last_write, .. } => Ok(last_write.clone()),
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
                *self = RelaxedVal::Init{ last_write: value, last_read: None, old_writes: Vec::new() };
            }
            RelaxedVal::Init { last_write, last_read: _, old_writes } => {
                old_writes.push(last_write.clone());
                *last_write = value
            }
        }
    }

    fn write_last(&mut self, value: Val<B>) {
        match self {
            RelaxedVal::Uninit(_) => {
                *self = RelaxedVal::Init{ last_write: value, last_read: None, old_writes: Vec::new() };
            }
            RelaxedVal::Init { last_write, .. } => {
                *last_write = value
            }
        }
    }
}

impl<'ir, B: BV> Register<'ir, B> {
    pub fn read(&mut self, shared_state: &SharedState<'ir, B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
        if self.relaxed {
            self.value.read(shared_state, solver, info)
        } else {
            self.value.read_last(shared_state, solver, info)
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
    map: HashMap<Name, Register<'ir, B>>
}

pub struct Iter<'a, 'ir, B> {
    iterator: hash_map::Iter<'a, Name, Register<'ir, B>>
}

impl<'ir, B: BV> RegisterBindings<'ir, B> {
    pub fn new() -> Self {
        RegisterBindings { map: HashMap::new() }
    }

    pub fn insert(&mut self, id: Name, relaxed: bool, v: UVal<'ir, B>) {
        match v {
            UVal::Uninit(ty) => {
                self.map.insert(id, Register { relaxed, value: RelaxedVal::Uninit(ty) });
            }
            UVal::Init(value) => {
                self.map.insert(id, Register { relaxed, value: RelaxedVal::Init { last_write: value, last_read: None, old_writes: Vec::new() } });
            }
        }
    }

    pub fn insert_register(&mut self, id: Name, v: Register<'ir, B>) {
        self.map.insert(id, v);
    }

    pub fn get(&mut self, id: Name, shared_state: &SharedState<'ir, B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Option<Val<B>>, ExecError> {
        if let Some(reg) = self.map.get_mut(&id) {
            let val = reg.read(shared_state, solver, info)?;
            Ok(Some(val))
        } else {
            Ok(None)
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
