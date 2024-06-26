// BSD 2-Clause License
//
// Copyright (c) 2019-2024 Alasdair Armstrong
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

use ahash;

use std::collections::{HashMap, HashSet};
use std::mem;
use std::sync::Arc;

use crate::bitvector::BV;
use crate::error::ExecError;
use crate::executor::task::{Task, TaskId, TaskState};
use crate::fraction::Fraction;
use crate::ir::*;
use crate::memory::Memory;
use crate::register::RegisterBindings;
use crate::smt::{Checkpoint, Solver, Sym};

#[derive(Clone)]
pub struct LocalDebugProbes {
    pub probe_this_function: bool,
}

#[derive(Clone)]
pub struct LocalState<'ir, B> {
    pub(super) vars: Bindings<'ir, B>,
    pub(super) regs: RegisterBindings<'ir, B>,
    pub(super) lets: Bindings<'ir, B>,
    pub(super) probes: LocalDebugProbes,
}

impl<'ir, B: BV> LocalState<'ir, B> {
    pub fn should_probe(&self, shared_state: &SharedState<'ir, B>, id: &Name) -> bool {
        if !self.probes.probe_this_function {
            return false;
        }

        shared_state.probes.contains(id)
    }

    pub fn collect_symbolic_variables(&self, vars: &mut HashSet<Sym, ahash::RandomState>) {
        for (_, var) in self.vars.iter().chain(self.lets.iter()) {
            if let UVal::Init(value) = var {
                value.collect_symbolic_variables(vars)
            }
        }
        for (_, reg) in self.regs.iter() {
            reg.collect_symbolic_variables(vars)
        }
    }
}

/// The callstack is implemented as a closure that restores the
/// caller's stack frame. It additionally takes the shared state as
/// input also to avoid ownership issues when creating the closure.
pub(super) type Stack<'ir, B> = Option<
    Arc<
        dyn 'ir
            + Send
            + Sync
            + Fn(Val<B>, &mut LocalFrame<'ir, B>, &SharedState<'ir, B>, &mut Solver<B>) -> Result<(), ExecError>,
    >,
>;

pub type Backtrace = Vec<(Name, usize)>;

/// A `Frame` is an immutable snapshot of the program state while it
/// is being symbolically executed.
#[derive(Clone)]
pub struct Frame<'ir, B> {
    pub(super) function_name: Name,
    pub(super) pc: usize,
    pub(super) forks: u32,
    pub(super) backjumps: u32,
    pub(super) local_state: Arc<LocalState<'ir, B>>,
    pub(super) memory: Arc<Memory<B>>,
    pub(super) instrs: &'ir [Instr<Name, B>],
    pub(super) stack_vars: Arc<Vec<Bindings<'ir, B>>>,
    pub(super) stack_call: Stack<'ir, B>,
    pub(super) backtrace: Arc<Backtrace>,
    pub(super) function_assumptions: Arc<HashMap<Name, Vec<(Vec<Val<B>>, Val<B>)>>>,
    pub(super) pc_counts: Arc<HashMap<B, usize>>,
    pub(super) taken_interrupts: Arc<Vec<(TaskId, u8)>>,
}

pub fn unfreeze_frame<'ir, B: BV>(frame: &Frame<'ir, B>) -> LocalFrame<'ir, B> {
    LocalFrame {
        function_name: frame.function_name,
        pc: frame.pc,
        forks: frame.forks,
        backjumps: frame.backjumps,
        local_state: (*frame.local_state).clone(),
        memory: (*frame.memory).clone(),
        instrs: frame.instrs,
        stack_vars: (*frame.stack_vars).clone(),
        stack_call: frame.stack_call.clone(),
        backtrace: (*frame.backtrace).clone(),
        function_assumptions: (*frame.function_assumptions).clone(),
        pc_counts: (*frame.pc_counts).clone(),
        taken_interrupts: (*frame.taken_interrupts).clone(),
    }
}

/// A `LocalFrame` is a mutable frame which is used by a currently
/// executing thread. It is turned into an immutable `Frame` when the
/// control flow forks on a choice, which can be shared by threads.
pub struct LocalFrame<'ir, B> {
    pub(super) function_name: Name,
    pub(super) pc: usize,
    pub(super) forks: u32,
    pub(super) backjumps: u32,
    pub(super) local_state: LocalState<'ir, B>,
    pub(super) memory: Memory<B>,
    pub(super) instrs: &'ir [Instr<Name, B>],
    pub(super) stack_vars: Vec<Bindings<'ir, B>>,
    pub(super) stack_call: Stack<'ir, B>,
    pub(super) backtrace: Backtrace,
    pub(super) function_assumptions: HashMap<Name, Vec<(Vec<Val<B>>, Val<B>)>>,
    pub(super) pc_counts: HashMap<B, usize>,
    pub(super) taken_interrupts: Vec<(TaskId, u8)>,
}

pub fn freeze_frame<'ir, B: BV>(frame: &LocalFrame<'ir, B>) -> Frame<'ir, B> {
    Frame {
        function_name: frame.function_name,
        pc: frame.pc,
        forks: frame.forks,
        backjumps: frame.backjumps,
        local_state: Arc::new(frame.local_state.clone()),
        memory: Arc::new(frame.memory.clone()),
        instrs: frame.instrs,
        stack_vars: Arc::new(frame.stack_vars.clone()),
        stack_call: frame.stack_call.clone(),
        backtrace: Arc::new(frame.backtrace.clone()),
        function_assumptions: Arc::new(frame.function_assumptions.clone()),
        pc_counts: Arc::new(frame.pc_counts.clone()),
        taken_interrupts: Arc::new(frame.taken_interrupts.clone()),
    }
}

impl<'ir, B: BV> LocalFrame<'ir, B> {
    pub fn collect_symbolic_variables(&self, vars: &mut HashSet<Sym, ahash::RandomState>) {
        self.local_state.collect_symbolic_variables(vars);

        for (_, var) in self.stack_vars.iter().flat_map(|frame| frame.iter()) {
            if let UVal::Init(value) = var {
                value.collect_symbolic_variables(vars)
            }
        }
    }

    pub fn vars_mut(&mut self) -> &mut Bindings<'ir, B> {
        &mut self.local_state.vars
    }

    pub fn vars(&self) -> &Bindings<'ir, B> {
        &self.local_state.vars
    }

    pub fn regs_mut(&mut self) -> &mut RegisterBindings<'ir, B> {
        &mut self.local_state.regs
    }

    pub fn regs(&self) -> &RegisterBindings<'ir, B> {
        &self.local_state.regs
    }

    pub fn add_regs(&mut self, regs: &RegisterBindings<'ir, B>) -> &mut Self {
        for (k, v) in regs {
            self.local_state.regs.insert_register(*k, v.clone())
        }
        self
    }

    pub fn lets_mut(&mut self) -> &mut Bindings<'ir, B> {
        &mut self.local_state.lets
    }

    pub fn lets(&self) -> &Bindings<'ir, B> {
        &self.local_state.lets
    }

    pub fn add_lets(&mut self, lets: &Bindings<'ir, B>) -> &mut Self {
        for (k, v) in lets {
            self.local_state.lets.insert(*k, v.clone());
        }
        self
    }

    pub fn get_exception(&self) -> Option<(&Val<B>, &str)> {
        if let Some(UVal::Init(Val::Bool(true))) = self.lets().get(&HAVE_EXCEPTION) {
            if let Some(UVal::Init(val)) = self.lets().get(&CURRENT_EXCEPTION) {
                let loc = match self.lets().get(&THROW_LOCATION) {
                    Some(UVal::Init(Val::String(s))) => s,
                    Some(UVal::Init(_)) => "location has wrong type",
                    _ => "missing location",
                };
                Some((val, loc))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn memory(&self) -> &Memory<B> {
        &self.memory
    }

    pub fn memory_mut(&mut self) -> &mut Memory<B> {
        &mut self.memory
    }

    pub fn set_memory(&mut self, memory: Memory<B>) -> &mut Self {
        self.memory = memory;
        self
    }

    pub fn new(
        name: Name,
        args: &[(Name, &'ir Ty<Name>)],
        ret_ty: &'ir Ty<Name>,
        vals: Option<&[Val<B>]>,
        instrs: &'ir [Instr<Name, B>],
    ) -> Self {
        let mut vars = HashMap::default();
        vars.insert(RETURN, UVal::Uninit(ret_ty));
        match vals {
            Some(vals) => {
                for ((id, _), val) in args.iter().zip(vals) {
                    vars.insert(*id, UVal::Init(val.clone()));
                }
            }
            None => {
                for (id, ty) in args {
                    vars.insert(*id, UVal::Uninit(ty));
                }
            }
        }

        let mut lets = HashMap::default();
        lets.insert(HAVE_EXCEPTION, UVal::Init(Val::Bool(false)));
        lets.insert(CURRENT_EXCEPTION, UVal::Uninit(&Ty::Union(SAIL_EXCEPTION)));
        lets.insert(THROW_LOCATION, UVal::Uninit(&Ty::String));
        lets.insert(NULL, UVal::Init(Val::List(Vec::new())));

        let regs = RegisterBindings::new();

        let probe_this_function = false;
        let probes = LocalDebugProbes { probe_this_function };

        LocalFrame {
            function_name: name,
            pc: 0,
            forks: 0,
            backjumps: 0,
            local_state: LocalState { vars, regs, lets, probes },
            memory: Memory::new(),
            instrs,
            stack_vars: Vec::new(),
            stack_call: None,
            backtrace: Vec::new(),
            function_assumptions: HashMap::new(),
            pc_counts: HashMap::new(),
            taken_interrupts: Vec::new(),
        }
    }

    pub fn new_call(
        &self,
        name: Name,
        args: &[(Name, &'ir Ty<Name>)],
        ret_ty: &'ir Ty<Name>,
        vals: Option<&[Val<B>]>,
        instrs: &'ir [Instr<Name, B>],
    ) -> Self {
        let mut new_frame = LocalFrame::new(name, args, ret_ty, vals, instrs);
        new_frame.forks = self.forks;
        new_frame.local_state.regs = self.local_state.regs.clone();
        new_frame.local_state.lets = self.local_state.lets.clone();
        new_frame.memory = self.memory.clone();
        new_frame
    }

    pub fn task_with_checkpoint<'task>(
        &self,
        task_id: TaskId,
        state: &'task TaskState<B>,
        checkpoint: Checkpoint<B>,
    ) -> Task<'ir, 'task, B> {
        Task {
            id: task_id,
            fraction: Fraction::one(),
            frame: freeze_frame(self),
            checkpoint,
            fork_cond: None,
            state,
            stop_conditions: None,
        }
    }

    pub fn task<'task>(&self, task_id: TaskId, state: &'task TaskState<B>) -> Task<'ir, 'task, B> {
        self.task_with_checkpoint(task_id, state, Checkpoint::new())
    }

    pub fn set_probes(&mut self, shared_state: &SharedState<'ir, B>) {
        let should_probe_here = if shared_state.probe_functions.is_empty() {
            true
        } else {
            self.backtrace.iter().any(|(n, _)| shared_state.probe_functions.contains(n))
        };

        self.local_state.probes.probe_this_function = should_probe_here
    }
}

pub(super) fn push_call_stack<B: BV>(frame: &mut LocalFrame<'_, B>) {
    let mut vars = HashMap::default();
    mem::swap(&mut vars, frame.vars_mut());
    frame.stack_vars.push(vars)
}

pub(super) fn pop_call_stack<B: BV>(frame: &mut LocalFrame<'_, B>) {
    if let Some(mut vars) = frame.stack_vars.pop() {
        mem::swap(&mut vars, frame.vars_mut())
    }
}
