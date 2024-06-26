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

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::executor::frame::{Backtrace, Frame};
use crate::fraction::Fraction;
use crate::ir::{Loc, Name, Reset, SharedState};
use crate::smt::{smtlib, Checkpoint, Event};
use crate::zencode;

static TASK_COUNTER: AtomicUsize = AtomicUsize::new(0);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TaskId {
    id: usize,
}

impl TaskId {
    pub fn from_usize(id: usize) -> Self {
        TaskId { id }
    }

    pub fn as_usize(self) -> usize {
        self.id
    }

    pub fn fresh() -> Self {
        TaskId { id: TASK_COUNTER.fetch_add(1, Ordering::SeqCst) }
    }
}

pub struct TaskInterrupt<B> {
    pub(super) id: u8,
    pub(super) trigger_register: Name,
    pub(super) trigger_value: B,
    pub(super) reset: HashMap<Loc<Name>, Reset<B>>,
}

impl<B> TaskInterrupt<B> {
    pub fn new(id: u8, trigger_register: Name, trigger_value: B, reset: HashMap<Loc<Name>, Reset<B>>) -> Self {
        TaskInterrupt { id, trigger_register, trigger_value, reset }
    }
}

pub struct TaskState<B> {
    pub(super) reset_registers: HashMap<Loc<Name>, Reset<B>>,
    // We might want to avoid loops in the assembly by requiring that
    // any unique program counter (pc) is only visited a fixed number
    // of times. Note that this is the architectural PC, not the isla
    // IR program counter in the frame.
    pub(super) pc_limit: Option<(Name, usize)>,
    // Exit if we ever announce an instruction with all bits set to zero
    pub(super) zero_announce_exit: bool,
    pub(super) interrupts: Vec<TaskInterrupt<B>>,
}

impl<B> TaskState<B> {
    pub fn new() -> Self {
        TaskState { reset_registers: HashMap::new(), pc_limit: None, zero_announce_exit: true, interrupts: Vec::new() }
    }

    pub fn with_reset_registers(self, reset_registers: HashMap<Loc<Name>, Reset<B>>) -> Self {
        TaskState { reset_registers, ..self }
    }

    pub fn with_pc_limit(self, pc: Name, limit: usize) -> Self {
        TaskState { pc_limit: Some((pc, limit)), ..self }
    }

    pub fn with_zero_announce_exit(self, b: bool) -> Self {
        TaskState { zero_announce_exit: b, ..self }
    }

    pub fn add_interrupt(&mut self, interrupt: TaskInterrupt<B>) -> &mut Self {
        self.interrupts.push(interrupt);
        self
    }
}

impl<B> Default for TaskState<B> {
    fn default() -> Self {
        Self::new()
    }
}

/// A collection of simple conditions under which to stop the execution
/// of path. The conditions are formed of the name of a function to
/// stop at, with an optional second name that must appear in the
/// backtrace.
#[derive(Clone)]
pub struct StopConditions {
    stops: HashMap<Name, (HashMap<Name, StopAction>, Option<StopAction>)>,
}

#[derive(Clone, Copy)]
pub enum StopAction {
    Kill,     // Remove entire trace
    Abstract, // Keep trace, put abstract call at end
}

impl StopConditions {
    pub fn new() -> Self {
        StopConditions { stops: HashMap::new() }
    }

    pub fn add(&mut self, function: Name, context: Option<Name>, action: StopAction) {
        let fn_entry = self.stops.entry(function).or_insert((HashMap::new(), None));
        if let Some(ctx) = context {
            fn_entry.0.insert(ctx, action);
        } else {
            fn_entry.1 = Some(action);
        }
    }

    pub fn union(&self, other: &StopConditions) -> Self {
        let mut dest: StopConditions = self.clone();
        for (f, (ctx, direct)) in &other.stops {
            if let Some(action) = direct {
                dest.add(*f, None, *action);
            }
            for (context, action) in ctx {
                dest.add(*f, Some(*context), *action);
            }
        }
        dest
    }

    pub fn should_stop(&self, callee: Name, caller: Name, backtrace: &Backtrace) -> Option<StopAction> {
        if let Some((ctx, direct)) = self.stops.get(&callee) {
            for (name, action) in ctx {
                if *name == caller || backtrace.iter().any(|(bt_name, _)| *name == *bt_name) {
                    return Some(*action);
                }
            }
            *direct
        } else {
            None
        }
    }

    fn parse_function_name<B>(f: &str, shared_state: &SharedState<B>) -> Name {
        let fz = zencode::encode(f);
        shared_state
            .symtab
            .get(&fz)
            .or_else(|| shared_state.symtab.get(f))
            .unwrap_or_else(|| panic!("Function {} not found", f))
    }

    pub fn parse<B>(args: Vec<String>, shared_state: &SharedState<B>, action: StopAction) -> StopConditions {
        let mut conds = StopConditions::new();
        for arg in args {
            let mut names = arg.split(',');
            if let Some(f) = names.next() {
                if let Some(ctx) = names.next() {
                    if names.next().is_none() {
                        conds.add(
                            StopConditions::parse_function_name(f, shared_state),
                            Some(StopConditions::parse_function_name(ctx, shared_state)),
                            action,
                        );
                    } else {
                        panic!("Bad stop condition: {}", arg);
                    }
                } else {
                    conds.add(StopConditions::parse_function_name(f, shared_state), None, action);
                }
            } else {
                panic!("Bad stop condition: {}", arg);
            }
        }
        conds
    }
}

/// A `Task` is a suspended point in the symbolic execution of a
/// program. It consists of a frame, which is a snapshot of the
/// program variables, a checkpoint which allows us to reconstruct the
/// SMT solver state, and finally an option SMTLIB definiton which is
/// added to the solver state when the task is resumed.
pub struct Task<'ir, 'task, B> {
    pub(crate) id: TaskId,
    pub(crate) fraction: Fraction,
    pub(crate) frame: Frame<'ir, B>,
    pub(crate) checkpoint: Checkpoint<B>,
    pub(crate) fork_cond: Option<(smtlib::Def, Event<B>)>,
    pub(crate) state: &'task TaskState<B>,
    pub(crate) stop_conditions: Option<&'task StopConditions>,
}

impl<'ir, 'task, B> Task<'ir, 'task, B> {
    pub fn set_stop_conditions(&mut self, new_fns: &'task StopConditions) {
        self.stop_conditions = Some(new_fns);
    }
}
