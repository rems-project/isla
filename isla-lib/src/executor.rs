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

//! This module implements the core of the symbolic execution engine.

use crossbeam::deque::{Injector, Steal, Stealer, Worker};
use crossbeam::queue::SegQueue;
use crossbeam::thread;
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::mem;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, RwLock};
use std::thread::sleep;
use std::time::{Duration, Instant};

use crate::bitvector::BV;
use crate::error::ExecError;
use crate::ir::source_loc::SourceLoc;
use crate::ir::*;
use crate::log;
use crate::memory::Memory;
use crate::primop;
use crate::primop_util::{ite_phi, smt_value, symbolic};
use crate::probe;
use crate::register::*;
use crate::smt::smtlib::Def;
use crate::smt::*;
use crate::zencode;

#[derive(Clone)]
struct LocalState<'ir, B> {
    vars: Bindings<'ir, B>,
    regs: RegisterBindings<'ir, B>,
    lets: Bindings<'ir, B>,
}

/// Gets a value from a variable `Bindings` map. Note that this function is set up to handle the
/// following case:
///
/// ```Sail
/// var x;
/// x = 3;
/// ```
///
/// When we declare a variable it has the value `UVal::Uninit(ty)` where `ty` is its type. When
/// that variable is first accessed it'll be initialized to a symbolic value in the SMT solver if it
/// is still uninitialized. This means that in the above code, because `x` is immediately assigned
/// the value 3, no interaction with the SMT solver will occur.
fn get_and_initialize<'state, 'ir, B: BV>(
    v: Name,
    vars: &'state mut Bindings<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<&'state Val<B>>, ExecError> {
    Ok(match vars.get_mut(&v) {
        Some(uval) => match uval {
            UVal::Uninit(ty) => {
                let sym = symbolic(ty, shared_state, solver, info)?;
                *uval = UVal::Init(sym);
                if let UVal::Init(value) = uval {
                    Some(value)
                } else {
                    unreachable!()
                }
            }
            UVal::Init(value) => Some(value),
        },
        None => None,
    })
}

fn get_id_and_initialize<'state, 'ir, B: BV>(
    id: Name,
    local_state: &'state mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
    info: SourceLoc,
    for_write: bool,
) -> Result<Cow<'state, Val<B>>, ExecError> {
    use Cow::*;

    Ok(match get_and_initialize(id, &mut local_state.vars, shared_state, solver, info)? {
        Some(value) => Borrowed(value),
        None => match local_state.regs.get(id, shared_state, solver, info)? {
            Some(value) => {
                let symbol = zencode::decode(shared_state.symtab.to_str(id));
                // HACK: Don't store the entire TLB in the trace
                if !for_write && symbol != "_TLB" {
                    solver.add_event(Event::ReadReg(id, accessor.to_vec(), value.clone()));
                }
                Borrowed(value)
            }
            None => match get_and_initialize(id, &mut local_state.lets, shared_state, solver, info)? {
                Some(value) => Borrowed(value),
                None => match shared_state.enum_members.get(&id) {
                    Some((member, enum_size)) => {
                        let enum_id = solver.get_enum(*enum_size);
                        Owned(Val::Enum(EnumMember { enum_id, member: *member }))
                    }
                    None => return Err(ExecError::VariableNotFound(zencode::decode(shared_state.symtab.to_str(id)))),
                },
            },
        },
    })
}

fn get_loc_and_initialize<'ir, B: BV>(
    loc: &Loc<Name>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
    info: SourceLoc,
    for_write: bool,
) -> Result<Val<B>, ExecError> {
    Ok(match loc {
        Loc::Id(id) => {
            get_id_and_initialize(*id, local_state, shared_state, solver, accessor, info, for_write)?.into_owned()
        }
        Loc::Field(loc, field) => {
            accessor.push(Accessor::Field(*field));
            if let Val::Struct(members) =
                get_loc_and_initialize(loc, local_state, shared_state, solver, accessor, info, for_write)?
            {
                match members.get(field) {
                    Some(field_value) => field_value.clone(),
                    None => panic!("No field {:?}", shared_state.symtab.to_str(*field)),
                }
            } else {
                panic!("Struct expression did not evaluate to a struct")
            }
        }
        _ => panic!("Cannot get_loc_and_initialize"),
    })
}

fn eval_exp_with_accessor<'state, 'ir, B: BV>(
    exp: &Exp<Name>,
    local_state: &'state mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
    info: SourceLoc,
) -> Result<Cow<'state, Val<B>>, ExecError> {
    use Cow::*;
    use Exp::*;

    Ok(match exp {
        Id(id) => get_id_and_initialize(*id, local_state, shared_state, solver, accessor, info, false)?,

        I64(n) => Owned(Val::I64(*n)),
        I128(n) => Owned(Val::I128(*n)),
        Unit => Owned(Val::Unit),
        Bool(b) => Owned(Val::Bool(*b)),
        // The parser only returns 64-bit or less bitvectors
        Bits(bv) => Owned(Val::Bits(B::new(bv.lower_u64(), bv.len()))),
        String(s) => Owned(Val::String(s.clone())),

        Undefined(ty) => Owned(symbolic(ty, shared_state, solver, info)?),

        Call(op, unevaluated_args) => {
            let mut args: Vec<Val<B>> = Vec::new();
            for arg in unevaluated_args {
                args.push(eval_exp(arg, local_state, shared_state, solver, info)?.into_owned())
            }
            Owned(match op {
                Op::Lt => primop::op_lt(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Gt => primop::op_gt(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Lteq => primop::op_lteq(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Gteq => primop::op_gteq(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Eq => primop::op_eq(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Neq => primop::op_neq(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Add => primop::op_add(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Sub => primop::op_sub(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvnot => primop::not_bits(args[0].clone(), solver, info)?,
                Op::Bvor => primop::or_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvxor => primop::xor_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvand => primop::and_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvadd => primop::add_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvsub => primop::sub_bits(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Bvaccess => primop::vector_access(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Concat => primop::append(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Not => primop::not_bool(args[0].clone(), solver, info)?,
                Op::And => primop::and_bool(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Or => primop::or_bool(args[0].clone(), args[1].clone(), solver, info)?,
                Op::Slice(len) => primop::op_slice(args[0].clone(), args[1].clone(), *len, solver, info)?,
                Op::SetSlice => primop::op_set_slice(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)?,
                Op::Unsigned(_) => primop::op_unsigned(args[0].clone(), solver, info)?,
                Op::Signed(_) => primop::op_signed(args[0].clone(), solver, info)?,
                Op::Head => primop::op_head(args[0].clone(), solver, info)?,
                Op::Tail => primop::op_tail(args[0].clone(), solver, info)?,
                Op::ZeroExtend(len) => primop::op_zero_extend(args[0].clone(), *len, solver, info)?,
            })
        }

        Kind(ctor_a, exp) => {
            let v = eval_exp(exp, local_state, shared_state, solver, info)?;
            Owned(match v.as_ref() {
                Val::Ctor(ctor_b, _) => Val::Bool(*ctor_a != *ctor_b),
                Val::SymbolicCtor(ctor_sym, _) => {
                    use smtlib::Exp::*;
                    let b = solver.define_const(Neq(Box::new(Var(*ctor_sym)), Box::new(ctor_a.to_smt())), info);
                    Val::Symbolic(b)
                }
                _ => return Err(ExecError::Type(format!("Kind check on non-constructor {:?}", &v), info)),
            })
        }

        Unwrap(ctor_a, exp) => {
            let v = eval_exp(exp, local_state, shared_state, solver, info)?;
            match v {
                Borrowed(Val::Ctor(ctor_b, v)) if *ctor_a == *ctor_b => Borrowed(v),

                Owned(Val::Ctor(ctor_b, v)) if *ctor_a == ctor_b => Owned(*v),

                Borrowed(Val::SymbolicCtor(_, possibilities)) => match possibilities.get(ctor_a) {
                    Some(v) => Borrowed(v),
                    None => return Err(ExecError::Type("No possible value for constructor".to_string(), info)),
                },

                Owned(Val::SymbolicCtor(_, mut possibilities)) => match possibilities.remove(ctor_a) {
                    Some(v) => Owned(v),
                    None => return Err(ExecError::Type("No possible value for constructor".to_string(), info)),
                },

                _ => {
                    return Err(ExecError::Type(
                        format!("Tried to unwrap non-constructor, or constructors didn't match {:?}", &v),
                        info,
                    ))
                }
            }
        }

        Field(exp, field) => {
            accessor.push(Accessor::Field(*field));
            match eval_exp_with_accessor(exp, local_state, shared_state, solver, accessor, info)? {
                Borrowed(Val::Struct(struct_value)) => match struct_value.get(field) {
                    Some(field_value) => Borrowed(field_value),
                    None => panic!("No field {:?}", shared_state.symtab.to_str(*field)),
                },

                Owned(Val::Struct(mut struct_value)) => match struct_value.remove(field) {
                    Some(field_value) => Owned(field_value),
                    None => panic!("No field {:?}", shared_state.symtab.to_str(*field)),
                },

                _ => panic!("Struct expression did not evaluate to a struct"),
            }
        }

        Ref(reg) => Owned(Val::Ref(*reg)),

        _ => panic!("Could not evaluate expression {:?}", exp),
    })
}

fn eval_exp<'state, 'ir, B: BV>(
    exp: &Exp<Name>,
    local_state: &'state mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Cow<'state, Val<B>>, ExecError> {
    eval_exp_with_accessor(exp, local_state, shared_state, solver, &mut Vec::new(), info)
}

fn assign_with_accessor<'ir, B: BV>(
    loc: &Loc<Name>,
    v: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    match loc {
        Loc::Id(id) => {
            if local_state.vars.contains_key(id) || *id == RETURN {
                local_state.vars.insert(*id, UVal::Init(v));
            } else if local_state.lets.contains_key(id) {
                local_state.lets.insert(*id, UVal::Init(v));
            } else {
                let symbol = zencode::decode(shared_state.symtab.to_str(*id));
                // HACK: Don't store the entire TLB in the trace
                if symbol != "_TLB" {
                    solver.add_event(Event::WriteReg(*id, accessor.to_vec(), v.clone()))
                }
                local_state.regs.assign(*id, v, shared_state);
            }
        }

        Loc::Field(loc, field) => {
            if let Val::Struct(field_values) =
                get_loc_and_initialize(loc, local_state, shared_state, solver, &mut accessor.clone(), info, true)?
            {
                accessor.push(Accessor::Field(*field));
                // As a sanity test, check that the field exists.
                match field_values.get(field) {
                    Some(_) => {
                        let mut field_values = field_values.clone();
                        field_values.insert(*field, v);
                        assign_with_accessor(
                            loc,
                            Val::Struct(field_values),
                            local_state,
                            shared_state,
                            solver,
                            accessor,
                            info,
                        )?;
                    }
                    None => panic!("Invalid field assignment"),
                }
            } else {
                panic!(
                    "Cannot assign struct to non-struct {:?}.{:?} ({:?})",
                    loc,
                    field,
                    get_loc_and_initialize(loc, local_state, shared_state, solver, &mut accessor.clone(), info, true)
                )
            }
        }

        Loc::Addr(loc) => {
            if let Val::Ref(reg) = get_loc_and_initialize(loc, local_state, shared_state, solver, accessor, info, true)?
            {
                assign_with_accessor(&Loc::Id(reg), v, local_state, shared_state, solver, accessor, info)?
            } else {
                panic!("Cannot get address of non-reference {:?}", loc)
            }
        }
    };
    Ok(())
}

fn assign<'ir, B: BV>(
    tid: usize,
    loc: &Loc<Name>,
    v: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    let id = loc.id();
    if shared_state.probes.contains(&id) {
        let mut symbol = String::from(shared_state.symtab.to_str(id));
        if symbol.starts_with('z') {
            symbol = zencode::decode(&symbol);
        }
        log_from!(tid, log::PROBE, &format!("Assigning {}[{:?}] <- {:?}", symbol, id, v))
    }

    assign_with_accessor(loc, v, local_state, shared_state, solver, &mut Vec::new(), info)
}

/// The callstack is implemented as a closure that restores the
/// caller's stack frame. It additionally takes the shared state as
/// input also to avoid ownership issues when creating the closure.
type Stack<'ir, B> = Option<
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
    function_name: Name,
    pc: usize,
    forks: u32,
    backjumps: u32,
    local_state: Arc<LocalState<'ir, B>>,
    memory: Arc<Memory<B>>,
    instrs: &'ir [Instr<Name, B>],
    stack_vars: Arc<Vec<Bindings<'ir, B>>>,
    stack_call: Stack<'ir, B>,
    backtrace: Arc<Backtrace>,
}

/// A `LocalFrame` is a mutable frame which is used by a currently
/// executing thread. It is turned into an immutable `Frame` when the
/// control flow forks on a choice, which can be shared by threads.
pub struct LocalFrame<'ir, B> {
    function_name: Name,
    pc: usize,
    forks: u32,
    backjumps: u32,
    local_state: LocalState<'ir, B>,
    memory: Memory<B>,
    instrs: &'ir [Instr<Name, B>],
    stack_vars: Vec<Bindings<'ir, B>>,
    stack_call: Stack<'ir, B>,
    backtrace: Backtrace,
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
    }
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
    }
}

impl<'ir, B: BV> LocalFrame<'ir, B> {
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
        vals: Option<&[Val<B>]>,
        instrs: &'ir [Instr<Name, B>],
    ) -> Self {
        let mut vars = HashMap::default();
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

        LocalFrame {
            function_name: name,
            pc: 0,
            forks: 0,
            backjumps: 0,
            local_state: LocalState { vars, regs, lets },
            memory: Memory::new(),
            instrs,
            stack_vars: Vec::new(),
            stack_call: None,
            backtrace: Vec::new(),
        }
    }

    pub fn new_call(
        &self,
        name: Name,
        args: &[(Name, &'ir Ty<Name>)],
        vals: Option<&[Val<B>]>,
        instrs: &'ir [Instr<Name, B>],
    ) -> Self {
        let mut new_frame = LocalFrame::new(name, args, vals, instrs);
        new_frame.forks = self.forks;
        new_frame.local_state.regs = self.local_state.regs.clone();
        new_frame.local_state.lets = self.local_state.lets.clone();
        new_frame.memory = self.memory.clone();
        new_frame
    }

    pub fn task_with_checkpoint<'task>(
        &self,
        task_id: usize,
        state: &'task TaskState<B>,
        checkpoint: Checkpoint<B>,
    ) -> Task<'ir, 'task, B> {
        Task { id: task_id, frame: freeze_frame(self), checkpoint, fork_cond: None, state, stop_conditions: None }
    }

    pub fn task<'task>(&self, task_id: usize, state: &'task TaskState<B>) -> Task<'ir, 'task, B> {
        self.task_with_checkpoint(task_id, state, Checkpoint::new())
    }
}

fn push_call_stack<B: BV>(frame: &mut LocalFrame<'_, B>) {
    let mut vars = HashMap::default();
    mem::swap(&mut vars, frame.vars_mut());
    frame.stack_vars.push(vars)
}

fn pop_call_stack<B: BV>(frame: &mut LocalFrame<'_, B>) {
    if let Some(mut vars) = frame.stack_vars.pop() {
        mem::swap(&mut vars, frame.vars_mut())
    }
}

#[derive(Copy, Clone, Debug)]
struct Timeout {
    start_time: Instant,
    duration: Option<Duration>,
}

impl Timeout {
    fn unlimited() -> Self {
        Timeout { start_time: Instant::now(), duration: None }
    }

    fn timed_out(&self) -> bool {
        self.duration.is_some() && self.start_time.elapsed() > self.duration.unwrap()
    }
}

pub fn reset_registers<'ir, 'task, B: BV>(
    _tid: usize,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    for (loc, reset) in &shared_state.reset_registers {
        if !task_state.reset_registers.contains_key(loc) {
            let value = reset(&frame.memory, shared_state.typedefs(), solver)?;
            let mut accessor = Vec::new();
            assign_with_accessor(
                loc,
                value.clone(),
                &mut frame.local_state,
                shared_state,
                solver,
                &mut accessor,
                info,
            )?;
            // Note that these are just the assumptions from reset_registers; there
            // may also be assumptions from default register values, recorded at the
            // top level.
            solver.add_event(Event::AssumeReg(loc.id(), accessor, value));
        }
    }
    for (loc, reset) in &task_state.reset_registers {
        let value = reset(&frame.memory, shared_state.typedefs(), solver)?;
        let mut accessor = Vec::new();
        assign_with_accessor(loc, value.clone(), &mut frame.local_state, shared_state, solver, &mut accessor, info)?;
        solver.add_event(Event::AssumeReg(loc.id(), accessor, value));
    }
    if !shared_state.reset_constraints.is_empty() {
        for constraint in &shared_state.reset_constraints {
            let mut lookup = |s| match shared_state.symtab.get_loc(s) {
                Some(loc) => {
                    let value = get_loc_and_initialize(
                        &loc,
                        &mut frame.local_state,
                        shared_state,
                        solver,
                        &mut Vec::new(),
                        info,
                        false,
                    )
                    .map_err(|e| e.to_string())?;
                    smt_value(&value, info).map_err(|e| e.to_string())
                }
                None => Err(format!("Location {} not found", s)),
            };
            let assertion_exp = constraint.map_var(&mut lookup).map_err(ExecError::Unreachable)?;
            solver.add_event(Event::Assume(constraint.clone()));
            solver.add(Def::Assert(assertion_exp));
        }
        if solver.check_sat().is_unsat()? {
            return Err(ExecError::Dead);
        }
    }
    Ok(())
}

// A collection of simple conditions under which to stop the execution
// of path.  The conditions are formed of the name of a function to
// stop at, with an optional second name that must appear in the
// backtrace.

#[derive(Clone)]
pub struct StopConditions {
    stops: HashMap<Name, HashSet<Name>>,
}

impl StopConditions {
    pub fn new() -> Self {
        StopConditions { stops: HashMap::new() }
    }
    pub fn add(&mut self, function: Name, context: Option<Name>) {
        if let Some(v) = self.stops.get_mut(&function) {
            if let Some(ctx) = context {
                v.insert(ctx);
            } else {
                *v = HashSet::new();
            }
        } else {
            self.stops.insert(function, context.iter().copied().collect());
        }
    }
    pub fn union(&self, other: &StopConditions) -> Self {
        let mut dest: StopConditions = self.clone();
        for (f, ctx) in &other.stops {
            if ctx.is_empty() {
                dest.add(*f, None);
            } else {
                for context in ctx {
                    dest.add(*f, Some(*context));
                }
            }
        }
        dest
    }
    pub fn should_stop(&self, callee: Name, caller: Name, backtrace: &Backtrace) -> bool {
        if let Some(names) = self.stops.get(&callee) {
            if !names.is_empty() {
                names.contains(&caller) || backtrace.iter().any(|(name, _)| names.contains(&name))
            } else {
                true
            }
        } else {
            false
        }
    }

    fn parse_function_name<B>(f: &str, shared_state: &SharedState<B>) -> Name {
        let fz = zencode::encode(f);
        shared_state
            .symtab
            .get(&fz)
            .or_else(|| shared_state.symtab.get(&f))
            .unwrap_or_else(|| panic!("Function {} not found", f))
    }

    pub fn parse<B>(args: Vec<String>, shared_state: &SharedState<B>) -> StopConditions {
        let mut conds = StopConditions::new();
        for arg in args {
            let mut names = arg.split(',');
            if let Some(f) = names.next() {
                if let Some(ctx) = names.next() {
                    if let None = names.next() {
                        conds.add(StopConditions::parse_function_name(f, shared_state), Some(StopConditions::parse_function_name(ctx, shared_state)));
                    } else {
                        panic!("Bad stop condition: {}", arg);
                    }
                } else {
                    conds.add(StopConditions::parse_function_name(f, shared_state), None);
                }
            } else {
                panic!("Bad stop condition: {}", arg);
            }
        }
        conds
    }
}

#[allow(clippy::too_many_arguments)]
fn run<'ir, 'task, B: BV>(
    tid: usize,
    task_id: usize,
    timeout: Timeout,
    stop_conditions: Option<&'task StopConditions>,
    queue: &Worker<Task<'ir, 'task, B>>,
    frame: &Frame<'ir, B>,
    task_state: &'task TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<(Val<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)> {
    let mut frame = unfreeze_frame(frame);
    match run_loop(tid, task_id, timeout, stop_conditions, queue, &mut frame, task_state, shared_state, solver) {
        Ok(v) => Ok((v, frame)),
        Err(err) => {
            frame.backtrace.push((frame.function_name, frame.pc));
            Err((err, frame.backtrace))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn run_loop<'ir, 'task, B: BV>(
    tid: usize,
    task_id: usize,
    timeout: Timeout,
    stop_conditions: Option<&'task StopConditions>,
    queue: &Worker<Task<'ir, 'task, B>>,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    loop {
        if frame.pc >= frame.instrs.len() {
            // Currently this happens when evaluating letbindings.
            log_from!(tid, log::VERBOSE, "Fell from end of instruction list");
            return Ok(Val::Unit);
        }

        if timeout.timed_out() {
            return Err(ExecError::Timeout);
        }

        match &frame.instrs[frame.pc] {
            Instr::Decl(v, ty, _) => {
                frame.vars_mut().insert(*v, UVal::Uninit(ty));
                frame.pc += 1;
            }

            Instr::Init(var, _, exp, info) => {
                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                frame.vars_mut().insert(*var, UVal::Init(value));
                frame.pc += 1;
            }

            Instr::Jump(exp, target, info) => {
                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver, *info)?;
                match *value.as_ref() {
                    Val::Symbolic(v) => {
                        use smtlib::Def::*;
                        use smtlib::Exp::*;

                        let test_true = Var(v);
                        let test_false = Not(Box::new(Var(v)));
                        let can_be_true = solver.check_sat_with(&test_true).is_sat()?;
                        let can_be_false = solver.check_sat_with(&test_false).is_sat()?;

                        if can_be_true && can_be_false {
                            if_logging!(log::FORK, {
                                log_from!(tid, log::FORK, &format!("{:?}", info));
                                probe::taint_info(log::FORK, v, Some(shared_state), solver)
                            });

                            let point = checkpoint(solver);
                            let frozen = Frame { pc: frame.pc + 1, ..freeze_frame(frame) };
                            frame.forks += 1;
                            queue.push(Task {
                                id: task_id,
                                frame: frozen,
                                checkpoint: point,
                                fork_cond: Some((Assert(test_false), Event::Fork(frame.forks - 1, v, 1, *info))),
                                state: task_state,
                                stop_conditions,
                            });

                            // Track which asserts are assocated with each fork in the trace, so we
                            // can turn a set of traces into a tree later
                            solver.add_event(Event::Fork(frame.forks - 1, v, 0, *info));

                            solver.add(Assert(test_true));
                            frame.pc = *target
                        } else if can_be_true {
                            solver.add(Assert(test_true));
                            frame.pc = *target
                        } else if can_be_false {
                            solver.add(Assert(test_false));
                            frame.pc += 1
                        } else {
                            return Err(ExecError::Dead);
                        }
                    }
                    Val::Bool(jump) => {
                        if jump {
                            frame.pc = *target
                        } else {
                            frame.pc += 1
                        }
                    }
                    _ => {
                        return Err(ExecError::Type(format!("Jump on non boolean {:?}", &value), *info));
                    }
                }
            }

            Instr::Goto(target) => frame.pc = *target,

            Instr::Copy(loc, exp, info) => {
                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::PrimopUnary(loc, f, arg, info) => {
                let arg = eval_exp(arg, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                let value = f(arg, solver, *info)?;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::PrimopBinary(loc, f, arg1, arg2, info) => {
                let arg1 = eval_exp(arg1, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                let arg2 = eval_exp(arg2, &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                let value = f(arg1, arg2, solver, *info)?;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::PrimopVariadic(loc, f, args, info) => {
                let args = args
                    .iter()
                    .map(|arg| eval_exp(arg, &mut frame.local_state, shared_state, solver, *info).map(Cow::into_owned))
                    .collect::<Result<_, _>>()?;
                let value = f(args, solver, frame, *info)?;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::Call(loc, _, f, args, info) => {
                if let Some(s) = stop_conditions {
                    if s.should_stop(*f, frame.function_name, &frame.backtrace) {
                        let symbol = zencode::decode(shared_state.symtab.to_str(*f));
                        return Err(ExecError::Stopped(symbol));
                    }
                }

                match shared_state.functions.get(f) {
                    None => {
                        if *f == INTERNAL_VECTOR_INIT && args.len() == 1 {
                            let arg =
                                eval_exp(&args[0], &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                            match loc {
                                Loc::Id(v) => match (arg, frame.vars().get(v)) {
                                    (Val::I64(len), Some(UVal::Uninit(Ty::Vector(_)))) => assign(
                                        tid,
                                        loc,
                                        Val::Vector(vec![Val::Poison; len as usize]),
                                        &mut frame.local_state,
                                        shared_state,
                                        solver,
                                        *info,
                                    )?,
                                    _ => {
                                        return Err(ExecError::Type(format!("internal_vector_init {:?}", &loc), *info))
                                    }
                                },
                                _ => return Err(ExecError::Type(format!("internal_vector_init {:?}", &loc), *info)),
                            };
                            frame.pc += 1
                        } else if *f == INTERNAL_VECTOR_UPDATE && args.len() == 3 {
                            let args = args
                                .iter()
                                .map(|arg| {
                                    eval_exp(arg, &mut frame.local_state, shared_state, solver, *info)
                                        .map(Cow::into_owned)
                                })
                                .collect::<Result<Vec<Val<B>>, _>>()?;
                            let vector = primop::vector_update(args, solver, frame, *info)?;
                            assign(tid, loc, vector, &mut frame.local_state, shared_state, solver, *info)?;
                            frame.pc += 1
                        } else if *f == SAIL_EXIT {
                            return Err(ExecError::Exit);
                        } else if *f == RESET_REGISTERS {
                            reset_registers(tid, frame, task_state, shared_state, solver, *info)?;
                            frame.regs_mut().synchronize();
                            frame.pc += 1
                        } else if *f == ITE_PHI {
                            let mut true_value = None;
                            let mut symbolics = Vec::new();
                            for cond in args.chunks_exact(2) {
                                let cond_var =
                                    match eval_exp(&cond[0], &mut frame.local_state, shared_state, solver, *info) {
                                        Ok(cond_var) => cond_var.into_owned(),
                                        // A variable not found error indicates that the block associated with this condition variable
                                        // has not been executed
                                        Err(ExecError::VariableNotFound(_)) => Val::Bool(false),
                                        Err(err) => return Err(err),
                                    };
                                match cond_var {
                                    Val::Bool(true) => {
                                        true_value = Some(
                                            eval_exp(&cond[1], &mut frame.local_state, shared_state, solver, *info)?
                                                .into_owned(),
                                        )
                                    }
                                    Val::Bool(false) => (),
                                    Val::Symbolic(sym) => symbolics.push((sym, &cond[1])),
                                    _ => return Err(ExecError::Type("ite_phi".to_string(), *info)),
                                }
                            }
                            if let Some(true_value) = true_value {
                                assign(tid, loc, true_value, &mut frame.local_state, shared_state, solver, *info)?
                            } else {
                                let symbolics = symbolics
                                    .iter()
                                    .map(|(sym, arg)| {
                                        Ok((
                                            *sym,
                                            eval_exp(arg, &mut frame.local_state, shared_state, solver, *info)?
                                                .into_owned(),
                                        ))
                                    })
                                    .collect::<Result<Vec<(Sym, Val<B>)>, _>>()?;
                                let result = ite_phi(&symbolics[0], &symbolics[1..], solver, *info)?;
                                assign(tid, loc, result, &mut frame.local_state, shared_state, solver, *info)?
                            }
                            frame.pc += 1
                        } else if *f == REG_DEREF && args.len() == 1 {
                            if let Val::Ref(reg) =
                                eval_exp(&args[0], &mut frame.local_state, shared_state, solver, *info)?.into_owned()
                            {
                                match frame.regs_mut().get(reg, shared_state, solver, *info)? {
                                    Some(value) => {
                                        solver.add_event(Event::ReadReg(reg, Vec::new(), value.clone()));
                                        assign(
                                            tid,
                                            loc,
                                            value.clone(),
                                            &mut frame.local_state,
                                            shared_state,
                                            solver,
                                            *info,
                                        )?
                                    }
                                    None => return Err(ExecError::Type(format!("reg_deref {:?}", &reg), *info)),
                                }
                            } else {
                                return Err(ExecError::Type(format!("reg_deref (not a register) {:?}", &f), *info));
                            };
                            frame.pc += 1
                        } else if *f == ABSTRACT_CALL && !args.is_empty() {
                            let mut args = args
                                .iter()
                                .map(|arg| {
                                    eval_exp(arg, &mut frame.local_state, shared_state, solver, *info)
                                        .map(Cow::into_owned)
                                })
                                .collect::<Result<Vec<Val<B>>, _>>()?;
                            let abstracted_fn = match args.pop().unwrap() {
                                Val::Ref(f) => f,
                                _ => panic!("Invalid abstract call (no function name provided)"),
                            };
                            let return_ty = &shared_state.functions[&abstracted_fn].1;
                            let return_value = symbolic(return_ty, shared_state, solver, *info)?;
                            solver.add_event(Event::Abstract { name: abstracted_fn, args, return_value });
                            frame.pc += 1
                        } else if shared_state.union_ctors.contains(f) {
                            assert!(args.len() == 1);
                            let arg =
                                eval_exp(&args[0], &mut frame.local_state, shared_state, solver, *info)?.into_owned();
                            assign(
                                tid,
                                loc,
                                Val::Ctor(*f, Box::new(arg)),
                                &mut frame.local_state,
                                shared_state,
                                solver,
                                *info,
                            )?;
                            frame.pc += 1
                        } else {
                            let symbol = zencode::decode(shared_state.symtab.to_str(*f));
                            panic!("Attempted to call non-existent function {} ({:?})", symbol, *f)
                        }
                    }

                    Some((params, _, instrs)) => {
                        let mut args = args
                            .iter()
                            .map(|arg| {
                                eval_exp(arg, &mut frame.local_state, shared_state, solver, *info).map(Cow::into_owned)
                            })
                            .collect::<Result<Vec<Val<B>>, _>>()?;

                        if shared_state.probes.contains(f) {
                            log_from!(tid, log::PROBE, probe::call_info(*f, &args, &shared_state.symtab));
                            probe::args_info(tid, &args, shared_state, solver)
                        }

                        if shared_state.trace_functions.contains(f) {
                            solver.trace_call(*f)
                        }

                        let caller_pc = frame.pc;
                        let caller_instrs = frame.instrs;
                        let caller_stack_call = frame.stack_call.clone();
                        push_call_stack(frame);
                        frame.backtrace.push((frame.function_name, caller_pc));
                        frame.function_name = *f;

                        // Set up a closure to restore our state when
                        // the function we call returns
                        frame.stack_call = Some(Arc::new(move |ret, frame, shared_state, solver| {
                            pop_call_stack(frame);
                            // could avoid putting caller_pc into the stack?
                            if let Some((name, _)) = frame.backtrace.pop() {
                                frame.function_name = name;
                            }
                            frame.pc = caller_pc + 1;
                            frame.instrs = caller_instrs;
                            frame.stack_call = caller_stack_call.clone();
                            assign(tid, &loc.clone(), ret, &mut frame.local_state, shared_state, solver, *info)
                        }));

                        for (i, arg) in args.drain(..).enumerate() {
                            frame.vars_mut().insert(params[i].0, UVal::Init(arg));
                        }
                        frame.pc = 0;
                        frame.instrs = instrs;
                    }
                }
            }

            Instr::End => match frame.vars().get(&RETURN) {
                None => panic!("Reached end without assigning to return"),
                Some(value) => {
                    let value = match value {
                        UVal::Uninit(ty) => symbolic(ty, shared_state, solver, SourceLoc::unknown())?,
                        UVal::Init(value) => value.clone(),
                    };

                    if shared_state.probes.contains(&frame.function_name) {
                        let symbol = zencode::decode(shared_state.symtab.to_str(frame.function_name));
                        log_from!(
                            tid,
                            log::PROBE,
                            &format!("Returning {} = {}", symbol, value.to_string(&shared_state.symtab))
                        );
                        probe::args_info(tid, std::slice::from_ref(&value), shared_state, solver)
                    }

                    if shared_state.trace_functions.contains(&frame.function_name) {
                        solver.trace_return(frame.function_name)
                    }

                    let caller = match &frame.stack_call {
                        None => return Ok(value),
                        Some(caller) => Arc::clone(caller),
                    };
                    (*caller)(value, frame, shared_state, solver)?
                }
            },

            // The idea beind the Monomorphize operation is it takes a
            // bitvector identifier, and if that identifer has a
            // symbolic value, then it uses the SMT solver to find all
            // the possible values for that bitvector and case splits
            // (i.e. forks) on them. This allows us to guarantee that
            // certain bitvectors are non-symbolic, at the cost of
            // increasing the number of paths.
            Instr::Monomorphize(id, info) => {
                let val = get_id_and_initialize(
                    *id,
                    &mut frame.local_state,
                    shared_state,
                    solver,
                    &mut Vec::new(),
                    *info,
                    false,
                )?;
                if let Val::Symbolic(v) = *val.as_ref() {
                    use smtlib::bits64;
                    use smtlib::Def::*;
                    use smtlib::Exp::*;
                    use smtlib::Ty::*;

                    let point = checkpoint(solver);

                    let len =
                        solver.length(v).ok_or_else(|| ExecError::Type(format!("_monomorphize {:?}", &v), *info))?;

                    // For the variable v to appear in the model, there must be some assertion that references it
                    let sym = solver.declare_const(BitVec(len), *info);
                    solver.assert_eq(Var(v), Var(sym));

                    if solver.check_sat().is_unsat()? {
                        return Err(ExecError::Dead);
                    }

                    let (result, size) = {
                        let mut model = Model::new(solver);
                        log_from!(tid, log::FORK, format!("Model: {:?}", model));
                        match model.get_var(v) {
                            Ok(Some(Bits64(bv))) => (bv.lower_u64(), bv.len()),
                            // __monomorphize should have a 'n <= 64 constraint in Sail
                            Ok(Some(other)) => {
                                return Err(ExecError::Type(format!("__monomorphize {:?}", &other), *info))
                            }
                            Ok(None) => return Err(ExecError::Z3Error(format!("No value for variable v{}", v))),
                            Err(error) => return Err(error),
                        }
                    };

                    let loc = format!("Fork @ monomorphizing v{}", v);
                    log_from!(tid, log::FORK, loc);

                    frame.forks += 1;

                    queue.push(Task {
                        id: task_id,
                        frame: freeze_frame(frame),
                        checkpoint: point,
                        fork_cond: Some((
                            Assert(Neq(Box::new(Var(v)), Box::new(bits64(result, size)))),
                            Event::Fork(frame.forks - 1, v, 1, *info),
                        )),
                        state: task_state,
                        stop_conditions,
                    });

                    solver.add_event(Event::Fork(frame.forks - 1, v, 0, *info));

                    solver.assert_eq(Var(v), bits64(result, size));

                    assign(
                        tid,
                        &Loc::Id(*id),
                        Val::Bits(B::new(result, size)),
                        &mut frame.local_state,
                        shared_state,
                        solver,
                        *info,
                    )?;
                }
                frame.pc += 1
            }

            // Arbitrary means return any value. It is used in the
            // Sail->C compilation for exceptional control flow paths
            // to avoid compiler warnings (which would also be UB in
            // C++ compilers). The value should never be used, so we
            // return Val::Poison here.
            Instr::Arbitrary => {
                if shared_state.probes.contains(&frame.function_name) {
                    let symbol = zencode::decode(shared_state.symtab.to_str(frame.function_name));
                    log_from!(
                        tid,
                        log::PROBE,
                        &format!("Returning via arbitrary {}[{:?}] = poison", symbol, frame.function_name)
                    );
                }

                if shared_state.trace_functions.contains(&frame.function_name) {
                    solver.trace_return(frame.function_name)
                }

                let caller = match &frame.stack_call {
                    None => return Ok(Val::Poison),
                    Some(caller) => Arc::clone(caller),
                };
                (*caller)(Val::Poison, frame, shared_state, solver)?
            }

            Instr::Failure => return Err(ExecError::MatchFailure),
        }
    }
}

/// A collector is run on the result of each path found via symbolic execution through the code. It
/// takes the result of the execution, which is either a combination of the return value and local
/// state at the end of the execution or an error, as well as the shared state and the SMT solver
/// state associated with that execution. It build a final result for all the executions by
/// collecting the results into a type R.
pub type Collector<'ir, B, R> = dyn 'ir
    + Sync
    + Fn(usize, usize, Result<(Val<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>, &SharedState<'ir, B>, Solver<B>, &R);

pub struct TaskState<B> {
    reset_registers: HashMap<Loc<Name>, Reset<B>>,
}

impl<B> TaskState<B> {
    pub fn new() -> Self {
        TaskState { reset_registers: HashMap::new() }
    }

    pub fn with_reset_registers(reset_registers: HashMap<Loc<Name>, Reset<B>>) -> Self {
        TaskState { reset_registers }
    }
}

impl<B> Default for TaskState<B> {
    fn default() -> Self {
        Self::new()
    }
}

/// A `Task` is a suspended point in the symbolic execution of a
/// program. It consists of a frame, which is a snapshot of the
/// program variables, a checkpoint which allows us to reconstruct the
/// SMT solver state, and finally an option SMTLIB definiton which is
/// added to the solver state when the task is resumed.
pub struct Task<'ir, 'task, B> {
    id: usize,
    frame: Frame<'ir, B>,
    checkpoint: Checkpoint<B>,
    fork_cond: Option<(smtlib::Def, Event<B>)>,
    state: &'task TaskState<B>,
    stop_conditions: Option<&'task StopConditions>,
}

impl<'ir, 'task, B> Task<'ir, 'task, B> {
    pub fn set_stop_conditions(&mut self, new_fns: &'task StopConditions) {
        self.stop_conditions = Some(new_fns);
    }
}

/// Start symbolically executing a Task using just the current thread, collecting the results using
/// the given collector.
pub fn start_single<'ir, 'task, B: BV, R>(
    task: Task<'ir, 'task, B>,
    shared_state: &SharedState<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) {
    let queue = Worker::new_lifo();
    queue.push(task);
    while let Some(task) = queue.pop() {
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
        if let Some((def, event)) = task.fork_cond {
            solver.add_event(event);

            solver.add(def)
        };
        let result = run(
            0,
            task.id,
            Timeout::unlimited(),
            task.stop_conditions,
            &queue,
            &task.frame,
            task.state,
            shared_state,
            &mut solver,
        );
        collector(0, task.id, result, shared_state, solver, collected)
    }
}

fn find_task<T>(local: &Worker<T>, global: &Injector<T>, stealers: &RwLock<Vec<Stealer<T>>>) -> Option<T> {
    let stealers = stealers.read().unwrap();
    local.pop().or_else(|| {
        std::iter::repeat_with(|| {
            let stolen: Steal<T> = stealers.iter().map(|s| s.steal()).collect();
            stolen.or_else(|| global.steal_batch_and_pop(local))
        })
        .find(|s| !s.is_retry())
        .and_then(|s| s.success())
    })
}

fn do_work<'ir, 'task, B: BV, R>(
    tid: usize,
    timeout: Timeout,
    queue: &Worker<Task<'ir, 'task, B>>,
    task: Task<'ir, 'task, B>,
    shared_state: &SharedState<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) {
    let cfg = Config::new();
    let ctx = Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
    if let Some((def, event)) = task.fork_cond {
        solver.add_event(event);
        solver.add(def)
    };
    let result =
        run(tid, task.id, timeout, task.stop_conditions, queue, &task.frame, task.state, shared_state, &mut solver);
    collector(tid, task.id, result, shared_state, solver, collected)
}

enum Response {
    Poke,
    Kill,
}

#[derive(Clone)]
enum Activity {
    Idle(usize, Sender<Response>),
    Busy(usize),
}

/// Start symbolically executing a Task across `num_threads` new threads, collecting the results
/// using the given collector.
pub fn start_multi<'ir, 'task, B: BV, R>(
    num_threads: usize,
    timeout: Option<u64>,
    tasks: Vec<Task<'ir, 'task, B>>,
    shared_state: &SharedState<'ir, B>,
    collected: Arc<R>,
    collector: &Collector<'ir, B, R>,
) where
    R: Send + Sync,
{
    let timeout = Timeout { start_time: Instant::now(), duration: timeout.map(Duration::from_secs) };

    let (tx, rx): (Sender<Activity>, Receiver<Activity>) = mpsc::channel();
    let global: Arc<Injector<Task<B>>> = Arc::new(Injector::<Task<B>>::new());
    let stealers: Arc<RwLock<Vec<Stealer<Task<B>>>>> = Arc::new(RwLock::new(Vec::new()));

    for task in tasks {
        global.push(task);
    }

    thread::scope(|scope| {
        for tid in 0..num_threads {
            // When a worker is idle, it reports that to the main orchestrating thread, which can
            // then 'poke' it to wake it up via a channel, which will cause the worker to try to
            // steal some work, or the main thread can kill the worker.
            let (poke_tx, poke_rx): (Sender<Response>, Receiver<Response>) = mpsc::channel();
            let thread_tx = tx.clone();
            let global = global.clone();
            let stealers = stealers.clone();
            let collected = collected.clone();

            scope.spawn(move |_| {
                let q = Worker::new_lifo();
                {
                    let mut stealers = stealers.write().unwrap();
                    stealers.push(q.stealer());
                }
                loop {
                    if let Some(task) = find_task(&q, &global, &stealers) {
                        thread_tx.send(Activity::Busy(tid)).unwrap();
                        do_work(tid, timeout, &q, task, shared_state, collected.as_ref(), collector);
                        while let Some(task) = find_task(&q, &global, &stealers) {
                            do_work(tid, timeout, &q, task, shared_state, collected.as_ref(), collector)
                        }
                    };
                    thread_tx.send(Activity::Idle(tid, poke_tx.clone())).unwrap();
                    match poke_rx.recv().unwrap() {
                        Response::Poke => (),
                        Response::Kill => break,
                    }
                }
            });
        }

        // Figuring out when to exit is a little complex. We start with only a few threads able to
        // work because we haven't actually explored any of the state space, so all the other
        // workers start idle and repeatedly try to steal work. There may be points when workers
        // have no work, but we want them to become active again if more work becomes available. We
        // therefore want to exit only when 1) all threads are idle, 2) we've told all the threads
        // to steal some work, and 3) all the threads fail to do so and remain idle.
        let mut current_activity = vec![0; num_threads];
        let mut last_messages = vec![Activity::Busy(0); num_threads];
        loop {
            loop {
                match rx.try_recv() {
                    Ok(Activity::Busy(tid)) => {
                        last_messages[tid] = Activity::Busy(tid);
                        current_activity[tid] = 0;
                    }
                    Ok(Activity::Idle(tid, poke)) => {
                        last_messages[tid] = Activity::Idle(tid, poke);
                        current_activity[tid] += 1;
                    }
                    Err(_) => break,
                }
            }
            let mut quiescent = true;
            for idleness in &current_activity {
                if *idleness < 2 {
                    quiescent = false
                }
            }
            if quiescent {
                for message in &last_messages {
                    match message {
                        Activity::Idle(_tid, poke) => poke.send(Response::Kill).unwrap(),
                        Activity::Busy(tid) => panic!("Found busy thread {} when quiescent", tid),
                    }
                }
                break;
            }
            for message in &last_messages {
                match message {
                    Activity::Idle(tid, poke) => {
                        poke.send(Response::Poke).unwrap();
                        current_activity[*tid] = 1;
                    }
                    Activity::Busy(_) => (),
                }
            }
            sleep(Duration::from_millis(1))
        }
    })
    .unwrap();
}

/// This `Collector` is used for boolean Sail functions. It returns
/// true via an AtomicBool if all reachable paths through the program
/// are unsatisfiable, which implies that the function always returns
/// true.
pub fn all_unsat_collector<'ir, B: BV>(
    tid: usize,
    _: usize,
    result: Result<(Val<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &AtomicBool,
) {
    match result {
        Ok(value) => match value {
            (Val::Symbolic(v), _) => {
                use smtlib::Def::*;
                use smtlib::Exp::*;
                solver.add(Assert(Not(Box::new(Var(v)))));
                if solver.check_sat() != SmtResult::Unsat {
                    log_from!(tid, log::VERBOSE, "Got sat");
                    collected.store(false, Ordering::Release)
                } else {
                    log_from!(tid, log::VERBOSE, "Got unsat")
                }
            }
            (Val::Bool(true), _) => log_from!(tid, log::VERBOSE, "Got true"),
            (Val::Bool(false), _) => {
                log_from!(tid, log::VERBOSE, "Got false");
                collected.store(false, Ordering::Release)
            }
            (value, _) => log_from!(tid, log::VERBOSE, &format!("Got value {:?}", value)),
        },
        Err((err, backtrace)) => match err {
            ExecError::Dead => log_from!(tid, log::VERBOSE, "Dead"),
            _ => {
                if_logging!(log::VERBOSE, {
                    log_from!(tid, log::VERBOSE, &format!("Got error, {:?}", err));
                    for (f, pc) in backtrace.iter().rev() {
                        log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
                    }
                });
                collected.store(false, Ordering::Release)
            }
        },
    }
}

pub type TraceQueue<B> = SegQueue<Result<(usize, Vec<Event<B>>), String>>;

pub type TraceResultQueue<B> = SegQueue<Result<(usize, bool, Vec<Event<B>>), String>>;

pub type TraceValueQueue<B> = SegQueue<Result<(usize, Val<B>, Vec<Event<B>>), String>>;

pub fn trace_collector<'ir, B: BV>(
    _: usize,
    task_id: usize,
    result: Result<(Val<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    _: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    match result {
        Ok(_) | Err((ExecError::Exit, _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, events.drain(..).cloned().collect())))
        }
        Err((ExecError::Dead, _)) => (),
        Err((err, _)) => {
            if solver.check_sat() == SmtResult::Sat {
                let model = Model::new(&solver);
                collected.push(Err(format!("Error {:?}\n{:?}", err, model)))
            } else {
                collected.push(Err(format!("Error {:?}\nno model", err)))
            }
        }
    }
}

pub fn trace_value_collector<'ir, B: BV>(
    _: usize,
    task_id: usize,
    result: Result<(Val<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    _: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &TraceValueQueue<B>,
) {
    match result {
        Ok((val, _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, val, events.drain(..).cloned().collect())))
        }
        Err((ExecError::Dead, _)) => (),
        Err((err, _)) => {
            if solver.check_sat() == SmtResult::Sat {
                let model = Model::new(&solver);
                collected.push(Err(format!("Error {:?}\n{:?}", err, model)))
            } else {
                collected.push(Err(format!("Error {:?}\nno model", err)))
            }
        }
    }
}

pub fn trace_result_collector<'ir, B: BV>(
    _: usize,
    task_id: usize,
    result: Result<(Val<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    _: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceResultQueue<B>,
) {
    match result {
        Ok((Val::Bool(result), _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, result, events.drain(..).cloned().collect())))
        }
        Ok((val, _)) => collected.push(Err(format!("Unexpected footprint return value: {:?}", val))),
        Err((ExecError::Dead, _)) => (),
        Err((err, _)) => collected.push(Err(format!("Error {:?}", err))),
    }
}

pub fn footprint_collector<'ir, B: BV>(
    _: usize,
    task_id: usize,
    result: Result<(Val<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    _: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    match result {
        // Footprint function returns true on traces we need to consider as part of the footprint
        Ok((Val::Bool(true), _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, events.drain(..).cloned().collect())))
        }
        // If it returns false or unit, we ignore that trace
        Ok((Val::Bool(false), _)) => (),
        // Anything else is an error!
        Ok((val, _)) => collected.push(Err(format!("Unexpected footprint return value: {:?}", val))),

        Err((ExecError::Dead, _)) => (),
        Err((err, _)) => collected.push(Err(format!("Error {:?}", err))),
    }
}
