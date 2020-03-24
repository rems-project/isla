// MIT License
//
// Copyright (c) 2019 Alasdair Armstrong
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! This module implements the core of the symbolic execution engine.

use crossbeam::deque::{Injector, Steal, Stealer, Worker};
use crossbeam::queue::SegQueue;
use crossbeam::thread;
use std::collections::HashMap;
use std::mem;
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Mutex, RwLock};
use std::thread::sleep;
use std::time::{Duration, Instant};

use crate::concrete::BV;
use crate::error::ExecError;
use crate::ir::*;
use crate::log;
use crate::memory::Memory;
use crate::primop;
use crate::probe;
use crate::smt::*;
use crate::zencode;

/// Create a Symbolic value of a specified type. Can return a concrete value if the type only
/// permits a single value, such as for the unit type or the zero-length bitvector type (which is
/// ideal because SMT solvers don't allow zero-length bitvectors). Compound types like structs will
/// be a concrete structure with symbolic values for each field. Returns the `NoSymbolicType` error
/// if the type cannot be represented in the SMT solver.
fn symbolic<B: BV>(ty: &Ty<Name>, shared_state: &SharedState<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let smt_ty = match ty {
        Ty::Unit => return Ok(Val::Unit),
        Ty::Bits(0) => return Ok(Val::Bits(B::zeros(0))),

        Ty::I64 => smtlib::Ty::BitVec(64),
        Ty::I128 => smtlib::Ty::BitVec(128),
        Ty::Bits(sz) => smtlib::Ty::BitVec(*sz),
        Ty::Bool => smtlib::Ty::Bool,
        Ty::Bit => smtlib::Ty::BitVec(1),

        Ty::Struct(name) => {
            if let Some(field_types) = shared_state.structs.get(name) {
                let field_values: Result<HashMap<Name, Val<B>>, ExecError> = field_types
                    .iter()
                    .map(|(f, ty)| match symbolic(ty, shared_state, solver) {
                        Ok(value) => Ok((*f, value)),
                        Err(error) => Err(error),
                    })
                    .collect();
                return Ok(Val::Struct(field_values?));
            } else {
                let name = zencode::decode(shared_state.symtab.to_str(*name));
                return Err(ExecError::Unreachable(format!("Struct {} does not appear to exist!", name)));
            }
        }

        Ty::Enum(name) => {
            use crate::smt::smtlib::*;
            let enum_size = shared_state.enums.get(name).unwrap().len();
            let enum_id = solver.get_enum(enum_size);
            let sym = solver.fresh();
            solver.add(Def::DeclareConst(sym, Ty::Enum(enum_id)));
            return Ok(Val::Symbolic(sym));
        }

        Ty::FixedVector(sz, ty) => {
            let values: Result<Vec<Val<B>>, ExecError> = (0..*sz).map(|_| symbolic(ty, shared_state, solver)).collect();
            return Ok(Val::Vector(values?));
        }

        // Some things we just can't represent symbolically, but we can continue in the hope that
        // they never actually get used.
        _ => return Ok(Val::Poison),
    };

    let sym = solver.fresh();
    solver.add(smtlib::Def::DeclareConst(sym, smt_ty));
    Ok(Val::Symbolic(sym))
}

#[derive(Clone)]
struct LocalState<'ir, B> {
    vars: Bindings<'ir, B>,
    regs: Bindings<'ir, B>,
    lets: Bindings<'ir, B>,
}

/// Gets a value from a HashMap. Note that this function is set up to handle the following case:
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
fn get_and_initialize<'ir, B: BV>(
    v: Name,
    vars: &mut Bindings<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<Option<Val<B>>, ExecError> {
    Ok(match vars.get(&v) {
        Some(UVal::Uninit(ty)) => {
            let sym = symbolic(ty, shared_state, solver)?;
            vars.insert(v, UVal::Init(sym.clone()));
            Some(sym)
        }
        Some(UVal::Init(value)) => Some(value.clone()),
        None => None,
    })
}

fn get_id_and_initialize<'ir, B: BV>(
    id: Name,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
) -> Result<Val<B>, ExecError> {
    Ok(match get_and_initialize(id, &mut local_state.vars, shared_state, solver)? {
        Some(value) => value,
        None => match get_and_initialize(id, &mut local_state.regs, shared_state, solver)? {
            Some(value) => {
                let symbol = zencode::decode(shared_state.symtab.to_str(id));
                // HACK: Don't store the entire TLB in the trace
                if symbol != "_TLB" {
                    log!(log::VERBOSE, &format!("Reading register: {} {:?}", symbol, value));
                    solver.add_event(Event::ReadReg(id, accessor.to_vec(), value.clone()));
                }
                value
            }
            None => match get_and_initialize(id, &mut local_state.lets, shared_state, solver)? {
                Some(value) => value,
                None => match shared_state.enum_members.get(&id) {
                    Some((member, enum_size)) => {
                        let enum_id = solver.get_enum(*enum_size);
                        Val::Enum(EnumMember { enum_id, member: *member })
                    }
                    None => panic!("Symbol {} ({:?}) not found", zencode::decode(shared_state.symtab.to_str(id)), id),
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
) -> Result<Val<B>, ExecError> {
    Ok(match loc {
        Loc::Id(id) => get_id_and_initialize(*id, local_state, shared_state, solver, accessor)?,
        _ => panic!("Cannot get_loc_and_initialize"),
    })
}

fn eval_exp_with_accessor<'ir, B: BV>(
    exp: &Exp<Name>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
) -> Result<Val<B>, ExecError> {
    use Exp::*;
    Ok(match exp {
        Id(id) => get_id_and_initialize(*id, local_state, shared_state, solver, accessor)?,

        I64(i) => Val::I64(*i),
        I128(i) => Val::I128(*i),
        Unit => Val::Unit,
        Bool(b) => Val::Bool(*b),
        Bits(bv) => Val::Bits(B::new(bv.bits, bv.length)),
        String(s) => Val::String(s.clone()),

        Undefined(ty) => symbolic(ty, shared_state, solver)?,

        Call(op, args) => {
            let args: Vec<Val<B>> =
                args.iter().map(|arg| eval_exp(arg, local_state, shared_state, solver)).collect::<Result<_, _>>()?;
            match op {
                Op::Lt => primop::op_lt(args[0].clone(), args[1].clone(), solver)?,
                Op::Gt => primop::op_gt(args[0].clone(), args[1].clone(), solver)?,
                Op::Lteq => primop::op_lteq(args[0].clone(), args[1].clone(), solver)?,
                Op::Gteq => primop::op_gteq(args[0].clone(), args[1].clone(), solver)?,
                Op::Eq => primop::op_eq(args[0].clone(), args[1].clone(), solver)?,
                Op::Neq => primop::op_neq(args[0].clone(), args[1].clone(), solver)?,
                Op::Add => primop::op_add(args[0].clone(), args[1].clone(), solver)?,
                Op::Sub => primop::op_sub(args[0].clone(), args[1].clone(), solver)?,
                Op::Bvnot => primop::not_bits(args[0].clone(), solver)?,
                Op::Bvor => primop::or_bits(args[0].clone(), args[1].clone(), solver)?,
                Op::Bvxor => primop::xor_bits(args[0].clone(), args[1].clone(), solver)?,
                Op::Bvand => primop::and_bits(args[0].clone(), args[1].clone(), solver)?,
                Op::Bvadd => primop::add_bits(args[0].clone(), args[1].clone(), solver)?,
                Op::Bvsub => primop::sub_bits(args[0].clone(), args[1].clone(), solver)?,
                Op::Bvaccess => primop::vector_access(args[0].clone(), args[1].clone(), solver)?,
                Op::Concat => primop::append(args[0].clone(), args[1].clone(), solver)?,
                Op::Not => primop::not_bool(args[0].clone(), solver)?,
                Op::And => primop::and_bool(args[0].clone(), args[1].clone(), solver)?,
                Op::Or => primop::or_bool(args[0].clone(), args[1].clone(), solver)?,
                Op::Slice(len) => primop::op_slice(args[0].clone(), args[1].clone(), *len, solver)?,
                Op::SetSlice => primop::op_set_slice(args[0].clone(), args[1].clone(), args[2].clone(), solver)?,
                Op::Unsigned(_) => primop::op_unsigned(args[0].clone(), solver)?,
                Op::Signed(_) => primop::op_signed(args[0].clone(), solver)?,
                Op::Head => primop::op_head(args[0].clone(), solver)?,
                Op::Tail => primop::op_tail(args[0].clone(), solver)?,
            }
        }

        Kind(ctor_a, exp) => {
            let v = eval_exp(exp, local_state, shared_state, solver)?;
            match v {
                Val::Ctor(ctor_b, _) => Val::Bool(*ctor_a != ctor_b),
                _ => return Err(ExecError::Type("Kind check on non-constructor")),
            }
        }

        Unwrap(ctor_a, exp) => {
            let v = eval_exp(exp, local_state, shared_state, solver)?;
            match v {
                Val::Ctor(ctor_b, v) => {
                    if *ctor_a == ctor_b {
                        *v
                    } else {
                        return Err(ExecError::Type("Constructors did not match in unwrap"));
                    }
                }
                _ => return Err(ExecError::Type("Tried to unwrap non-constructor")),
            }
        }

        Field(exp, field) => {
            accessor.push(Accessor::Field(*field));
            if let Val::Struct(struct_value) = eval_exp_with_accessor(exp, local_state, shared_state, solver, accessor)?
            {
                match struct_value.get(field) {
                    Some(field_value) => field_value.clone(),
                    None => panic!("No field"),
                }
            } else {
                panic!("Struct expression did not evaluate to a struct")
            }
        }

        Ref(reg) => Val::Ref(*reg),

        _ => panic!("Could not evaluate expression {:?}", exp),
    })
}

fn eval_exp<'ir, B: BV>(
    exp: &Exp<Name>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    eval_exp_with_accessor(exp, local_state, shared_state, solver, &mut Vec::new())
}

fn assign_with_accessor<'ir, B: BV>(
    loc: &Loc<Name>,
    v: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    accessor: &mut Vec<Accessor>,
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
                local_state.regs.insert(*id, UVal::Init(v));
            }
        }

        Loc::Field(loc, field) => {
            let mut accessor = Vec::new();
            accessor.push(Accessor::Field(*field));
            if let Val::Struct(field_values) =
                get_loc_and_initialize(loc, local_state, shared_state, solver, &mut accessor)?
            {
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
                            &mut accessor,
                        )?;
                    }
                    None => panic!("Invalid field assignment"),
                }
            } else {
                panic!(
                    "Cannot assign struct to non-struct {:?}.{:?} ({:?})",
                    loc,
                    field,
                    get_loc_and_initialize(loc, local_state, shared_state, solver, &mut accessor)
                )
            }
        }

        Loc::Addr(loc) => {
            if let Val::Ref(reg) = get_loc_and_initialize(loc, local_state, shared_state, solver, accessor)? {
                assign_with_accessor(&Loc::Id(reg), v, local_state, shared_state, solver, accessor)?
            } else {
                panic!("Cannot get address of non-reference {:?}", loc)
            }
        }
    };
    Ok(())
}

fn assign<'ir, B: BV>(
    loc: &Loc<Name>,
    v: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<(), ExecError> {
    assign_with_accessor(loc, v, local_state, shared_state, solver, &mut Vec::new())
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

/// A `Frame` is an immutable snapshot of the program state while it
/// is being symbolically executed.
pub struct Frame<'ir, B> {
    pc: usize,
    forks: u32,
    backjumps: u32,
    local_state: Arc<LocalState<'ir, B>>,
    memory: Arc<Memory<B>>,
    instrs: &'ir [Instr<Name, B>],
    stack_vars: Arc<Vec<Bindings<'ir, B>>>,
    stack_call: Stack<'ir, B>,
}

/// A `LocalFrame` is a mutable frame which is used by a currently
/// executing thread. It is turned into an immutable `Frame` when the
/// control flow forks on a choice, which can be shared by threads.
pub struct LocalFrame<'ir, B> {
    pc: usize,
    forks: u32,
    backjumps: u32,
    local_state: LocalState<'ir, B>,
    memory: Memory<B>,
    instrs: &'ir [Instr<Name, B>],
    stack_vars: Vec<Bindings<'ir, B>>,
    stack_call: Stack<'ir, B>,
}

pub fn unfreeze_frame<'ir, B: BV>(frame: &Frame<'ir, B>) -> LocalFrame<'ir, B> {
    LocalFrame {
        pc: frame.pc,
        forks: frame.forks,
        backjumps: frame.backjumps,
        local_state: (*frame.local_state).clone(),
        memory: (*frame.memory).clone(),
        instrs: frame.instrs,
        stack_vars: (*frame.stack_vars).clone(),
        stack_call: frame.stack_call.clone(),
    }
}

pub fn freeze_frame<'ir, B: BV>(frame: &LocalFrame<'ir, B>) -> Frame<'ir, B> {
    Frame {
        pc: frame.pc,
        forks: frame.forks,
        backjumps: frame.backjumps,
        local_state: Arc::new(frame.local_state.clone()),
        memory: Arc::new(frame.memory.clone()),
        instrs: frame.instrs,
        stack_vars: Arc::new(frame.stack_vars.clone()),
        stack_call: frame.stack_call.clone(),
    }
}

impl<'ir, B: BV> LocalFrame<'ir, B> {
    pub fn vars_mut(&mut self) -> &mut Bindings<'ir, B> {
        &mut self.local_state.vars
    }

    pub fn vars(&self) -> &Bindings<'ir, B> {
        &self.local_state.vars
    }

    pub fn regs_mut(&mut self) -> &mut Bindings<'ir, B> {
        &mut self.local_state.regs
    }

    pub fn regs(&self) -> &Bindings<'ir, B> {
        &self.local_state.regs
    }

    pub fn add_regs(&mut self, regs: &Bindings<'ir, B>) -> &mut Self {
        for (k, v) in regs.iter() {
            self.local_state.regs.insert(*k, v.clone());
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
        for (k, v) in lets.iter() {
            self.local_state.lets.insert(*k, v.clone());
        }
        self
    }

    pub fn get_exception(&self) -> Option<(&Val<B>,&str)> {
        if let Some(UVal::Init(Val::Bool(true))) = self.lets().get(&HAVE_EXCEPTION) {
            if let Some(UVal::Init(val)) = self.lets().get(&CURRENT_EXCEPTION) {
                let loc = match self.lets().get(&THROW_LOCATION) {
                    Some(UVal::Init(Val::String(s))) => s,
                    Some(UVal::Init(_)) => "location has wrong type",
                    _ => "missing location"
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

    pub fn new(args: &[(Name, &'ir Ty<Name>)], vals: Option<&[Val<B>]>, instrs: &'ir [Instr<Name, B>]) -> Self {
        let mut vars = HashMap::new();
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

        let mut lets = HashMap::new();
        lets.insert(HAVE_EXCEPTION, UVal::Init(Val::Bool(false)));
        lets.insert(CURRENT_EXCEPTION, UVal::Uninit(&Ty::Union(SAIL_EXCEPTION)));
        lets.insert(THROW_LOCATION, UVal::Uninit(&Ty::String));
        lets.insert(NULL, UVal::Init(Val::List(Vec::new())));

        let regs = HashMap::new();

        LocalFrame {
            pc: 0,
            forks: 0,
            backjumps: 0,
            local_state: LocalState { vars, regs, lets },
            memory: Memory::new(),
            instrs,
            stack_vars: Vec::new(),
            stack_call: None,
        }
    }

    pub fn new_call(
        &self,
        args: &[(Name, &'ir Ty<Name>)],
        vals: Option<&[Val<B>]>,
        instrs: &'ir [Instr<Name, B>],
    ) -> Self {
        let mut new_frame = LocalFrame::new(args, vals, instrs);
        new_frame.forks = self.forks;
        new_frame.local_state.regs = self.local_state.regs.clone();
        new_frame.local_state.lets = self.local_state.lets.clone();
        new_frame.memory = self.memory.clone();
        new_frame
    }

    pub fn task_with_checkpoint(&self, task_id: usize, checkpoint: Checkpoint<B>) -> Task<'ir, B> {
        Task { id: task_id, frame: freeze_frame(&self), checkpoint, fork_cond: None }
    }
    pub fn task(&self, task_id: usize) -> Task<'ir, B> {
        self.task_with_checkpoint(task_id, Checkpoint::new())
    }
}

fn push_call_stack<'ir, B: BV>(frame: &mut LocalFrame<'ir, B>) {
    let mut vars = Box::new(HashMap::new());
    mem::swap(&mut *vars, frame.vars_mut());
    frame.stack_vars.push(*vars)
}

fn pop_call_stack<'ir, B: BV>(frame: &mut LocalFrame<'ir, B>) {
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

fn run<'ir, B: BV>(
    tid: usize,
    task_id: usize,
    timeout: Timeout,
    queue: &Worker<Task<'ir, B>>,
    frame: &Frame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<(Val<B>, LocalFrame<'ir, B>), ExecError> {
    let mut frame = unfreeze_frame(frame);
    loop {
        if frame.pc >= frame.instrs.len() {
            // Currently this happens when evaluating letbindings.
            log_from!(tid, log::VERBOSE, "Fell from end of instruction list");
            return Ok((Val::Unit, frame));
        }

        if timeout.timed_out() {
            return Err(ExecError::Timeout);
        }

        match &frame.instrs[frame.pc] {
            Instr::Decl(v, ty) => {
                //let symbol = zencode::decode(shared_state.symtab.to_str(*v));
                //log_from!(tid, log::VERBOSE, &format!("{}", symbol));
                frame.vars_mut().insert(*v, UVal::Uninit(ty));
                frame.pc += 1;
            }

            Instr::Init(var, _, exp) => {
                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver)?;
                frame.vars_mut().insert(*var, UVal::Init(value));
                frame.pc += 1;
            }

            Instr::Jump(exp, target, loc) => {
                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver)?;
                match value {
                    Val::Symbolic(v) => {
                        use smtlib::Def::*;
                        use smtlib::Exp::*;

                        let test_true = Var(v);
                        let test_false = Not(Box::new(Var(v)));
                        let can_be_true = solver.check_sat_with(&test_true).is_sat()?;
                        let can_be_false = solver.check_sat_with(&test_false).is_sat()?;

                        if can_be_true && can_be_false {
                            // Trace which asserts are assocated with each fork in the trace, so we
                            // can turn a set of traces into a tree later
                            log_from!(tid, log::FORK, loc);
                            solver.add_event(Event::Fork(frame.forks, v, loc.clone()));
                            frame.forks += 1;

                            let point = checkpoint(solver);
                            let frozen = Frame { pc: frame.pc + 1, ..freeze_frame(&frame) };
                            queue.push(Task {
                                id: task_id,
                                frame: frozen,
                                checkpoint: point,
                                fork_cond: Some(Assert(test_false)),
                            });
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
                        return Err(ExecError::Type("Jump on non boolean"));
                    }
                }
            }

            Instr::Goto(target) => frame.pc = *target,

            Instr::Copy(loc, exp) => {
                let value = eval_exp(exp, &mut frame.local_state, shared_state, solver)?;
                assign(loc, value, &mut frame.local_state, shared_state, solver)?;
                frame.pc += 1;
            }

            Instr::PrimopUnary(loc, f, arg) => {
                let arg = eval_exp(arg, &mut frame.local_state, shared_state, solver)?;
                let value = f(arg, solver)?;
                assign(loc, value, &mut frame.local_state, shared_state, solver)?;
                frame.pc += 1;
            }

            Instr::PrimopBinary(loc, f, arg1, arg2) => {
                let arg1 = eval_exp(arg1, &mut frame.local_state, shared_state, solver)?;
                let arg2 = eval_exp(arg2, &mut frame.local_state, shared_state, solver)?;
                let value = f(arg1, arg2, solver)?;
                assign(loc, value, &mut frame.local_state, shared_state, solver)?;
                frame.pc += 1;
            }

            Instr::PrimopVariadic(loc, f, args) => {
                let args = args
                    .iter()
                    .map(|arg| eval_exp(arg, &mut frame.local_state, shared_state, solver))
                    .collect::<Result<_, _>>()?;
                let value = f(args, solver, &mut frame)?;
                assign(loc, value, &mut frame.local_state, shared_state, solver)?;
                frame.pc += 1;
            }

            Instr::Call(loc, _, f, args) => {
                match shared_state.functions.get(&f) {
                    None => {
                        if *f == INTERNAL_VECTOR_INIT && args.len() == 1 {
                            let arg = eval_exp(&args[0], &mut frame.local_state, shared_state, solver)?;
                            match loc {
                                Loc::Id(v) => match (arg, frame.vars().get(v)) {
                                    (Val::I64(len), Some(UVal::Uninit(Ty::Vector(_)))) => assign(
                                        loc,
                                        Val::Vector(vec![Val::Poison; len as usize]),
                                        &mut frame.local_state,
                                        shared_state,
                                        solver,
                                    )?,
                                    _ => return Err(ExecError::Type("internal_vector_init")),
                                },
                                _ => return Err(ExecError::Type("internal_vector_init")),
                            };
                            frame.pc += 1
                        } else if *f == INTERNAL_VECTOR_UPDATE {
                            frame.pc += 1
                        } else if *f == SAIL_EXIT {
                            return Err(ExecError::Exit);
                        } else if *f == REG_DEREF && args.len() == 1 {
                            if let Val::Ref(reg) = eval_exp(&args[0], &mut frame.local_state, shared_state, solver)? {
                                match get_and_initialize(reg, frame.regs_mut(), shared_state, solver)? {
                                    Some(value) => {
                                        solver.add_event(Event::ReadReg(reg, Vec::new(), value.clone()));
                                        assign(loc, value, &mut frame.local_state, shared_state, solver)?
                                    }
                                    None => return Err(ExecError::Type("reg_deref")),
                                }
                            } else {
                                return Err(ExecError::Type("reg_deref (not a register)"));
                            };
                            frame.pc += 1
                        } else if shared_state.union_ctors.contains(f) {
                            assert!(args.len() == 1);
                            let arg = eval_exp(&args[0], &mut frame.local_state, shared_state, solver)?;
                            assign(loc, Val::Ctor(*f, Box::new(arg)), &mut frame.local_state, shared_state, solver)?;
                            frame.pc += 1
                        } else {
                            let symbol = zencode::decode(shared_state.symtab.to_str(*f));
                            panic!("Attempted to call non-existent function {} ({:?})", symbol, *f)
                        }
                    }

                    Some((params, _, instrs)) => {
                        let mut args = args
                            .iter()
                            .map(|arg| eval_exp(arg, &mut frame.local_state, shared_state, solver))
                            .collect::<Result<Vec<Val<B>>, _>>()?;

                        if shared_state.probes.contains(f) {
                            let symbol = zencode::decode(shared_state.symtab.to_str(*f));
                            log_from!(tid, log::PROBE, &format!("Calling {}[{:?}]({:?})", symbol, f, &args));
                            probe::args_info(tid, &args, shared_state, solver)
                        }

                        let caller_pc = frame.pc;
                        let caller_instrs = frame.instrs;
                        let caller_stack_call = frame.stack_call.clone();
                        push_call_stack(&mut frame);

                        // Set up a closure to restore our state when
                        // the function we call returns
                        frame.stack_call = Some(Arc::new(move |ret, frame, shared_state, solver| {
                            pop_call_stack(frame);
                            frame.pc = caller_pc + 1;
                            frame.instrs = caller_instrs;
                            frame.stack_call = caller_stack_call.clone();
                            assign(&loc.clone(), ret, &mut frame.local_state, shared_state, solver)
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
                        UVal::Uninit(ty) => symbolic(ty, shared_state, solver)?,
                        UVal::Init(value) => value.clone(),
                    };
                    let caller = match &frame.stack_call {
                        None => return Ok((value, frame)),
                        Some(caller) => Arc::clone(caller),
                    };
                    (*caller)(value, &mut frame, shared_state, solver)?
                }
            },

            // The idea beind the Monomorphize operation is it takes a
            // bitvector identifier, and if that identifer has a
            // symbolic value, then it uses the SMT solver to find all
            // the possible values for that bitvector and case splits
            // (i.e. forks) on them. This allows us to guarantee that
            // certain bitvectors are non-symbolic, at the cost of
            // increasing the number of paths.
            Instr::Monomorphize(id) => {
                let val = get_id_and_initialize(*id, &mut frame.local_state, shared_state, solver, &mut Vec::new())?;
                if let Val::Symbolic(v) = val {
                    use smtlib::Def::*;
                    use smtlib::Exp::*;
                    use smtlib::Ty::*;

                    let point = checkpoint(solver);

                    let len = solver.length(v).ok_or_else(|| ExecError::Type("_monomorphize"))?;

                    // For the variable v to appear in the model, there must be some assertion that references it
                    let sym = solver.fresh();
                    solver.add(DeclareConst(sym, BitVec(len)));
                    solver.add(Assert(Eq(Box::new(Var(v)), Box::new(Var(sym)))));

                    if solver.check_sat().is_unsat()? {
                        return Err(ExecError::Dead);
                    }

                    let (result, size) = {
                        let mut model = Model::new(solver);
                        log_from!(tid, log::FORK, format!("Model: {:?}", model));
                        match model.get_bv_var(v) {
                            Ok(Some(Bits64(result, size))) => (result, size),
                            // __monomorphize should have a 'n <= 64 constraint in Sail
                            Ok(Some(_)) => return Err(ExecError::Type("__monomorphize")),
                            Ok(None) => return Err(ExecError::Z3Error(format!("No value for variable v{}", v))),
                            Err(error) => return Err(error),
                        }
                    };

                    let loc = format!("Fork @ monomorphizing v{}", v);
                    log_from!(tid, log::FORK, loc);
                    solver.add_event(Event::Fork(frame.forks, v, loc.clone()));
                    frame.forks += 1;

                    queue.push(Task {
                        id: task_id,
                        frame: freeze_frame(&frame),
                        checkpoint: point,
                        fork_cond: Some(Assert(Neq(Box::new(Var(v)), Box::new(Bits64(result, size))))),
                    });

                    assign(
                        &Loc::Id(*id),
                        Val::Bits(B::new(result, size)),
                        &mut frame.local_state,
                        shared_state,
                        solver,
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
                let caller = match &frame.stack_call {
                    None => return Ok((Val::Poison, frame)),
                    Some(caller) => Arc::clone(caller),
                };
                (*caller)(Val::Poison, &mut frame, shared_state, solver)?
            }

            Instr::Failure => return Err(ExecError::MatchFailure),
        }
    }
}

/// A collector is run on the result of each path found via symbolic execution through the code. It
/// takes the result of the execution, which is either a combination of the return value and local
/// state at the end of the execution or an error, as well as the shared state and the SMT solver
/// state associated with that execution. It build a final result for all the executions by
/// collecting the results into a type R, protected by a lock.
pub type Collector<'ir, B, R> = dyn 'ir
    + Sync
    + Fn(usize, usize, Result<(Val<B>, LocalFrame<'ir, B>), ExecError>, &SharedState<'ir, B>, Solver<B>, &R) -> ();

/// A `Task` is a suspended point in the symbolic execution of a
/// program. It consists of a frame, which is a snapshot of the
/// program variables, a checkpoint which allows us to reconstruct the
/// SMT solver state, and finally an option SMTLIB definiton which is
/// added to the solver state when the task is resumed.
pub struct Task<'ir, B> {
    id: usize,
    frame: Frame<'ir, B>,
    checkpoint: Checkpoint<B>,
    fork_cond: Option<smtlib::Def>,
}

/// Start symbolically executing a Task using just the current thread, collecting the results using
/// the given collector.
pub fn start_single<'ir, B: BV, R>(
    task: Task<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) {
    let queue = Worker::new_lifo();
    queue.push(task);
    while let Some(task) = queue.pop() {
        let cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
        if let Some(def) = task.fork_cond {
            solver.add(def)
        };
        let result = run(0, task.id, Timeout::unlimited(), &queue, &task.frame, shared_state, &mut solver);
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

fn do_work<'ir, B: BV, R>(
    tid: usize,
    timeout: Timeout,
    queue: &Worker<Task<'ir, B>>,
    task: Task<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) {
    let cfg = Config::new();
    let ctx = Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
    if let Some(def) = task.fork_cond {
        solver.add(def)
    };
    let result = run(tid, task.id, timeout, queue, &task.frame, shared_state, &mut solver);
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
pub fn start_multi<'ir, B: BV, R>(
    num_threads: usize,
    timeout: Option<u64>,
    tasks: Vec<Task<'ir, B>>,
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
            // then 'poke' it to wait it up via a channel, which will cause the worker to try to
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
                        log_from!(tid, log::VERBOSE, "Working");
                        thread_tx.send(Activity::Busy(tid)).unwrap();
                        do_work(tid, timeout, &q, task, &shared_state, collected.as_ref(), collector);
                        while let Some(task) = find_task(&q, &global, &stealers) {
                            do_work(tid, timeout, &q, task, &shared_state, collected.as_ref(), collector)
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
/// true via the mutex if all reachable paths through the program are
/// unsatisfiable, which implies that the function always returns
/// true.
pub fn all_unsat_collector<'ir, B: BV>(
    tid: usize,
    _: usize,
    result: Result<(Val<B>, LocalFrame<'ir, B>), ExecError>,
    _: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &Mutex<bool>,
) {
    match result {
        Ok(value) => match value {
            (Val::Symbolic(v), _) => {
                use smtlib::Def::*;
                use smtlib::Exp::*;
                solver.add(Assert(Not(Box::new(Var(v)))));
                if solver.check_sat() != SmtResult::Unsat {
                    log_from!(tid, log::VERBOSE, "Got sat");
                    let mut b = collected.lock().unwrap();
                    *b &= false
                } else {
                    log_from!(tid, log::VERBOSE, "Got unsat")
                }
            }
            (Val::Bool(true), _) => log_from!(tid, log::VERBOSE, "Got true"),
            (Val::Bool(false), _) => {
                log_from!(tid, log::VERBOSE, "Got false");
                let mut b = collected.lock().unwrap();
                *b &= false
            }
            (value, _) => log_from!(tid, log::VERBOSE, &format!("Got value {:?}", value)),
        },
        Err(err) => match err {
            ExecError::Dead => log_from!(tid, log::VERBOSE, "Dead"),
            _ => {
                log_from!(tid, log::VERBOSE, &format!("Got error, {:?}", err));
                let mut b = collected.lock().unwrap();
                *b &= false
            }
        },
    }
}

pub type TraceQueue<B> = SegQueue<Result<(usize, Vec<Event<B>>), String>>;

pub type TraceResultQueue<B> = SegQueue<Result<(usize, bool, Vec<Event<B>>), String>>;

pub fn trace_collector<'ir, B: BV>(
    _: usize,
    task_id: usize,
    result: Result<(Val<B>, LocalFrame<'ir, B>), ExecError>,
    _: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    use crate::simplify::simplify;

    match result {
        Ok(_) | Err(ExecError::Exit) => {
            let mut events = simplify(solver.trace());
            collected.push(Ok((task_id, events.drain(..).map({ |ev| ev.clone() }).collect())))
        }
        Err(ExecError::Dead) => (),
        Err(err) => collected.push(Err(format!("Error {:?}", err))),
    }
}

pub fn trace_result_collector<'ir, B: BV>(
    _: usize,
    task_id: usize,
    result: Result<(Val<B>, LocalFrame<'ir, B>), ExecError>,
    _: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceResultQueue<B>,
) {
    use crate::simplify::simplify;

    match result {
        Ok((Val::Bool(result), _)) => {
            let mut events = simplify(solver.trace());
            collected.push(Ok((task_id, result, events.drain(..).map({ |ev| ev.clone() }).collect())))
        }
        Ok((val, _)) => collected.push(Err(format!("Unexpected footprint return value: {:?}", val))),
        Err(ExecError::Dead) => (),
        Err(err) => collected.push(Err(format!("Error {:?}", err))),
    }
}

pub fn footprint_collector<'ir, B: BV>(
    _: usize,
    task_id: usize,
    result: Result<(Val<B>, LocalFrame<'ir, B>), ExecError>,
    _: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    use crate::simplify::simplify;

    match result {
        // Footprint function returns true on traces we need to consider as part of the footprint
        Ok((Val::Bool(true), _)) => {
            let mut events = simplify(solver.trace());
            collected.push(Ok((task_id, events.drain(..).map({ |ev| ev.clone() }).collect())))
        }
        // If it returns false or unit, we ignore that trace
        Ok((Val::Bool(false), _)) => (),
        // Anything else is an error!
        Ok((val, _)) => collected.push(Err(format!("Unexpected footprint return value: {:?}", val))),

        Err(ExecError::Dead) => (),
        Err(err) => collected.push(Err(format!("Error {:?}", err))),
    }
}
