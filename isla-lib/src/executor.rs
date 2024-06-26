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
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, RwLock};
use std::thread;
use std::time::{Duration, Instant};

use crate::bitvector::{b64::B64, required_index_bits, BV};
use crate::error::{ExecError, IslaError};
use crate::fraction::Fraction;
use crate::ir::*;
use crate::log;
use crate::primop;
use crate::primop_util::{build_ite, ite_phi, smt_value, symbolic};
use crate::probe;
use crate::smt::smtlib::Def;
use crate::smt::*;
use crate::source_loc::SourceLoc;
use crate::zencode;

mod frame;
mod task;

pub use frame::{freeze_frame, unfreeze_frame, Backtrace, Frame, LocalFrame, LocalState};
use frame::{pop_call_stack, push_call_stack};
pub use task::{StopAction, StopConditions, Task, TaskId, TaskInterrupt, TaskState};

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
    accessor: &mut [Accessor],
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
                None => match shared_state.type_info.enum_members.get(&id) {
                    Some((member, enum_size, enum_id)) => {
                        let enum_id = solver.get_enum(*enum_id, *enum_size);
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

enum RegisterVectorIndex {
    ConcreteIndex(usize),
    SymbolicIndex(Sym),
}

fn fix_index_length<B: BV>(i: Sym, from: u32, to: u32, solver: &mut Solver<B>, info: SourceLoc) -> Sym {
    use smtlib::Exp::*;
    if from == to {
        i
    } else if from > to {
        solver.define_const(Extract(to - 1, 0, Box::new(Var(i))), info)
    } else {
        solver.define_const(ZeroExtend(to - from, Box::new(Var(i))), info)
    }
}

fn read_register_from_vector<'ir, B: BV>(
    n: Val<B>,
    regs_vector: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    use smtlib::Exp::*;
    use RegisterVectorIndex::*;

    let bad_regs_argument = "read_register_from_vector must be given a vector of register references";
    let regs: Vec<Name> = match &regs_vector {
        Val::Vector(regs) => {
            regs.iter()
                .map(|r| {
                    if let Val::Ref(r) = r {
                        Ok(*r)
                    } else {
                        Err(ExecError::Type(bad_regs_argument.to_string(), info))
                    }
                })
                .collect::<Result<_, _>>()?
        }
        _ => return Err(ExecError::Type(bad_regs_argument.to_string(), info)),
    };
    let rib = required_index_bits(regs.len());

    let invalid_index_argument = "read_register_from_vector invalid index";
    let index = match n {
        Val::Bits(bv) => ConcreteIndex(bv.lower_u64() as usize),
        Val::I64(n) => {
            ConcreteIndex(n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?)
        }
        Val::I128(n) => {
            ConcreteIndex(n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?)
        }
        Val::Symbolic(v) => {
            if let Some(len) = solver.length(v) {
                let v = fix_index_length(v, len, rib, solver, info);
                SymbolicIndex(v)
            } else {
                return Err(ExecError::Type(
                    "read_register_from_vector could not determine length of index bitvector".to_string(),
                    info,
                ));
            }
        }
        _ => return Err(ExecError::Type("read_register_from_vector index type must be a bitvector".to_string(), info)),
    };

    match index {
        ConcreteIndex(i) => {
            // This unwrap should be same as all register references must point to value registers
            let value = local_state.regs.get(regs[i], shared_state, solver, info)?.unwrap();
            solver.add_event(Event::ReadReg(regs[i], Vec::new(), value.clone()));
            Ok(value.clone())
        }
        SymbolicIndex(i) => {
            // See above case for unwrap safety
            let mut chain = local_state.regs.get(regs[0], shared_state, solver, info)?.unwrap().clone();
            let mut reg_values = vec![chain.clone()];
            for (j, reg) in regs[1..].iter().enumerate() {
                let choice = solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                    solver.define_const(Eq(Box::new(Var(i)), Box::new(Bits64(B64::new((j + 1) as u64, rib)))), info)
                });
                let value = local_state.regs.get(*reg, shared_state, solver, info)?.unwrap();
                reg_values.push(value.clone());
                chain = solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                    build_ite(choice, value, &chain, solver, info)
                })?
            }
            solver.add_event(Event::Abstract {
                name: READ_REGISTER_FROM_VECTOR,
                primitive: true,
                args: vec![n, regs_vector, Val::Vector(reg_values)],
                return_value: chain.clone(),
            });
            Ok(chain)
        }
    }
}

fn write_register_from_vector<'ir, B: BV>(
    n: Val<B>,
    value: Val<B>,
    regs_vector: Val<B>,
    local_state: &mut LocalState<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    use smtlib::Exp::*;
    use RegisterVectorIndex::*;

    let bad_regs_argument = "write_register_from_vector must be given a vector of register references";
    let regs: Vec<Name> = match &regs_vector {
        Val::Vector(regs) => {
            regs.iter()
                .map(|r| {
                    if let Val::Ref(r) = r {
                        Ok(*r)
                    } else {
                        Err(ExecError::Type(bad_regs_argument.to_string(), info))
                    }
                })
                .collect::<Result<_, _>>()?
        }
        _ => return Err(ExecError::Type(bad_regs_argument.to_string(), info)),
    };
    let rib = required_index_bits(regs.len());

    let invalid_index_argument = "write_register_from_vector invalid index";
    let index = match n {
        Val::Bits(bv) => ConcreteIndex(bv.lower_u64() as usize),
        Val::I64(n) => {
            ConcreteIndex(n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?)
        }
        Val::I128(n) => {
            ConcreteIndex(n.try_into().map_err(|_| ExecError::Type(invalid_index_argument.to_string(), info))?)
        }
        Val::Symbolic(v) => {
            if let Some(len) = solver.length(v) {
                let v = fix_index_length(v, len, rib, solver, info);
                SymbolicIndex(v)
            } else {
                return Err(ExecError::Type(
                    "write_register_from_vector could not determine length of index bitvector".to_string(),
                    info,
                ));
            }
        }
        _ => {
            return Err(ExecError::Type("write_register_from_vector index type must be a bitvector".to_string(), info))
        }
    };

    match index {
        ConcreteIndex(i) => {
            // This unwrap should be same as all register references must point to value registers
            local_state.regs.assign(regs[i], value.clone(), shared_state);
            solver.add_event(Event::WriteReg(regs[i], Vec::new(), value))
        }
        SymbolicIndex(i) => {
            let mut reg_values = Vec::new();
            for (j, reg) in regs.iter().enumerate() {
                solver.set_def_attrs(DefAttrs::uninteresting());
                let choice = solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                    solver.define_const(Eq(Box::new(Var(i)), Box::new(Bits64(B64::new(j as u64, rib)))), info)
                });
                let current_value = local_state.regs.get(*reg, shared_state, solver, info)?.unwrap().clone();
                local_state.regs.assign(
                    *reg,
                    solver.with_def_attrs(DefAttrs::uninteresting(), |solver| {
                        build_ite(choice, &value, &current_value, solver, info)
                    })?,
                    shared_state,
                );
                reg_values.push(current_value);
            }
            solver.add_event(Event::Abstract {
                name: WRITE_REGISTER_FROM_VECTOR,
                primitive: true,
                args: vec![n, value, regs_vector, Val::Vector(reg_values)],
                return_value: Val::Unit,
            })
        }
    }

    Ok(())
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
                Op::IsEmpty => primop::op_is_empty(args[0].clone(), solver, info)?,
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

                non_struct => {
                    return Err(ExecError::Type(
                        format!(
                            "When accessing field {} struct expression {:?} did not evaluate to a struct, instead {}",
                            shared_state.symtab.to_str(*field),
                            exp,
                            non_struct.as_ref().to_string(shared_state)
                        ),
                        info,
                    ))
                }
            }
        }

        Ref(reg) => Owned(Val::Ref(*reg)),

        Struct(_, exp_fields) => {
            let mut val_fields = HashMap::default();
            for (id, exp) in exp_fields {
                let v = eval_exp(exp, local_state, shared_state, solver, info)?.into_owned();
                val_fields.insert(*id, v);
            }
            Owned(Val::Struct(val_fields))
        }
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
            if local_state.vars.contains_key(id) {
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
    if local_state.should_probe(shared_state, &id) {
        log_from!(
            tid,
            log::PROBE,
            &format!(
                "Assigning {}[{:?}] <- {:?} at {}",
                loc_string(loc, &shared_state.symtab),
                id,
                v,
                info.location_string(shared_state.symtab.files())
            )
        )
    }

    assign_with_accessor(loc, v, local_state, shared_state, solver, &mut Vec::new(), info)
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

fn smt_exp_to_value<B: BV>(exp: smtlib::Exp<Sym>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    use smtlib::Exp;
    let v = match exp {
        Exp::Var(v) => Val::Symbolic(v),
        Exp::Bits64(b) => Val::Bits(B::new(b.lower_u64(), b.len())),
        Exp::Enum(m) => Val::Enum(m),
        Exp::Bool(b) => Val::Bool(b),
        _ => {
            // TODO: other sources?
            let v = solver.define_const(exp, SourceLoc::command_line());
            Val::Symbolic(v)
        }
    };
    Ok(v)
}

pub fn interrupt_pending<'ir, B: BV>(
    tid: usize,
    task_id: TaskId,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<bool, ExecError> {
    for interrupt in &task_state.interrupts {
        let Some(Val::Bits(reg_value)) =
            frame.local_state.regs.get(interrupt.trigger_register, shared_state, solver, info)?
        else {
            return Err(ExecError::BadInterrupt(
                "trigger register does not exist, or does not have a concrete bitvector value",
            ));
        };

        if *reg_value == interrupt.trigger_value {
            for (taken_task_id, taken_interrupt_id) in frame.taken_interrupts.iter().cloned() {
                if task_id == taken_task_id && interrupt.id == taken_interrupt_id {
                    return Ok(false);
                }
            }

            frame.taken_interrupts.push((task_id, interrupt.id));

            log_from!(tid, log::VERBOSE, "Injecting pending interrupt");
            for (loc, reset) in &interrupt.reset {
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
                solver.add_event(Event::AssumeReg(loc.id(), accessor, value));
            }

            return Ok(true);
        }
    }

    // No interrupts were pending
    Ok(false)
}

pub fn reset_registers<'ir, B: BV>(
    _tid: usize,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &TaskState<B>,
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
            let reg_id = loc.id();
            frame.local_state.regs.synchronize_register(reg_id);
            // Note that these are just the assumptions from reset_registers; there
            // may also be assumptions from default register values, recorded at the
            // top level.
            solver.add_event(Event::AssumeReg(reg_id, accessor, value));
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
        if solver.check_sat(info).is_unsat()? {
            return Err(ExecError::InconsistentRegisterReset);
        }
    }
    // The arguments and result of any function assumptions are
    // evaluated now so that they can refer to register values in the
    // prestate of an instruction.
    for (f, args, result) in &shared_state.function_assumptions {
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
        let smt_args: Result<Vec<Option<smtlib::Exp<Sym>>>, _> = args
            .iter()
            .map(|e| match e {
                None => Ok(None),
                Some(e) => e.map_var(&mut lookup).map(Some).map_err(ExecError::Unreachable),
            })
            .collect();
        let smt_result: smtlib::Exp<Sym> = result.map_var(&mut lookup).map_err(ExecError::Unreachable)?;
        let val_args: Result<Vec<Val<B>>, _> = smt_args?
            .drain(..)
            .map(|e| match e {
                None => Ok(Val::Unit),
                Some(e) => smt_exp_to_value(e, solver),
            })
            .collect();
        let val_args = val_args?;
        let val_result = smt_exp_to_value(smt_result, solver)?;
        let f_name = shared_state.symtab.lookup(f);
        solver.add_event(Event::AssumeFun { name: f_name, args: val_args.clone(), return_value: val_result.clone() });
        let asms = frame.function_assumptions.entry(f_name).or_default();
        asms.push((val_args, val_result));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn run<'ir, 'task, B: BV>(
    tid: usize,
    task_id: TaskId,
    task_fraction: &mut Fraction,
    timeout: Timeout,
    stop_conditions: Option<&'task StopConditions>,
    queue: &Worker<Task<'ir, 'task, B>>,
    frame: &Frame<'ir, B>,
    task_state: &'task TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)> {
    let mut frame = unfreeze_frame(frame);
    match run_loop(
        tid,
        task_id,
        task_fraction,
        timeout,
        stop_conditions,
        queue,
        &mut frame,
        task_state,
        shared_state,
        solver,
    ) {
        Ok(run) => Ok((run, frame)),
        Err(err) => {
            frame.backtrace.push((frame.function_name, frame.pc));
            Err((err, frame.backtrace))
        }
    }
}

// A special primitive can either continue execution, or it can exit
enum SpecialResult {
    Exit,
    Continue,
}

#[allow(clippy::too_many_arguments)]
fn run_special_primop<'ir, B: BV>(
    loc: &Loc<Name>,
    f: Name,
    args: &[Exp<Name>],
    info: SourceLoc,
    tid: usize,
    task_id: TaskId,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<SpecialResult, ExecError> {
    if f == INTERNAL_VECTOR_INIT && args.len() == 1 {
        let arg = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        match loc {
            Loc::Id(v) => match (arg, frame.vars().get(v)) {
                (Val::I64(len), Some(UVal::Uninit(Ty::Vector(_) | Ty::FixedVector(_, _)))) => assign(
                    tid,
                    loc,
                    Val::Vector(vec![Val::Poison; len as usize]),
                    &mut frame.local_state,
                    shared_state,
                    solver,
                    info,
                )?,
                _ => return Err(ExecError::Type(format!("internal_vector_init {:?}", &loc), info)),
            },
            _ => return Err(ExecError::Type(format!("internal_vector_init {:?}", &loc), info)),
        };
        frame.pc += 1
    } else if f == INTERNAL_VECTOR_UPDATE && args.len() == 3 {
        let args = args
            .iter()
            .map(|arg| eval_exp(arg, &mut frame.local_state, shared_state, solver, info).map(Cow::into_owned))
            .collect::<Result<Vec<Val<B>>, _>>()?;
        let vector = primop::vector_update(args, solver, frame, info)?;
        assign(tid, loc, vector, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == RESET_REGISTERS {
        reset_registers(tid, frame, task_state, shared_state, solver, info)?;
        frame.regs_mut().synchronize();
        assign(tid, loc, Val::Unit, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == INTERRUPT_PENDING {
        let pending = interrupt_pending(tid, task_id, frame, task_state, shared_state, solver, info)?;
        assign(tid, loc, Val::Bool(pending), &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == ITE_PHI {
        let mut true_value = None;
        let mut symbolics = Vec::new();
        for cond in args.chunks_exact(2) {
            let cond_var = match eval_exp(&cond[0], &mut frame.local_state, shared_state, solver, info) {
                Ok(cond_var) => cond_var.into_owned(),
                // A variable not found error indicates that the block associated with this condition variable
                // has not been executed
                Err(ExecError::VariableNotFound(_)) => Val::Bool(false),
                Err(err) => return Err(err),
            };
            match cond_var {
                Val::Bool(true) => {
                    true_value =
                        Some(eval_exp(&cond[1], &mut frame.local_state, shared_state, solver, info)?.into_owned())
                }
                Val::Bool(false) => (),
                Val::Symbolic(sym) => symbolics.push((sym, &cond[1])),
                _ => return Err(ExecError::Type("ite_phi".to_string(), info)),
            }
        }
        if let Some(true_value) = true_value {
            assign(tid, loc, true_value, &mut frame.local_state, shared_state, solver, info)?
        } else {
            let symbolics = symbolics
                .iter()
                .map(|(sym, arg)| {
                    Ok((*sym, eval_exp(arg, &mut frame.local_state, shared_state, solver, info)?.into_owned()))
                })
                .collect::<Result<Vec<(Sym, Val<B>)>, _>>()?;
            let result = ite_phi(&symbolics[0], &symbolics[1..], solver, info)?;
            assign(tid, loc, result, &mut frame.local_state, shared_state, solver, info)?
        }
        frame.pc += 1
    } else if f == REG_DEREF && args.len() == 1 {
        if let Val::Ref(reg) = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned() {
            match frame.regs_mut().get(reg, shared_state, solver, info)? {
                Some(value) => {
                    solver.add_event(Event::ReadReg(reg, Vec::new(), value.clone()));
                    assign(tid, loc, value.clone(), &mut frame.local_state, shared_state, solver, info)?
                }
                None => return Err(ExecError::Type(format!("reg_deref {:?}", &reg), info)),
            }
        } else {
            return Err(ExecError::Type(format!("reg_deref (not a register) {:?}", &f), info));
        };
        frame.pc += 1
    } else if (f == ABSTRACT_CALL || f == ABSTRACT_PRIMOP) && !args.is_empty() {
        let mut args = args
            .iter()
            .map(|arg| eval_exp(arg, &mut frame.local_state, shared_state, solver, info).map(Cow::into_owned))
            .collect::<Result<Vec<Val<B>>, _>>()?;
        let abstracted_fn = match args.pop().unwrap() {
            Val::Ref(f) => f,
            _ => panic!("Invalid abstract call (no function name provided)"),
        };
        let return_ty = if f == ABSTRACT_CALL {
            &shared_state.functions[&abstracted_fn].1
        } else {
            &shared_state.externs[&abstracted_fn].1
        };
        let return_value = symbolic(return_ty, shared_state, solver, info)?;
        solver.add_event(Event::Abstract {
            name: abstracted_fn,
            primitive: f == ABSTRACT_PRIMOP,
            args,
            return_value: return_value.clone(),
        });
        assign(tid, loc, return_value, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == READ_REGISTER_FROM_VECTOR {
        assert!(args.len() == 2);
        let n = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        let regs = eval_exp(&args[1], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        let value = read_register_from_vector(n, regs, &mut frame.local_state, shared_state, solver, info)?;
        assign(tid, loc, value, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == WRITE_REGISTER_FROM_VECTOR {
        assert!(args.len() == 3);
        let n = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        let value = eval_exp(&args[1], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        let regs = eval_exp(&args[2], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        write_register_from_vector(n, value, regs, &mut frame.local_state, shared_state, solver, info)?;
        assign(tid, loc, Val::Unit, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if f == INSTR_ANNOUNCE {
        assert!(args.len() == 1);
        let opcode = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        if let Some((arch_pc, limit)) = task_state.pc_limit {
            if let Some(reg) = frame.local_state.regs.get(arch_pc, shared_state, solver, info)? {
                match reg {
                    Val::Bits(bv) => {
                        let count = frame.pc_counts.entry(*bv).or_insert(0);
                        *count += 1;
                        if *count > limit {
                            return Err(ExecError::PCLimitReached(bv.lower_u64()));
                        }
                    }
                    // We could just do nothing if the program counter register is symbolic?
                    _ => {
                        return Err(ExecError::Type(
                            "Program counter contains non-bitvector or symbolic value".to_string(),
                            info,
                        ))
                    }
                }
            }
        };
        match opcode {
            Val::Bits(bv) if bv.is_zero() && task_state.zero_announce_exit => return Ok(SpecialResult::Exit),
            _ => (),
        };
        solver.add_event(Event::Instr(opcode));
        assign(tid, loc, Val::Unit, &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else if shared_state.type_info.union_ctors.contains(&f) {
        assert!(args.len() == 1);
        let arg = eval_exp(&args[0], &mut frame.local_state, shared_state, solver, info)?.into_owned();
        assign(tid, loc, Val::Ctor(f, Box::new(arg)), &mut frame.local_state, shared_state, solver, info)?;
        frame.pc += 1
    } else {
        let symbol = zencode::decode(shared_state.symtab.to_str(f));
        return Err(ExecError::NoFunction(symbol, info));
    }
    Ok(SpecialResult::Continue)
}

pub enum Run<B> {
    /// Returned when the model finishes executing
    Finished(Val<B>),
    /// `Exit` is used when the Sail 'exit' function is explicitly
    /// called by the model to exit early.
    Exit,
    /// `Dead` means we are in an inconsistent state, where the
    /// run/trace can safely be discarded by the consumer.
    Dead,
    /// `Suspended` is used when the execution has not yet finished,
    /// but control has been returned back to the consumer.
    Suspended,
}

#[allow(clippy::too_many_arguments)]
fn run_loop<'ir, 'task, B: BV>(
    tid: usize,
    task_id: TaskId,
    task_fraction: &mut Fraction,
    timeout: Timeout,
    stop_conditions: Option<&'task StopConditions>,
    queue: &Worker<Task<'ir, 'task, B>>,
    frame: &mut LocalFrame<'ir, B>,
    task_state: &'task TaskState<B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<Run<B>, ExecError> {
    let mut last_z3_reset = Instant::now();

    'main_loop: loop {
        if frame.pc >= frame.instrs.len() {
            // Currently this happens when evaluating letbindings.
            return Ok(Run::Finished(Val::Unit));
        }

        if timeout.timed_out() {
            return Err(ExecError::Timeout);
        }

        if last_z3_reset.elapsed() > Duration::from_millis(500) {
            //let mut vars = HashSet::default();
            //frame.collect_symbolic_variables(&mut vars);
            //solver.reset(vars);
            last_z3_reset = Instant::now()
        };

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

                        let can_be_true = solver.check_sat_with(&test_true, *info).is_sat()?;
                        let can_be_false = solver.check_sat_with(&test_false, *info).is_sat()?;

                        if can_be_true && can_be_false {
                            if_logging!(log::FORK, {
                                log_from!(tid, log::FORK, info.location_string(shared_state.symtab.files()));
                                probe::taint_info(log::FORK, v, Some(shared_state), solver)
                            });

                            let point = checkpoint(solver);
                            let frozen = Frame { pc: frame.pc + 1, ..freeze_frame(frame) };
                            frame.forks += 1;
                            task_fraction.halve();
                            queue.push(Task {
                                id: task_id,
                                fraction: task_fraction.clone(),
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
                            return Ok(Run::Dead);
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

            Instr::PrimopReset(loc, reset, info) => {
                let value = reset(&frame.memory, shared_state.typedefs(), solver)?;
                assign(tid, loc, value, &mut frame.local_state, shared_state, solver, *info)?;
                frame.pc += 1;
            }

            Instr::Call(loc, _, f, args, info) => {
                match shared_state.functions.get(f) {
                    None => {
                        match run_special_primop(
                            loc,
                            *f,
                            args,
                            *info,
                            tid,
                            task_id,
                            frame,
                            task_state,
                            shared_state,
                            solver,
                        )? {
                            SpecialResult::Continue => (),
                            SpecialResult::Exit => return Ok(Run::Exit),
                        }
                    }

                    Some((params, ret_ty, instrs)) => {
                        frame.set_probes(shared_state);

                        let mut args = args
                            .iter()
                            .map(|arg| {
                                eval_exp(arg, &mut frame.local_state, shared_state, solver, *info).map(Cow::into_owned)
                            })
                            .collect::<Result<Vec<Val<B>>, _>>()?;

                        if frame.local_state.should_probe(shared_state, f) {
                            log_from!(tid, log::PROBE, probe::call_info(*f, &args, shared_state, *info));
                            probe::args_info(tid, &args, shared_state, solver)
                        }

                        if shared_state.trace_functions.contains(f) {
                            solver.trace_call(*f)
                        }

                        if let Some(s) = stop_conditions {
                            match s.should_stop(*f, frame.function_name, &frame.backtrace) {
                                Some(StopAction::Kill) => {
                                    let symbol = zencode::decode(shared_state.symtab.to_str(*f));
                                    return Err(ExecError::Stopped(symbol));
                                }
                                Some(StopAction::Abstract) => {
                                    solver.add_event(Event::Abstract {
                                        name: *f,
                                        args,
                                        primitive: false,
                                        return_value: Val::Poison,
                                    });
                                    return Ok(Run::Finished(Val::Poison));
                                }
                                None => (),
                            }
                        }

                        if let Some(assumptions) = frame.function_assumptions.get(f) {
                            for (required_args, result) in assumptions {
                                if args.len() == required_args.len()
                                    && required_args.iter().zip(args.iter()).all(|(req, arg)| {
                                        primop::eq_anything(req.clone(), arg.clone(), solver, *info)
                                            .map(|v| match v {
                                                Val::Symbolic(var) => {
                                                    solver.check_sat_with(&smtlib::Exp::Eq(
                                                        Box::new(smtlib::Exp::Var(var)),
                                                        Box::new(smtlib::Exp::Bool(false)),
                                                    ), *info) == SmtResult::Unsat
                                                }
                                                Val::Bool(b) => b,
                                                _ => panic!("TODO"),
                                            })
                                            .unwrap()
                                    })
                                {
                                    assign(
                                        tid,
                                        loc,
                                        result.clone(),
                                        &mut frame.local_state,
                                        shared_state,
                                        solver,
                                        *info,
                                    )?;
                                    solver.add_event(Event::UseFunAssumption {
                                        name: *f,
                                        args,
                                        return_value: result.clone(),
                                    });
                                    frame.pc += 1;
                                    continue 'main_loop;
                                }
                            }
                        }

                        let caller_pc = frame.pc;
                        let caller_instrs = frame.instrs;
                        let caller_stack_call = frame.stack_call.clone();
                        push_call_stack(frame);
                        frame.backtrace.push((frame.function_name, caller_pc));
                        frame.function_name = *f;
                        frame.vars_mut().insert(RETURN, UVal::Uninit(ret_ty));

                        // Set up a closure to restore our state when
                        // the function we call returns
                        frame.stack_call = Some(Arc::new(move |ret, frame, shared_state, solver| {
                            pop_call_stack(frame);
                            frame.set_probes(shared_state);
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
                None => panic!("Return variable missing at end of function"),
                Some(value) => {
                    let value = match value {
                        UVal::Uninit(ty) => symbolic(ty, shared_state, solver, SourceLoc::unknown())?,
                        UVal::Init(value) => value.clone(),
                    };

                    if frame.local_state.should_probe(shared_state, &frame.function_name) {
                        let symbol = zencode::decode(shared_state.symtab.to_str(frame.function_name));
                        log_from!(
                            tid,
                            log::PROBE,
                            &format!("Returning {} = {}", symbol, value.to_string(shared_state))
                        );
                        probe::args_info(tid, std::slice::from_ref(&value), shared_state, solver)
                    }

                    if shared_state.trace_functions.contains(&frame.function_name) {
                        solver.trace_return(frame.function_name)
                    }

                    let caller = match &frame.stack_call {
                        None => return Ok(Run::Finished(value)),
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

                    if solver.check_sat(*info).is_unsat()? {
                        return Ok(Run::Dead);
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

                    log_from!(tid, log::FORK, format!("Fork @ monomorphizing v{}", v));

                    frame.forks += 1;

                    // Because we will likely case-split more times in the task we add to the queue,
                    // give it a larger part of the fraction (otherwise the denominator becomes
                    // small very fast).
                    let child_frac = task_fraction.min_split(6);
                    queue.push(Task {
                        id: task_id,
                        fraction: child_frac,
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
                if frame.local_state.should_probe(shared_state, &frame.function_name) {
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
                    None => return Ok(Run::Finished(Val::Poison)),
                    Some(caller) => Arc::clone(caller),
                };
                (*caller)(Val::Poison, frame, shared_state, solver)?
            }

            Instr::Exit(cause, info) => {
                return match cause {
                    ExitCause::MatchFailure => Err(ExecError::MatchFailure(*info)),
                    ExitCause::AssertionFailure => Err(ExecError::AssertionFailure(None, *info)),
                    ExitCause::Explicit => Ok(Run::Exit),
                }
            }
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
    + Fn(usize, TaskId, Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>, &SharedState<'ir, B>, Solver<B>, &R);

/// Start symbolically executing a Task using just the current thread, collecting the results using
/// the given collector.
pub fn start_single<'ir, B: BV, R>(
    task: Task<'ir, '_, B>,
    shared_state: &SharedState<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) {
    let queue = Worker::new_lifo();
    queue.push(task);
    while let Some(mut task) = queue.pop() {
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
            &mut task.fraction,
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
    mut task: Task<'ir, 'task, B>,
    shared_state: &SharedState<'ir, B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
) -> Fraction {
    let cfg = Config::new();
    let ctx = Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, task.checkpoint);
    if let Some((def, event)) = task.fork_cond {
        solver.add_event(event);
        solver.add(def)
    };
    let result = run(
        tid,
        task.id,
        &mut task.fraction,
        timeout,
        task.stop_conditions,
        queue,
        &task.frame,
        task.state,
        shared_state,
        &mut solver,
    );
    collector(tid, task.id, result, shared_state, solver, collected);
    task.fraction
}

enum Response {
    Poke,
    Kill,
}

enum Progress {
    Finished { tid: usize, task_id: TaskId, frac: Fraction },
    Idle { tid: usize },
}

/// Start symbolically executing a Task across `num_threads` new threads, collecting the results
/// using the given collector.
pub fn start_multi<'ir, B: BV, R>(
    num_threads: usize,
    timeout: Option<u64>,
    tasks: Vec<Task<'ir, '_, B>>,
    shared_state: &SharedState<'ir, B>,
    collected: Arc<R>,
    collector: &Collector<'ir, B, R>,
) where
    R: Send + Sync,
{
    let timeout = Timeout { start_time: Instant::now(), duration: timeout.map(Duration::from_secs) };

    let (tx, rx): (Sender<Progress>, Receiver<Progress>) = mpsc::channel();
    let global: Arc<Injector<Task<B>>> = Arc::new(Injector::<Task<B>>::new());
    let stealers: Arc<RwLock<Vec<Stealer<Task<B>>>>> = Arc::new(RwLock::new(Vec::new()));

    let mut progress: HashMap<TaskId, Fraction, ahash::RandomState> = HashMap::default();

    for task in tasks {
        global.push(task);
    }

    thread::scope(|scope| {
        let mut poke_txs = Vec::new();

        for tid in 0..num_threads {
            // When a worker is idle, it reports that to the main orchestrating thread, which can
            // then 'poke' it to wake it up via a channel, which will cause the worker to try to
            // steal some work, or the main thread can kill the worker.
            let (poke_tx, poke_rx): (Sender<Response>, Receiver<Response>) = mpsc::channel();
            poke_txs.push(poke_tx.clone());

            let thread_tx = tx.clone();
            let global = global.clone();
            let stealers = stealers.clone();
            let collected = collected.clone();

            scope.spawn(move || {
                let q = Worker::new_lifo();
                {
                    let mut stealers = stealers.write().unwrap();
                    stealers.push(q.stealer());
                }
                loop {
                    while let Some(task) = find_task(&q, &global, &stealers) {
                        let task_id = task.id;
                        let frac = do_work(tid, timeout, &q, task, shared_state, collected.as_ref(), collector);
                        thread_tx.send(Progress::Finished { tid, task_id, frac }).unwrap();
                    }
                    thread_tx.send(Progress::Idle { tid }).unwrap();
                    match poke_rx.recv().unwrap() {
                        Response::Poke => (),
                        Response::Kill => break,
                    }
                }
            });
        }

        let mut is_idle = vec![false; num_threads];
        loop {
            loop {
                match rx.try_recv() {
                    Ok(Progress::Finished { tid, task_id, frac }) => {
                        let current_fraction = progress.entry(task_id).or_insert(Fraction::zero());
                        *current_fraction += frac;
                        is_idle[tid] = false
                    }
                    Ok(Progress::Idle { tid }) => is_idle[tid] = true,
                    Err(_) => break,
                }
            }
            // Try to wake up any idle threads
            for (tid, idle) in is_idle.iter().enumerate() {
                if *idle {
                    poke_txs[tid].send(Response::Poke).unwrap()
                }
            }
            let mut all_tasks_complete = true;
            for (_, frac) in progress.iter() {
                if !frac.is_one() {
                    all_tasks_complete = false;
                }
            }
            if all_tasks_complete {
                for poke_tx in poke_txs.iter() {
                    poke_tx.send(Response::Kill).unwrap()
                }
                break;
            }
            thread::sleep(Duration::from_millis(1))
        }
    })
}

type Spawner<'ir, 'task, B, R> = dyn Fn(&R) -> Vec<Task<'ir, 'task, B>>;

pub trait Collection: Default {
    fn link_child(&self, task_id: TaskId);
    fn link_parent(&self, task_id: TaskId);
}

/// Start symbolically executing a Task across `num_threads` new
/// threads, collecting a separate result for each task.
pub fn start_multi_per_task<'ir, 'task, B: BV, R>(
    num_threads: usize,
    timeout: Option<u64>,
    tasks: Vec<Task<'ir, 'task, B>>,
    shared_state: &SharedState<'ir, B>,
    collector: &Collector<'ir, B, R>,
    spawner: &Spawner<'ir, 'task, B, R>,
) -> HashMap<TaskId, R, ahash::RandomState>
where
    R: Send + Sync + Collection,
{
    let timeout = Timeout { start_time: Instant::now(), duration: timeout.map(Duration::from_secs) };

    let (tx, rx): (Sender<Progress>, Receiver<Progress>) = mpsc::channel();
    let global: Arc<Injector<Task<B>>> = Arc::new(Injector::<Task<B>>::new());
    let stealers: Arc<RwLock<Vec<Stealer<Task<B>>>>> = Arc::new(RwLock::new(Vec::new()));

    let mut progress: HashMap<TaskId, Fraction, ahash::RandomState> = HashMap::default();
    let mut finished: HashSet<TaskId, ahash::RandomState> = HashSet::default();
    let mut collected_lock: RwLock<HashMap<TaskId, R, ahash::RandomState>> = RwLock::new(HashMap::default());

    for task in tasks {
        let collected = collected_lock.get_mut().unwrap();
        collected.insert(task.id, R::default());
        global.push(task);
    }

    thread::scope(|scope| {
        let mut poke_txs = Vec::new();

        for tid in 0..num_threads {
            // When a worker is idle, it reports that to the main orchestrating thread, which can
            // then 'poke' it to wake it up via a channel, which will cause the worker to try to
            // steal some work, or the main thread can kill the worker.
            let (poke_tx, poke_rx): (Sender<Response>, Receiver<Response>) = mpsc::channel();
            poke_txs.push(poke_tx.clone());

            let thread_tx = tx.clone();
            let global = global.clone();
            let stealers = stealers.clone();
            let collected_lock = &collected_lock;

            scope.spawn(move || {
                let q = Worker::new_lifo();
                {
                    let mut stealers = stealers.write().unwrap();
                    stealers.push(q.stealer());
                }
                loop {
                    while let Some(task) = find_task(&q, &global, &stealers) {
                        let task_id = task.id;
                        let collected = collected_lock.read().unwrap();
                        let task_results = collected.get(&task_id).unwrap();
                        let frac = do_work(tid, timeout, &q, task, shared_state, task_results, collector);
                        thread_tx.send(Progress::Finished { tid, task_id, frac }).unwrap();
                    }
                    thread_tx.send(Progress::Idle { tid }).unwrap();
                    match poke_rx.recv().unwrap() {
                        Response::Poke => (),
                        Response::Kill => break,
                    }
                }
            });
        }

        let mut is_idle = vec![false; num_threads];
        loop {
            loop {
                match rx.try_recv() {
                    Ok(Progress::Finished { tid, task_id, frac }) => {
                        let current_fraction = progress.entry(task_id).or_insert(Fraction::zero());
                        *current_fraction += frac;
                        is_idle[tid] = false
                    }
                    Ok(Progress::Idle { tid }) => is_idle[tid] = true,
                    Err(_) => break,
                }
            }
            // Try to wake up any idle threads
            for (tid, idle) in is_idle.iter().enumerate() {
                if *idle {
                    poke_txs[tid].send(Response::Poke).unwrap()
                }
            }
            let mut all_tasks_complete = true;
            for (task_id, frac) in progress.iter() {
                if frac.is_one() && !finished.contains(task_id) {
                    let mut collected = collected_lock.write().unwrap();
                    let task_results = collected.get(task_id).unwrap();
                    let mut new_tasks = spawner(task_results);
                    if !new_tasks.is_empty() {
                        all_tasks_complete = false;
                    };
                    for new_task in new_tasks.iter() {
                        task_results.link_child(new_task.id);
                    }
                    for new_task in new_tasks.drain(..) {
                        let results = R::default();
                        results.link_parent(*task_id);
                        collected.insert(new_task.id, results);
                        global.push(new_task);
                    }
                    finished.insert(*task_id);
                }
                if !frac.is_one() {
                    all_tasks_complete = false;
                }
            }
            if all_tasks_complete {
                for poke_tx in poke_txs.iter() {
                    poke_tx.send(Response::Kill).unwrap()
                }
                break;
            }
            thread::sleep(Duration::from_millis(1))
        }
    });

    collected_lock.into_inner().unwrap()
}

/// This `Collector` is used for boolean Sail functions. It returns
/// true via an AtomicBool if all reachable paths through the program
/// are unsatisfiable, which implies that the function always returns
/// true.
pub fn all_unsat_collector<'ir, B: BV>(
    tid: usize,
    _: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &AtomicBool,
) {
    match result {
        Ok((Run::Finished(value), _)) => match value {
            Val::Symbolic(v) => {
                use smtlib::Def::*;
                use smtlib::Exp::*;
                solver.add(Assert(Not(Box::new(Var(v)))));
                if solver.check_sat(SourceLoc::unknown()) != SmtResult::Unsat {
                    log_from!(tid, log::VERBOSE, "Got sat");
                    collected.store(false, Ordering::Release)
                } else {
                    log_from!(tid, log::VERBOSE, "Got unsat")
                }
            }
            Val::Bool(true) => log_from!(tid, log::VERBOSE, "Got true"),
            Val::Bool(false) => {
                log_from!(tid, log::VERBOSE, "Got false");
                collected.store(false, Ordering::Release)
            }
            _ => log_from!(tid, log::VERBOSE, &format!("Got value {:?}", value)),
        },
        Ok((Run::Dead, _)) => (),
        Ok((Run::Exit | Run::Suspended, _)) => log_from!(tid, log::VERBOSE, "Unexpected return".to_string()),
        Err((err, backtrace)) => {
            if_logging!(log::VERBOSE, {
                log_from!(tid, log::VERBOSE, &format!("Got error, {:?}", err));
                for (f, pc) in backtrace.iter().rev() {
                    log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
                }
            });
            collected.store(false, Ordering::Release)
        }
    }
}

#[derive(Debug)]
pub enum TraceError {
    /// This is returned when we get an unexpected value at the end of
    /// a trace, for example if we are expecting a boolean result and
    /// we get something else.
    UnexpectedValue(String),
    /// When the trace suspended itself, and we aren't expecting it
    /// to, we cannot return a complete trace.
    UnexpectedSuspension,
    /// An execution error occured when generating the trace
    Exec { err: ExecError, model: Option<String> },
}

impl IslaError for TraceError {
    fn source_loc(&self) -> SourceLoc {
        match self {
            TraceError::UnexpectedValue(_) => SourceLoc::unknown(),
            TraceError::UnexpectedSuspension => SourceLoc::unknown(),
            TraceError::Exec { err, .. } => err.source_loc(),
        }
    }
}

impl fmt::Display for TraceError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TraceError::UnexpectedValue(s) => write!(f, "Unexpected value {}", s),
            TraceError::UnexpectedSuspension => write!(f, "Unexpected suspension"),
            TraceError::Exec { err, model: Some(s) } => write!(f, "{}\nModel: {}", err, s),
            TraceError::Exec { err, model: None } => write!(f, "{}", err),
        }
    }
}

impl TraceError {
    pub fn exec(err: ExecError) -> Self {
        TraceError::Exec { err, model: None }
    }

    fn exec_model<B: BV>(err: ExecError, model: Model<B>) -> Self {
        TraceError::Exec { err, model: Some(format!("{:?}", model)) }
    }

    fn unexpected_value<B: BV>(v: Val<B>) -> Self {
        TraceError::UnexpectedValue(format!("{:?}", v))
    }
}

pub type TraceQueue<B> = SegQueue<Result<(TaskId, Vec<Event<B>>), TraceError>>;

pub type TraceResultQueue<B> = SegQueue<Result<(TaskId, bool, Vec<Event<B>>), TraceError>>;

pub type TraceValueQueue<B> = SegQueue<Result<(TaskId, Val<B>, Vec<Event<B>>), TraceError>>;

pub fn trace_collector<'ir, B: BV>(
    tid: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    match result {
        Ok((Run::Finished(_) | Run::Exit, _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, events.drain(..).cloned().collect())))
        }
        Ok((Run::Suspended, _)) => collected.push(Err(TraceError::UnexpectedSuspension)),
        Ok((Run::Dead, _)) => (),
        Err((err, backtrace)) => {
            log_from!(tid, log::VERBOSE, format!("Error {:?}", err));
            for (f, pc) in backtrace.iter().rev() {
                log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
            }
            if solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat {
                let model = Model::new(&solver);
                collected.push(Err(TraceError::exec_model(err, model)))
            } else {
                collected.push(Err(TraceError::exec(err)))
            }
        }
    }
}

pub fn trace_value_collector<'ir, B: BV>(
    _: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    _: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &TraceValueQueue<B>,
) {
    match result {
        Ok((Run::Finished(value), _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, value, events.drain(..).cloned().collect())))
        }
        Ok((Run::Exit | Run::Suspended, _)) => (),
        Ok((Run::Dead, _)) => (),
        Err((err, _)) => {
            if solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat {
                let model = Model::new(&solver);
                collected.push(Err(TraceError::exec_model(err, model)))
            } else {
                collected.push(Err(TraceError::exec(err)))
            }
        }
    }
}

pub fn trace_result_collector<'ir, B: BV>(
    _: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    _: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceResultQueue<B>,
) {
    match result {
        Ok((Run::Finished(Val::Bool(result)), _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, result, events.drain(..).cloned().collect())))
        }
        Ok((Run::Exit, _)) => (),
        Ok((Run::Suspended, _)) => collected.push(Err(TraceError::UnexpectedSuspension)),
        Ok((Run::Finished(val), _)) => collected.push(Err(TraceError::unexpected_value(val))),
        Ok((Run::Dead, _)) => (),
        Err((err, _)) => collected.push(Err(TraceError::exec(err))),
    }
}

pub fn footprint_collector<'ir, B: BV>(
    _: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    _: &SharedState<'ir, B>,
    solver: Solver<B>,
    collected: &TraceQueue<B>,
) {
    match result {
        // Footprint function returns true on traces we need to consider as part of the footprint
        Ok((Run::Finished(Val::Bool(true)), _)) => {
            let mut events = solver.trace().to_vec();
            collected.push(Ok((task_id, events.drain(..).cloned().collect())))
        }
        // If it is dead, returns false or exits, we ignore that trace
        Ok((Run::Finished(Val::Bool(false)) | Run::Exit | Run::Dead, _)) => (),
        // Any other value is an error!
        Ok((Run::Finished(value), _)) => collected.push(Err(TraceError::unexpected_value(value))),

        Ok((Run::Suspended, _)) => collected.push(Err(TraceError::UnexpectedSuspension)),

        Err((err, _)) => collected.push(Err(TraceError::exec(err))),
    }
}
