// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
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

//! This module is a big set of primitive operations and builtins
//! which are implemented over the [crate::ir::Val] type. Most are not
//! exported directly but instead are exposed via the [Primops] struct
//! which contains all the primops (and is created using it's Default
//! instance). During initialization (via the [crate::init] module)
//! textual references to primops in the IR are replaced with direct
//! function pointers to their implementation in this module. The
//! [Unary], [Binary], and [Variadic] types are function pointers to
//! unary, binary, and other primops, which are contained within
//! [Primops].

#![allow(clippy::comparison_chain)]
#![allow(clippy::cognitive_complexity)]

use std::cmp::min;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::ops::{Not, Shl, Shr};
use std::str::FromStr;

use crate::bitvector::b64::B64;
use crate::bitvector::BV;
use crate::error::ExecError;
use crate::executor::LocalFrame;
use crate::ir::{BitsSegment, Reset, UVal, Val, ELF_ENTRY};
use crate::primop_util::*;
use crate::smt::smtlib::*;
use crate::smt::*;
use crate::source_loc::SourceLoc;

pub mod float;
pub mod memory;

pub type Unary<B> = fn(Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError>;
pub type Binary<B> = fn(Val<B>, Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError>;
pub type Variadic<B> =
    fn(Vec<Val<B>>, solver: &mut Solver<B>, frame: &mut LocalFrame<B>, info: SourceLoc) -> Result<Val<B>, ExecError>;

#[allow(clippy::needless_range_loop)]
fn smt_mask_lower<V>(len: usize, mask_width: usize) -> Exp<V> {
    if len <= 64 {
        Exp::Bits64(B64::new(u64::MAX >> (64 - mask_width), len as u32))
    } else {
        let mut bitvec = vec![false; len];
        for i in 0..mask_width {
            bitvec[i] = true
        }
        Exp::Bits(bitvec)
    }
}

fn smt_zeros<V>(i: i128) -> Exp<V> {
    if i <= 64 {
        Exp::Bits64(B64::zeros(i as u32))
    } else {
        Exp::Bits(vec![false; i as usize])
    }
}

fn smt_ones<V>(i: i128) -> Exp<V> {
    if i <= 64 {
        Exp::Bits64(B64::ones(i as u32))
    } else {
        Exp::Bits(vec![true; i as usize])
    }
}

macro_rules! unary_primop_copy {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path) => {
        pub fn $f<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            match replace_mixed_bits(x, solver, info)? {
                Val::Symbolic(x) => solver.define_const($smt_op(Box::new(Exp::Var(x))), info).into(),
                $unwrap(x) => Ok($wrap($concrete_op(x))),
                _ => Err(ExecError::Type($name, info)),
            }
        }
    };
}

macro_rules! binary_primop_copy {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path, $to_symbolic:path) => {
        pub fn $f<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            match (replace_mixed_bits(x, solver, info)?, replace_mixed_bits(y, solver, info)?) {
                (Val::Symbolic(x), Val::Symbolic(y)) => {
                    solver.define_const($smt_op(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
                }
                (Val::Symbolic(x), $unwrap(y)) => {
                    solver.define_const($smt_op(Box::new(Exp::Var(x)), Box::new($to_symbolic(y))), info).into()
                }
                ($unwrap(x), Val::Symbolic(y)) => {
                    solver.define_const($smt_op(Box::new($to_symbolic(x)), Box::new(Exp::Var(y))), info).into()
                }
                ($unwrap(x), $unwrap(y)) => Ok($wrap($concrete_op(x, y))),
                (_, _) => Err(ExecError::Type($name, info)),
            }
        }
    };
}

macro_rules! binary_primop {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path, $to_symbolic:path) => {
        pub fn $f<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            match (replace_mixed_bits(x, solver, info)?, replace_mixed_bits(y, solver, info)?) {
                (Val::Symbolic(x), Val::Symbolic(y)) => {
                    solver.define_const($smt_op(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
                }
                (Val::Symbolic(x), $unwrap(y)) => {
                    solver.define_const($smt_op(Box::new(Exp::Var(x)), Box::new($to_symbolic(y))), info).into()
                }
                ($unwrap(x), Val::Symbolic(y)) => {
                    solver.define_const($smt_op(Box::new($to_symbolic(x)), Box::new(Exp::Var(y))), info).into()
                }
                ($unwrap(x), $unwrap(y)) => Ok($wrap($concrete_op(&x, &y))),
                (_, _) => Err(ExecError::Type($name, info)),
            }
        }
    };
}

pub(crate) fn assume<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::Symbolic(v) => {
            solver.add(Def::Assert(Exp::Var(v)));
            Ok(Val::Unit)
        }
        Val::Bool(b) => {
            if b {
                Ok(Val::Unit)
            } else {
                solver.add(Def::Assert(Exp::Bool(false)));
                Ok(Val::Unit)
            }
        }
        _ => Err(ExecError::Type(format!("assert {:?}", &x), info)),
    }
}

// If the assertion can succeed, it will
fn optimistic_assert<B: BV>(
    x: Val<B>,
    message: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let message = match message {
        Val::String(message) => Some(message),
        _ => None,
    };
    match x {
        Val::Symbolic(v) => {
            let test_true = Box::new(Exp::Var(v));
            let can_be_true = solver.check_sat_with(&test_true, info).is_sat()?;
            if can_be_true {
                solver.add(Def::Assert(Exp::Var(v)));
                Ok(Val::Unit)
            } else {
                Err(ExecError::AssertionFailure(message, info))
            }
        }
        Val::Bool(b) => {
            if b {
                Ok(Val::Unit)
            } else {
                Err(ExecError::AssertionFailure(message, info))
            }
        }
        _ => Err(ExecError::Type(format!("optimistic_assert {:?}", &x), info)),
    }
}

// If the assertion can fail, it will
fn pessimistic_assert<B: BV>(
    x: Val<B>,
    message: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let message = match message {
        Val::String(message) => Some(message),
        _ => None,
    };
    match x {
        Val::Symbolic(v) => {
            let test_false = Exp::Not(Box::new(Exp::Var(v)));
            let can_be_false = solver.check_sat_with(&test_false, info).is_sat()?;
            if can_be_false {
                Err(ExecError::AssertionFailure(message, info))
            } else {
                Ok(Val::Unit)
            }
        }
        Val::Bool(b) => {
            if b {
                Ok(Val::Unit)
            } else {
                Err(ExecError::AssertionFailure(message, info))
            }
        }
        _ => Err(ExecError::Type(format!("pessimistic_assert {:?}", &x), info)),
    }
}

// Conversion functions

fn i64_to_i128<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::I64(x) => Ok(Val::I128(i128::from(x))),
        Val::Symbolic(x) => solver.define_const(Exp::SignExtend(64, Box::new(Exp::Var(x))), info).into(),
        _ => Err(ExecError::Type(format!("%i64->%i {:?}", &x), info)),
    }
}

fn i128_to_i64<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::I128(x) => match i64::try_from(x) {
            Ok(y) => Ok(Val::I64(y)),
            Err(_) => Err(ExecError::Overflow),
        },
        Val::Symbolic(x) => solver.define_const(Exp::Extract(63, 0, Box::new(Exp::Var(x))), info).into(),
        _ => Err(ExecError::Type(format!("%i->%i64 {:?}", &x), info)),
    }
}

// FIXME: The Sail->C compilation uses xs == NULL to check if a list
// is empty, so we replicate that here for now, but we should
// introduce a separate @is_empty operator instead.
pub(crate) fn op_eq<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::List(xs), Val::List(ys)) => {
            if xs.len() != ys.len() {
                Ok(Val::Bool(false))
            } else if xs.is_empty() && ys.is_empty() {
                Ok(Val::Bool(true))
            } else {
                Err(ExecError::Type(format!("op_eq {:?} {:?}", &xs, &ys), info))
            }
        }
        (x, y) => eq_anything(x, y, solver, info),
    }
}

pub(crate) fn op_neq<B: BV>(
    x: Val<B>,
    y: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::List(xs), Val::List(ys)) => {
            if xs.len() != ys.len() {
                Ok(Val::Bool(true))
            } else if xs.is_empty() && ys.is_empty() {
                Ok(Val::Bool(false))
            } else {
                Err(ExecError::Type(format!("op_neq {:?} {:?}", &xs, &ys), info))
            }
        }
        (x, y) => neq_anything(x, y, solver, info),
    }
}

pub(crate) fn op_head<B: BV>(xs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        Val::List(mut xs) => match xs.pop() {
            Some(x) => Ok(x),
            None => Err(ExecError::Type(format!("op_head (list empty) {:?}", &xs), info)),
        },
        _ => Err(ExecError::Type(format!("op_head {:?}", &xs), info)),
    }
}

pub(crate) fn op_tail<B: BV>(xs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        Val::List(mut xs) => {
            xs.pop();
            Ok(Val::List(xs))
        }
        _ => Err(ExecError::Type(format!("op_tail {:?}", &xs), info)),
    }
}

pub(crate) fn op_is_empty<B: BV>(xs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        Val::List(xs) => Ok(Val::Bool(xs.is_empty())),
        _ => Err(ExecError::Type(format!("op_tail {:?}", &xs), info)),
    }
}

binary_primop!(op_lt, "op_lt".to_string(), Val::I64, Val::Bool, i64::lt, Exp::Bvslt, smt_i64);
binary_primop!(op_gt, "op_gt".to_string(), Val::I64, Val::Bool, i64::gt, Exp::Bvsgt, smt_i64);
binary_primop!(op_lteq, "op_lteq".to_string(), Val::I64, Val::Bool, i64::le, Exp::Bvsle, smt_i64);
binary_primop!(op_gteq, "op_gteq".to_string(), Val::I64, Val::Bool, i64::ge, Exp::Bvsge, smt_i64);
binary_primop_copy!(op_add, "op_add".to_string(), Val::I64, Val::I64, i64::wrapping_add, Exp::Bvadd, smt_i64);
binary_primop_copy!(op_sub, "op_sub".to_string(), Val::I64, Val::I64, i64::wrapping_sub, Exp::Bvsub, smt_i64);

pub(crate) fn bit_to_bool<B: BV>(bit: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match bit {
        Val::Bits(bit) => Ok(Val::Bool(bit == B::BIT_ONE)),
        Val::Symbolic(bit) => {
            solver.define_const(Exp::Eq(Box::new(Exp::Bits([true].to_vec())), Box::new(Exp::Var(bit))), info).into()
        }
        _ => Err(ExecError::Type(format!("bit_to_bool {:?}", &bit), info)),
    }
}

pub(crate) fn op_unsigned<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => Ok(Val::I64(bits.unsigned() as i64)),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => solver.define_const(Exp::ZeroExtend(64 - length, Box::new(Exp::Var(bits))), info).into(),
            None => Err(ExecError::Type(format!("op_unsigned {:?}", &bits), info)),
        },
        _ => Err(ExecError::Type(format!("op_unsigned {:?}", &bits), info)),
    }
}

pub(crate) fn op_signed<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => Ok(Val::I64(bits.signed() as i64)),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => solver.define_const(Exp::SignExtend(64 - length, Box::new(Exp::Var(bits))), info).into(),
            None => Err(ExecError::Type(format!("op_unsigned (solver cannot determine length) {:?}", &bits), info)),
        },
        _ => Err(ExecError::Type(format!("op_unsigned {:?}", &bits), info)),
    }
}

// Basic comparisons

unary_primop_copy!(not_bool, "not".to_string(), Val::Bool, Val::Bool, bool::not, Exp::Not);
binary_primop!(eq_int, "eq_int".to_string(), Val::I128, Val::Bool, i128::eq, Exp::Eq, smt_i128);
binary_primop!(eq_bool, "eq_bool".to_string(), Val::Bool, Val::Bool, bool::eq, Exp::Eq, Exp::Bool);
binary_primop!(lteq_int, "lteq".to_string(), Val::I128, Val::Bool, i128::le, Exp::Bvsle, smt_i128);
binary_primop!(gteq_int, "gteq".to_string(), Val::I128, Val::Bool, i128::ge, Exp::Bvsge, smt_i128);
binary_primop!(lt_int, "lt".to_string(), Val::I128, Val::Bool, i128::lt, Exp::Bvslt, smt_i128);
binary_primop!(gt_int, "gt".to_string(), Val::I128, Val::Bool, i128::gt, Exp::Bvsgt, smt_i128);

pub fn and_bool<B: BV>(lhs: Val<B>, rhs: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::Bool(false), _) => Ok(Val::Bool(false)),
        (_, Val::Bool(false)) => Ok(Val::Bool(false)),
        (Val::Bool(true), rhs) => Ok(rhs),
        (lhs, Val::Bool(true)) => Ok(lhs),
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            solver.define_const(Exp::And(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
        }
        (lhs, rhs) => Err(ExecError::Type(format!("and_bool {:?} {:?}", lhs, rhs), info)),
    }
}

pub fn or_bool<B: BV>(lhs: Val<B>, rhs: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::Bool(true), _) => Ok(Val::Bool(true)),
        (_, Val::Bool(true)) => Ok(Val::Bool(true)),
        (Val::Bool(false), rhs) => Ok(rhs),
        (lhs, Val::Bool(false)) => Ok(lhs),
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            solver.define_const(Exp::Or(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
        }
        (lhs, rhs) => Err(ExecError::Type(format!("or_bool {:?} {:?}", lhs, rhs), info)),
    }
}

fn abs_int<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::I128(x) => Ok(Val::I128(x.abs())),
        Val::Symbolic(x) => {
            let y = solver.fresh();
            solver.add(Def::DefineConst(
                y,
                Exp::Ite(
                    Box::new(Exp::Bvslt(Box::new(Exp::Var(x)), Box::new(smt_i128(0)))),
                    Box::new(Exp::Bvneg(Box::new(Exp::Var(x)))),
                    Box::new(Exp::Var(x)),
                ),
            ));
            Ok(Val::Symbolic(y))
        }
        _ => Err(ExecError::Type(format!("abs_int {:?}", &x), info)),
    }
}

// Arithmetic operations

fn ediv_i128<V: Clone>(x: Box<Exp<V>>, y: Box<Exp<V>>) -> Exp<V> {
    Exp::Ite(
        Box::new(Exp::Bvslt(Box::new(Exp::Bvsrem(x.clone(), y.clone())), Box::new(smt_i128(0)))),
        Box::new(Exp::Ite(
            Box::new(Exp::Bvsgt(y.clone(), Box::new(smt_i128(0)))),
            Box::new(Exp::Bvsub(Box::new(Exp::Bvsdiv(x.clone(), y.clone())), Box::new(smt_i128(1)))),
            Box::new(Exp::Bvadd(Box::new(Exp::Bvsdiv(x.clone(), y.clone())), Box::new(smt_i128(1)))),
        )),
        Box::new(Exp::Bvsdiv(x, y)),
    )
}

fn emod_i128<V: Clone>(x: Box<Exp<V>>, y: Box<Exp<V>>) -> Exp<V> {
    let srem = Box::new(Exp::Bvsrem(x, y.clone()));
    Exp::Ite(
        Box::new(Exp::Bvslt(srem.clone(), Box::new(smt_i128(0)))),
        Box::new(Exp::Ite(
            Box::new(Exp::Bvslt(y.clone(), Box::new(smt_i128(0)))),
            Box::new(Exp::Bvsub(srem.clone(), y.clone())),
            Box::new(Exp::Bvadd(srem.clone(), y)),
        )),
        srem,
    )
}

binary_primop_copy!(sub_int, "sub_int".to_string(), Val::I128, Val::I128, i128::wrapping_sub, Exp::Bvsub, smt_i128);
binary_primop_copy!(mult_int, "mult_int".to_string(), Val::I128, Val::I128, i128::wrapping_mul, Exp::Bvmul, smt_i128);
unary_primop_copy!(neg_int, "neg_int".to_string(), Val::I128, Val::I128, i128::wrapping_neg, Exp::Bvneg);
binary_primop_copy!(tdiv_int, "tdiv_int".to_string(), Val::I128, Val::I128, i128::wrapping_div, Exp::Bvsdiv, smt_i128);
binary_primop_copy!(
    ediv_int,
    "ediv_int".to_string(),
    Val::I128,
    Val::I128,
    i128::wrapping_div_euclid,
    ediv_i128,
    smt_i128
);
binary_primop_copy!(tmod_int, "tmod_int".to_string(), Val::I128, Val::I128, i128::wrapping_rem, Exp::Bvsrem, smt_i128);
binary_primop_copy!(
    emod_int,
    "emod_int".to_string(),
    Val::I128,
    Val::I128,
    i128::wrapping_rem_euclid,
    emod_i128,
    smt_i128
);
binary_primop_copy!(shl_int, "shl_int".to_string(), Val::I128, Val::I128, i128::shl, Exp::Bvshl, smt_i128);
binary_primop_copy!(shr_int, "shr_int".to_string(), Val::I128, Val::I128, i128::shr, Exp::Bvashr, smt_i128);
binary_primop_copy!(shl_mach_int, "shl_mach_int".to_string(), Val::I64, Val::I64, i64::shl, Exp::Bvshl, smt_i64);
binary_primop_copy!(shr_mach_int, "shr_mach_int".to_string(), Val::I64, Val::I64, i64::shr, Exp::Bvashr, smt_i64);
binary_primop_copy!(udiv_int, "udiv_int".to_string(), Val::I128, Val::I128, i128::wrapping_div, Exp::Bvudiv, smt_i128);

pub(crate) fn add_int<B: BV>(
    x: Val<B>,
    y: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            solver.define_const(Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
        }
        (Val::Symbolic(x), Val::I128(y)) => {
            if y != 0 {
                solver.define_const(Exp::Bvadd(Box::new(Exp::Var(x)), Box::new(smt_i128(y))), info).into()
            } else {
                Ok(Val::Symbolic(x))
            }
        }
        (Val::I128(x), Val::Symbolic(y)) => {
            if x != 0 {
                solver.define_const(Exp::Bvadd(Box::new(smt_i128(x)), Box::new(Exp::Var(y))), info).into()
            } else {
                Ok(Val::Symbolic(y))
            }
        }
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(i128::wrapping_add(x, y))),
        (x, y) => Err(ExecError::Type(format!("add_int {:?} {:?}", &x, &y), info)),
    }
}

macro_rules! symbolic_compare {
    ($op: path, $x: expr, $y: expr, $solver: ident) => {{
        let z = $solver.fresh();
        $solver
            .add(Def::DefineConst(z, Exp::Ite(Box::new($op(Box::new($x), Box::new($y))), Box::new($x), Box::new($y))));
        Ok(Val::Symbolic(z))
    }};
}

fn max_int<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(i128::max(x, y))),
        (Val::I128(x), Val::Symbolic(y)) => symbolic_compare!(Exp::Bvsgt, smt_i128(x), Exp::Var(y), solver),
        (Val::Symbolic(x), Val::I128(y)) => symbolic_compare!(Exp::Bvsgt, Exp::Var(x), smt_i128(y), solver),
        (Val::Symbolic(x), Val::Symbolic(y)) => symbolic_compare!(Exp::Bvsgt, Exp::Var(x), Exp::Var(y), solver),
        (x, y) => Err(ExecError::Type(format!("max_int {:?} {:?}", &x, &y), info)),
    }
}

fn min_int<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(i128::min(x, y))),
        (Val::I128(x), Val::Symbolic(y)) => symbolic_compare!(Exp::Bvslt, smt_i128(x), Exp::Var(y), solver),
        (Val::Symbolic(x), Val::I128(y)) => symbolic_compare!(Exp::Bvslt, Exp::Var(x), smt_i128(y), solver),
        (Val::Symbolic(x), Val::Symbolic(y)) => symbolic_compare!(Exp::Bvslt, Exp::Var(x), Exp::Var(y), solver),
        (x, y) => Err(ExecError::Type(format!("max_int {:?} {:?}", &x, &y), info)),
    }
}

fn pow2<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::I128(x) => Ok(Val::I128(1 << x)),
        Val::Symbolic(x) => solver.define_const(Exp::Bvshl(Box::new(smt_i128(1)), Box::new(Exp::Var(x))), info).into(),
        _ => Err(ExecError::Type(format!("pow2 {:?}", &x), info)),
    }
}

fn pow_int<B: BV>(x: Val<B>, y: Val<B>, _solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(x.pow(y.try_into().map_err(|_| ExecError::Overflow)?))),
        (x, y) => Err(ExecError::Type(format!("pow_int {:?} {:?}", &x, &y), info)),
    }
}

fn sub_nat<B: BV>(x: Val<B>, y: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (x, y) {
        (Val::I128(x), Val::I128(y)) => Ok(Val::I128(i128::max(x - y, 0))),
        (Val::I128(x), Val::Symbolic(y)) => {
            symbolic_compare!(Exp::Bvsgt, Exp::Bvsub(Box::new(smt_i128(x)), Box::new(Exp::Var(y))), smt_i128(0), solver)
        }
        (Val::Symbolic(x), Val::I128(y)) => {
            symbolic_compare!(Exp::Bvsgt, Exp::Bvsub(Box::new(Exp::Var(x)), Box::new(smt_i128(y))), smt_i128(0), solver)
        }
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            symbolic_compare!(Exp::Bvsgt, Exp::Bvsub(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), smt_i128(0), solver)
        }
        (x, y) => Err(ExecError::Type(format!("sub_nat {:?} {:?}", &x, &y), info)),
    }
}

// Bitvector operations

fn length<B: BV>(x: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match x {
        Val::Symbolic(v) => match solver.length(v) {
            Some(len) => Ok(Val::I128(i128::from(len))),
            None => Err(ExecError::Type(format!("length (solver cannot determine length) {:?}", &v), info)),
        },
        Val::Bits(bv) => Ok(Val::I128(bv.len_i128())),
        Val::MixedBits(segments) => Ok(Val::I128(
            segments.iter().try_fold(0, |n, segment| Ok(n + i128::from(segment_length(segment, solver, info)?)))?,
        )),
        Val::Vector(v) => Ok(Val::I128(v.len() as i128)),
        _ => Err(ExecError::Type(format!("length {:?}", &x), info)),
    }
}

binary_primop!(eq_bits, "eq_bits".to_string(), Val::Bits, Val::Bool, B::eq, Exp::Eq, smt_sbits);
binary_primop!(neq_bits, "neq_bits".to_string(), Val::Bits, Val::Bool, B::ne, Exp::Neq, smt_sbits);
unary_primop_copy!(not_bits, "not_bits".to_string(), Val::Bits, Val::Bits, B::not, Exp::Bvnot);
binary_primop_copy!(xor_bits, "xor_bits".to_string(), Val::Bits, Val::Bits, B::bitxor, Exp::Bvxor, smt_sbits);
binary_primop_copy!(or_bits, "or_bits".to_string(), Val::Bits, Val::Bits, B::bitor, Exp::Bvor, smt_sbits);
binary_primop_copy!(and_bits, "and_bits".to_string(), Val::Bits, Val::Bits, B::bitand, Exp::Bvand, smt_sbits);
binary_primop_copy!(add_bits, "add_bits".to_string(), Val::Bits, Val::Bits, B::add, Exp::Bvadd, smt_sbits);
binary_primop_copy!(sub_bits, "sub_bits".to_string(), Val::Bits, Val::Bits, B::sub, Exp::Bvsub, smt_sbits);

fn add_bits_int<B: BV>(bits: Val<B>, n: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (bits, n) {
        (Val::Bits(bits), Val::I128(n)) => Ok(Val::Bits(bits.add_i128(n))),
        (Val::Symbolic(bits), Val::I128(n)) => {
            let result = solver.fresh();
            let len = match solver.length(bits) {
                Some(len) => len,
                None => {
                    return Err(ExecError::Type(
                        format!("add_bits_int (solver cannot determine length) {:?} {:?}", &bits, &n),
                        info,
                    ))
                }
            };
            assert!(len <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvadd(Box::new(Exp::Var(bits)), Box::new(Exp::Extract(len - 1, 0, Box::new(smt_i128(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (Val::Bits(bits), Val::Symbolic(n)) => {
            let result = solver.fresh();
            assert!(bits.len() <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvadd(Box::new(smt_sbits(bits)), Box::new(Exp::Extract(bits.len() - 1, 0, Box::new(Exp::Var(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (Val::Symbolic(bits), Val::Symbolic(n)) => {
            let result = solver.fresh();
            let len = match solver.length(bits) {
                Some(len) => len,
                None => {
                    return Err(ExecError::Type(
                        format!("add_bits_int (solver cannot determine length) {:?} {:?}", &bits, &n),
                        info,
                    ))
                }
            };
            assert!(len <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvadd(Box::new(Exp::Var(bits)), Box::new(Exp::Extract(len - 1, 0, Box::new(Exp::Var(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (bits, n) => Err(ExecError::Type(format!("add_bits_int {:?} {:?}", &bits, &n), info)),
    }
}

fn sub_bits_int<B: BV>(bits: Val<B>, n: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (bits, n) {
        (Val::Bits(bits), Val::I128(n)) => Ok(Val::Bits(bits.sub_i128(n))),
        (Val::Symbolic(bits), Val::I128(n)) => {
            let result = solver.fresh();
            let len = match solver.length(bits) {
                Some(len) => len,
                None => {
                    return Err(ExecError::Type(
                        format!("sub_bits_int (solver cannot determine length) {:?} {:?}", &bits, &n),
                        info,
                    ))
                }
            };
            assert!(len <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvsub(Box::new(Exp::Var(bits)), Box::new(Exp::Extract(len - 1, 0, Box::new(smt_i128(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (Val::Bits(bits), Val::Symbolic(n)) => {
            let result = solver.fresh();
            assert!(bits.len() <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvsub(Box::new(smt_sbits(bits)), Box::new(Exp::Extract(bits.len() - 1, 0, Box::new(Exp::Var(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (Val::Symbolic(bits), Val::Symbolic(n)) => {
            let result = solver.fresh();
            let len = match solver.length(bits) {
                Some(len) => len,
                None => {
                    return Err(ExecError::Type(
                        format!("sub_bits_int (solver cannot determine length) {:?} {:?}", &bits, &n),
                        info,
                    ))
                }
            };
            assert!(len <= 128);
            solver.add(Def::DefineConst(
                result,
                Exp::Bvsub(Box::new(Exp::Var(bits)), Box::new(Exp::Extract(len - 1, 0, Box::new(Exp::Var(n))))),
            ));
            Ok(Val::Symbolic(result))
        }
        (bits, n) => Err(ExecError::Type(format!("sub_bits_int {:?} {:?}", &bits, &n), info)),
    }
}

fn zeros<B: BV>(len: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match len {
        Val::I128(len) => {
            if len <= B::MAX_WIDTH as i128 {
                Ok(Val::Bits(B::zeros(len as u32)))
            } else {
                solver.define_const(smt_zeros(len), info).into()
            }
        }
        Val::Symbolic(_) => Err(ExecError::SymbolicLength("zeros", info)),
        _ => Err(ExecError::Type(format!("zeros {:?}", &len), info)),
    }
}

fn ones<B: BV>(len: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match len {
        Val::I128(len) => {
            if len <= B::MAX_WIDTH as i128 {
                Ok(Val::Bits(B::ones(len as u32)))
            } else {
                solver.define_const(smt_ones(len), info).into()
            }
        }
        Val::Symbolic(_) => Err(ExecError::SymbolicLength("ones", info)),
        _ => Err(ExecError::Type(format!("ones {:?}", &len), info)),
    }
}

/// The zero_extend and sign_extend functions are essentially the
/// same, so use a macro to define both.
macro_rules! extension {
    ($id: ident, $name: expr, $smt_extension: path, $concrete_extension: path) => {
        pub fn $id<B: BV>(
            bits: Val<B>,
            len: Val<B>,
            solver: &mut Solver<B>,
            info: SourceLoc,
        ) -> Result<Val<B>, ExecError> {
            match (replace_mixed_bits(bits, solver, info)?, len) {
                (Val::Bits(bits), Val::I128(len)) => {
                    let len = len as u32;
                    if len > B::MAX_WIDTH {
                        let ext = len - bits.len();
                        solver.define_const($smt_extension(ext, Box::new(smt_sbits(bits))), info).into()
                    } else {
                        Ok(Val::Bits($concrete_extension(bits, len)))
                    }
                }
                (Val::Symbolic(bits), Val::I128(len)) => {
                    let ext = match solver.length(bits) {
                        Some(orig_len) => len as u32 - orig_len,
                        None => return Err(ExecError::Type($name, info)),
                    };
                    solver.define_const($smt_extension(ext, Box::new(Exp::Var(bits))), info).into()
                }
                (_, Val::Symbolic(_)) => Err(ExecError::SymbolicLength("extension", info)),
                (_, _) => Err(ExecError::Type($name, info)),
            }
        }
    };
}

extension!(zero_extend, "zero_extend".to_string(), Exp::ZeroExtend, B::zero_extend);
extension!(sign_extend, "sign_extend".to_string(), Exp::SignExtend, B::sign_extend);

pub(crate) fn op_zero_extend<B: BV>(
    bits: Val<B>,
    len: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => {
            if len > 64 {
                let ext = len - bits.len();
                solver.define_const(Exp::ZeroExtend(ext, Box::new(smt_sbits(bits))), info).into()
            } else {
                Ok(Val::Bits(B::zero_extend(bits, len)))
            }
        }
        Val::Symbolic(bits) => {
            let ext = match solver.length(bits) {
                Some(orig_len) => len - orig_len,
                None => {
                    return Err(ExecError::Type(
                        format!("op_zero_extend (solver cannot determine length) {:?}", &bits),
                        info,
                    ))
                }
            };
            solver.define_const(Exp::ZeroExtend(ext, Box::new(Exp::Var(bits))), info).into()
        }
        _ => Err(ExecError::Type(format!("op_zero_extend {:?}", &bits), info)),
    }
}

fn replicate_exp<V: Clone>(bits: Exp<V>, times: i128) -> Exp<V> {
    if times == 0 {
        bits64(0, 0)
    } else if times == 1 {
        bits
    } else {
        Exp::Concat(Box::new(bits.clone()), Box::new(replicate_exp(bits, times - 1)))
    }
}

fn replicate_bits<B: BV>(
    bits: Val<B>,
    times: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match (bits, times) {
        (Val::Bits(bits), Val::I128(times)) => match bits.replicate(times) {
            Some(replicated) => Ok(Val::Bits(replicated)),
            None => solver.define_const(replicate_exp(smt_sbits(bits), times), info).into(),
        },
        (Val::Symbolic(bits), Val::I128(times)) => {
            if times == 0 {
                Ok(Val::Bits(B::zeros(0)))
            } else {
                solver.define_const(replicate_exp(Exp::Var(bits), times), info).into()
            }
        }
        (bits, times) => Err(ExecError::Type(format!("replicate_bits {:?} {:?}", &bits, &times), info)),
    }
}

/// This macro implements the symbolic slice operation for anything
/// that is implemented as a bitvector in the SMT solver, so it can be
/// used for slice, get_slice_int, etc.
macro_rules! slice {
    ($bits_length: expr, $bits: expr, $from: expr, $slice_length: expr, $solver: ident, $info: ident) => {{
        assert!(($slice_length as u32) <= $bits_length);
        match $from {
            _ if $slice_length == 0 => Ok(Val::Bits(B::zeros(0))),

            Val::Symbolic(from) => {
                let sliced = $solver.fresh();
                // As from is symbolic we need to use bvlshr to do a
                // left shift before extracting between length - 1 to
                // 0. We therefore need to make from the correct
                // length so the bvlshr is type-correct.
                let shift = if $bits_length > 128 {
                    Exp::ZeroExtend($bits_length - 128, Box::new(Exp::Var(from)))
                } else if $bits_length < 128 {
                    Exp::Extract($bits_length - 1, 0, Box::new(Exp::Var(from)))
                } else {
                    Exp::Var(from)
                };
                $solver.add(Def::DefineConst(
                    sliced,
                    Exp::Extract($slice_length as u32 - 1, 0, Box::new(Exp::Bvlshr(Box::new($bits), Box::new(shift)))),
                ));
                Ok(Val::Symbolic(sliced))
            }

            Val::I128(from) => {
                let sliced = $solver.fresh();
                if from == 0 && ($slice_length as u32) == $bits_length {
                    $solver.add(Def::DefineConst(sliced, $bits))
                } else {
                    $solver.add(Def::DefineConst(
                        sliced,
                        Exp::Extract((from + $slice_length - 1) as u32, from as u32, Box::new($bits)),
                    ))
                }
                Ok(Val::Symbolic(sliced))
            }

            Val::I64(from) => {
                let sliced = $solver.fresh();
                if from == 0 && ($slice_length as u32) == $bits_length {
                    $solver.add(Def::DefineConst(sliced, $bits))
                } else {
                    $solver.add(Def::DefineConst(
                        sliced,
                        Exp::Extract((from as i128 + $slice_length - 1) as u32, from as u32, Box::new($bits)),
                    ))
                }
                Ok(Val::Symbolic(sliced))
            }

            _ => Err(ExecError::Type(format!("slice! {:?}", &$from), $info)),
        }
    }};
}

fn mixed_bits_slice<B: BV>(
    segments: &[BitsSegment<B>],
    bits_length: u32,
    from: u32,
    length: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let mut remaining = bits_length;
    let mut new_segments = vec![];
    let to = from + length;
    for segment in segments {
        let segment_length = segment_length(segment, solver, info)?;
        let segment_bottom = remaining - segment_length;
        if to > segment_bottom {
            if from >= remaining {
                break;
            }
            if to >= remaining && segment_bottom >= from {
                new_segments.push(segment.clone());
            } else {
                let segment_to = min(segment_length, to - segment_bottom) - 1;
                let segment_from = if segment_bottom >= from { 0 } else { from - segment_bottom };
                let new_segment = match segment {
                    BitsSegment::Symbolic(v) => BitsSegment::Symbolic(
                        solver.define_const(Exp::Extract(segment_to, segment_from, Box::new(Exp::Var(*v))), info),
                    ),
                    BitsSegment::Concrete(bv) => BitsSegment::Concrete(
                        bv.extract(segment_to, segment_from)
                            .ok_or_else(|| ExecError::Unreachable("op_slice MixedBits Concrete extract".to_string()))?,
                    ),
                };
                new_segments.push(new_segment);
            }
        }
        remaining -= segment_length;
    }
    match new_segments[..] {
        [BitsSegment::Symbolic(v)] => Ok(Val::Symbolic(v)),
        [BitsSegment::Concrete(bv)] => Ok(Val::Bits(bv)),
        _ => Ok(Val::MixedBits(new_segments)),
    }
}

pub(crate) fn op_slice<B: BV>(
    bits: Val<B>,
    from: Val<B>,
    length: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits_length = length_bits(&bits, solver, info)?;
    match bits {
        Val::Symbolic(bits) => slice!(bits_length, Exp::Var(bits), from, length as i128, solver, info),
        Val::Bits(bits) => match from {
            Val::I64(from) => match bits.slice(from as u32, length) {
                Some(bits) => Ok(Val::Bits(bits)),
                None => Err(ExecError::Type("op_slice (can't slice)".to_string(), info)),
            },
            _ if bits.is_zero() => Ok(Val::Bits(B::zeros(bits_length))),
            _ => slice!(bits_length, smt_sbits(bits), from, length as i128, solver, info),
        },
        Val::MixedBits(ref segments) => match from {
            Val::I64(from) => mixed_bits_slice(segments, bits_length, from as u32, length, solver, info),
            _ => op_slice(replace_mixed_bits(bits, solver, info)?, from, length, solver, info),
        },
        _ => Err(ExecError::Type(format!("op_slice {:?}", &bits), info)),
    }
}

fn slice_internal<B: BV>(
    bits: Val<B>,
    from: Val<B>,
    length: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bits_length = length_bits(&bits, solver, info)?;
    match length {
        Val::I128(length) => match bits {
            Val::Symbolic(bits) => slice!(bits_length, Exp::Var(bits), from, length, solver, info),
            Val::Bits(bits) => match from {
                Val::I128(from) => match bits.slice(from as u32, length as u32) {
                    Some(bits) => Ok(Val::Bits(bits)),
                    None => {
                        // Out-of-range slices shouldn't happen in IR from well-typed Sail, but linearization can
                        // produce them (although the result will be thrown away).  This should match the semantics
                        // of the symbolic case but isn't tested because the results aren't used.
                        match bits.shiftr(from).slice(0, length as u32) {
                            Some(bits) => Ok(Val::Bits(bits)),
                            None => Err(ExecError::Type(
                                format!("slice_internal (cannot slice) {:?} {:?}", &from, &length),
                                info,
                            )),
                        }
                    }
                },
                _ if bits.is_zero() => Ok(Val::Bits(B::zeros(bits_length))),
                _ => slice!(bits_length, smt_sbits(bits), from, length, solver, info),
            },
            Val::MixedBits(ref segments) => match from {
                Val::I128(from) => mixed_bits_slice(segments, bits_length, from as u32, length as u32, solver, info),
                _ => {
                    let bits_smt = mixed_bits_to_smt(bits, solver, info)?;
                    slice!(bits_length, bits_smt, from, length, solver, info)
                }
            },
            _ => Err(ExecError::Type(format!("slice_internal {:?}", &bits), info)),
        },
        Val::Symbolic(_) => Err(ExecError::SymbolicLength("slice_internal", info)),
        _ => Err(ExecError::Type(format!("slice_internal {:?}", &length), info)),
    }
}

fn slice<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    slice_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)
}

pub fn subrange_internal<B: BV>(
    bits: Val<B>,
    high: Val<B>,
    low: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (bits, high, low) {
        (Val::Symbolic(bits), Val::I128(high), Val::I128(low)) => {
            solver.define_const(Exp::Extract(high as u32, low as u32, Box::new(Exp::Var(bits))), info).into()
        }
        (Val::Bits(bits), Val::I128(high), Val::I128(low)) => match bits.extract(high as u32, low as u32) {
            Some(bits) => Ok(Val::Bits(bits)),
            None => Err(ExecError::Type(
                format!("subrange_internal (cannot extract) {:?} {:?} {:?}", &bits, &high, &low),
                info,
            )),
        },
        (Val::MixedBits(ref segments), Val::I128(high), Val::I128(low)) => {
            let bits_length = segments_length(segments, solver, info)?;
            mixed_bits_slice(segments, bits_length, low as u32, (high - low + 1) as u32, solver, info)
        }
        (_, _, Val::Symbolic(_)) => Err(ExecError::SymbolicLength("subrange_internal", info)),
        (_, Val::Symbolic(_), _) => Err(ExecError::SymbolicLength("subrange_internal", info)),
        (bits, high, low) => {
            Err(ExecError::Type(format!("subrange_internal {:?} {:?} {:?}", &bits, &high, &low), info))
        }
    }
}

fn subrange<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    subrange_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)
}

fn sail_truncate<B: BV>(
    bits: Val<B>,
    len: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    slice_internal(bits, Val::I128(0), len, solver, info)
}

fn sail_truncate_lsb<B: BV>(
    bits: Val<B>,
    len: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (bits, len) {
        (Val::Bits(bits), Val::I128(len)) => match bits.truncate_lsb(len) {
            Some(truncated) => Ok(Val::Bits(truncated)),
            None => Err(ExecError::Type(format!("sail_truncateLSB (cannot truncate) {:?} {:?}", &bits, &len), info)),
        },
        (Val::Symbolic(bits), Val::I128(len)) => {
            if len == 0 {
                Ok(Val::Bits(B::new(0, 0)))
            } else if let Some(orig_len) = solver.length(bits) {
                let low = orig_len - (len as u32);
                solver.define_const(Exp::Extract(orig_len - 1, low, Box::new(Exp::Var(bits))), info).into()
            } else {
                Err(ExecError::Type(format!("sail_truncateLSB (invalid length) {:?} {:?}", &bits, &len), info))
            }
        }
        (Val::MixedBits(ref segments), Val::I128(len)) => {
            let bits_length = segments_length(segments, solver, info)?;
            mixed_bits_slice(segments, bits_length, bits_length - len as u32, len as u32, solver, info)
        }
        (_, Val::Symbolic(_)) => Err(ExecError::SymbolicLength("sail_truncateLSB", info)),
        (bits, len) => Err(ExecError::Type(format!("sail_truncateLSB {:?} {:?}", &bits, &len), info)),
    }
}

fn sail_unsigned<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => Ok(Val::I128(bits.unsigned())),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => {
                assert!(length < 128);
                solver.define_const(Exp::ZeroExtend(128 - length, Box::new(Exp::Var(bits))), info).into()
            }
            None => Err(ExecError::Type(format!("sail_unsigned (solver cannot determine length) {:?}", &bits), info)),
        },
        _ => Err(ExecError::Type(format!("sail_unsigned {:?}", &bits), info)),
    }
}

fn sail_signed<B: BV>(bits: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bits = replace_mixed_bits(bits, solver, info)?;
    match bits {
        Val::Bits(bits) => Ok(Val::I128(bits.signed())),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => {
                assert!(length < 128);
                solver.define_const(Exp::SignExtend(128 - length, Box::new(Exp::Var(bits))), info).into()
            }
            None => Err(ExecError::Type(format!("sail_signed (solver cannot determine length) {:?}", &bits), info)),
        },
        _ => Err(ExecError::Type(format!("sail_signed {:?}", &bits), info)),
    }
}

fn shiftr<B: BV>(bits: Val<B>, shift: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I128) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    match (bits, shift) {
        (Val::Symbolic(x), Val::Symbolic(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(y)))
                } else {
                    Exp::Var(y)
                };
                solver.define_const(Exp::Bvlshr(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("shiftr {:?} {:?}", &x, &y), info)),
        },
        (Val::Symbolic(x), Val::I128(0)) => Ok(Val::Symbolic(x)),
        (Val::Symbolic(x), Val::I128(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(y)))
                } else {
                    smt_i128(y)
                };
                solver.define_const(Exp::Bvlshr(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("shiftr {:?} {:?}", &x, &y), info)),
        },
        (Val::Bits(x), Val::Symbolic(y)) => solver
            .define_const(
                Exp::Bvlshr(Box::new(smt_sbits(x)), Box::new(Exp::Extract(x.len() - 1, 0, Box::new(Exp::Var(y))))),
                info,
            )
            .into(),
        (Val::Bits(x), Val::I128(y)) => Ok(Val::Bits(x.shiftr(y))),
        (bits, shift) => Err(ExecError::Type(format!("shiftr {:?} {:?}", &bits, &shift), info)),
    }
}

fn arith_shiftr<B: BV>(
    bits: Val<B>,
    shift: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I128) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    match (bits, shift) {
        (Val::Symbolic(x), Val::Symbolic(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(y)))
                } else {
                    Exp::Var(y)
                };
                solver.define_const(Exp::Bvashr(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("arith_shiftr {:?} {:?}", &x, &y), info)),
        },
        (Val::Symbolic(x), Val::I128(0)) => Ok(Val::Symbolic(x)),
        (Val::Symbolic(x), Val::I128(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(y)))
                } else {
                    smt_i128(y)
                };
                solver.define_const(Exp::Bvashr(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("arith_shiftr {:?} {:?}", &x, &y), info)),
        },
        (Val::Bits(x), Val::Symbolic(y)) => solver
            .define_const(
                Exp::Bvashr(Box::new(smt_sbits(x)), Box::new(Exp::Extract(x.len() - 1, 0, Box::new(Exp::Var(y))))),
                info,
            )
            .into(),
        (Val::Bits(x), Val::I128(y)) => Ok(Val::Bits(x.arith_shiftr(y))),
        (bits, shift) => Err(ExecError::Type(format!("arith_shiftr {:?} {:?}", &bits, &shift), info)),
    }
}

fn shiftl<B: BV>(bits: Val<B>, len: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I128) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    match (bits, len) {
        (Val::Symbolic(x), Val::Symbolic(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(y)))
                } else {
                    Exp::Var(y)
                };
                solver.define_const(Exp::Bvshl(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("shiftl {:?} {:?}", &x, &y), info)),
        },
        (Val::Symbolic(x), Val::I128(0)) => Ok(Val::Symbolic(x)),
        (Val::Symbolic(x), Val::I128(y)) => match solver.length(x) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(y)))
                } else {
                    smt_i128(y)
                };
                solver.define_const(Exp::Bvshl(Box::new(Exp::Var(x)), Box::new(shift)), info).into()
            }
            None => Err(ExecError::Type(format!("shiftl {:?} {:?}", &x, &y), info)),
        },
        (Val::Bits(x), Val::Symbolic(y)) => solver
            .define_const(
                Exp::Bvshl(Box::new(smt_sbits(x)), Box::new(Exp::Extract(x.len() - 1, 0, Box::new(Exp::Var(y))))),
                info,
            )
            .into(),
        (Val::Bits(x), Val::I128(y)) => Ok(Val::Bits(x.shiftl(y))),
        (bits, len) => Err(ExecError::Type(format!("shiftl {:?} {:?}", &bits, &len), info)),
    }
}

pub fn shift_bits_right<B: BV>(
    bits: Val<B>,
    shift: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, Bits) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    let bits_len = length_bits(&bits, solver, info)?;
    let shift = replace_mixed_bits(shift, solver, info)?;
    let shift_len = length_bits(&shift, solver, info)?;
    match (&bits, &shift) {
        (Val::Symbolic(_), Val::Symbolic(_)) | (Val::Bits(_), Val::Symbolic(_)) | (Val::Symbolic(_), Val::Bits(_)) => {
            let shift = if bits_len < shift_len {
                Exp::Extract(bits_len - 1, 0, Box::new(smt_value(&shift, info)?))
            } else if bits_len > shift_len {
                Exp::ZeroExtend(bits_len - shift_len, Box::new(smt_value(&shift, info)?))
            } else {
                smt_value(&shift, info)?
            };
            solver.define_const(Exp::Bvlshr(Box::new(smt_value(&bits, info)?), Box::new(shift)), info).into()
        }
        (Val::Bits(x), Val::Bits(y)) => {
            let shift: u64 = (*y).try_into()?;
            Ok(Val::Bits(x.shiftr(shift as i128)))
        }
        (_, _) => Err(ExecError::Type(format!("shift_bits_right {:?} {:?}", &bits, &shift), info)),
    }
}

pub fn shift_bits_left<B: BV>(
    bits: Val<B>,
    shift: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, Bits) explicitly, if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    let bits_len = length_bits(&bits, solver, info)?;
    let shift = replace_mixed_bits(shift, solver, info)?;
    let shift_len = length_bits(&shift, solver, info)?;
    match (&bits, &shift) {
        (Val::Symbolic(_), Val::Symbolic(_)) | (Val::Bits(_), Val::Symbolic(_)) | (Val::Symbolic(_), Val::Bits(_)) => {
            let shift = if bits_len < shift_len {
                Exp::Extract(bits_len - 1, 0, Box::new(smt_value(&shift, info)?))
            } else if bits_len > shift_len {
                Exp::ZeroExtend(bits_len - shift_len, Box::new(smt_value(&shift, info)?))
            } else {
                smt_value(&shift, info)?
            };
            solver.define_const(Exp::Bvshl(Box::new(smt_value(&bits, info)?), Box::new(shift)), info).into()
        }
        (Val::Bits(x), Val::Bits(y)) => {
            let shift: u64 = (*y).try_into()?;
            Ok(Val::Bits(x.shiftl(shift as i128)))
        }
        (_, _) => Err(ExecError::Type(format!("shift_bits_left {:?} {:?}", &bits, &shift), info)),
    }
}

pub(crate) fn append<B: BV>(
    lhs: Val<B>,
    rhs: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            solver.define_const(Exp::Concat(Box::new(Exp::Var(x)), Box::new(Exp::Var(y))), info).into()
        }
        (Val::Symbolic(x), Val::Bits(y)) => {
            if y.len() == 0 {
                solver.define_const(Exp::Var(x), info).into()
            } else {
                solver.define_const(Exp::Concat(Box::new(Exp::Var(x)), Box::new(smt_sbits(y))), info).into()
            }
        }
        (Val::Bits(x), Val::Symbolic(y)) => {
            if x.len() == 0 {
                solver.define_const(Exp::Var(y), info).into()
            } else {
                solver.define_const(Exp::Concat(Box::new(smt_sbits(x)), Box::new(Exp::Var(y))), info).into()
            }
        }
        (Val::Bits(x), Val::Bits(y)) => match x.append(y) {
            Some(z) => Ok(Val::Bits(z)),
            None => solver.define_const(Exp::Concat(Box::new(smt_sbits(x)), Box::new(smt_sbits(y))), info).into(),
        },
        (Val::MixedBits(mut segments), Val::Symbolic(v)) => {
            segments.push(BitsSegment::Symbolic(v));
            Ok(Val::MixedBits(segments))
        }
        (Val::MixedBits(mut segments), Val::Bits(bv)) => {
            segments.push(BitsSegment::Concrete(bv));
            Ok(Val::MixedBits(segments))
        }
        (Val::MixedBits(mut segments_l), Val::MixedBits(mut segments_r)) => {
            segments_l.append(&mut segments_r);
            Ok(Val::MixedBits(segments_l))
        }
        (Val::Symbolic(v), Val::MixedBits(mut segments)) => {
            segments.insert(0, BitsSegment::Symbolic(v));
            Ok(Val::MixedBits(segments))
        }
        (Val::Bits(bv), Val::MixedBits(mut segments)) => {
            segments.insert(0, BitsSegment::Concrete(bv));
            Ok(Val::MixedBits(segments))
        }
        (lhs, rhs) => Err(ExecError::Type(format!("append {:?} {:?}", &lhs, &rhs), info)),
    }
}

fn segment_for_bit<B: BV>(
    segments: &[BitsSegment<B>],
    index: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(Val<B>, Val<B>), ExecError> {
    let mut segment_from = segments_length(segments, solver, info)?;
    for segment in segments {
        let segment_length = segment_length(segment, solver, info)?;
        segment_from -= segment_length;
        if index >= segment_from {
            return Ok((segment.into(), Val::I128((index - segment_from) as i128)));
        }
    }
    Err(ExecError::OutOfBounds("vector_access"))
}

pub(crate) fn vector_access<B: BV>(
    vec: Val<B>,
    n: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let (vec, n) = match (vec, n) {
        (Val::MixedBits(segments), Val::I128(n)) => segment_for_bit(&segments, n as u32, solver, info)?,
        (vec, n) => (replace_mixed_bits(vec, solver, info)?, n),
    };

    match (vec, n) {
        (Val::Symbolic(bits), Val::Symbolic(n)) => match solver.length(bits) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(n)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(n)))
                } else {
                    Exp::Var(n)
                };
                solver
                    .define_const(
                        Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(Exp::Var(bits)), Box::new(shift)))),
                        info,
                    )
                    .into()
            }
            None => Err(ExecError::Type(format!("vector_access {:?} {:?}", &bits, &n), info)),
        },
        (Val::Symbolic(bits), Val::I128(n)) => match solver.length(bits) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(n)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(n)))
                } else {
                    smt_i128(n)
                };
                solver
                    .define_const(
                        Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(Exp::Var(bits)), Box::new(shift)))),
                        info,
                    )
                    .into()
            }
            None => Err(ExecError::Type(format!("vector_access {:?} {:?}", &bits, &n), info)),
        },
        (Val::Bits(bits), Val::Symbolic(n)) => {
            let shift = Exp::Extract(bits.len() - 1, 0, Box::new(Exp::Var(n)));
            solver
                .define_const(
                    Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(smt_sbits(bits)), Box::new(shift)))),
                    info,
                )
                .into()
        }
        (Val::Bits(bits), Val::I128(n)) => match bits.slice(n as u32, 1) {
            Some(bit) => Ok(Val::Bits(bit)),
            None => Err(ExecError::Type(format!("vector_access {:?} {:?}", &bits, &n), info)),
        },
        (Val::Vector(vec), Val::I128(n)) => match vec.get(n as usize) {
            Some(elem) => Ok(elem.clone()),
            None => Err(ExecError::OutOfBounds("vector_access")),
        },
        (Val::Vector(vec), Val::Symbolic(n)) => {
            let mut it = vec.iter().enumerate().rev();
            if let Some((_, last_item)) = it.next() {
                let mut exp = smt_value(last_item, info)?;
                for (i, item) in it {
                    exp = Exp::Ite(
                        Box::new(Exp::Eq(Box::new(Exp::Var(n)), Box::new(bits64(i as u64, 128)))),
                        Box::new(smt_value(item, info)?),
                        Box::new(exp),
                    );
                }
                let var = solver.fresh();
                solver.add(Def::DefineConst(var, exp));
                Ok(Val::Symbolic(var))
            } else {
                Err(ExecError::Type(format!("vector_access {:?} {:?}", &vec, &n), info))
            }
        }
        (vec, n) => Err(ExecError::Type(format!("vector_access {:?} {:?}", &vec, &n), info)),
    }
}

/// The set_slice! macro implements the Sail set_slice builtin for any
/// combination of symbolic or concrete operands, with the result
/// always being symbolic. The argument order is the same as the Sail
/// function it implements, plus the solver as a final argument.
macro_rules! set_slice {
    ($bits_length: expr, $update_length: ident, $bits: expr, $n: expr, $update: expr, $solver: ident, $info: ident) => {
        if $bits_length == 0 {
            Ok(Val::Bits(B::zeros(0)))
        } else if $update_length == 0 {
            $solver.define_const($bits, $info).into()
        } else {
            let mask_lower = smt_mask_lower($bits_length as usize, $update_length as usize);
            let update = if $bits_length == $update_length {
                $update
            } else {
                Exp::ZeroExtend($bits_length - $update_length, Box::new($update))
            };
            let shift = if $bits_length < 128 {
                Exp::Extract($bits_length - 1, 0, Box::new($n))
            } else if $bits_length > 128 {
                Exp::ZeroExtend($bits_length - 128, Box::new($n))
            } else {
                $n
            };
            let sliced = $solver.fresh();
            $solver.add(Def::DefineConst(
                sliced,
                Exp::Bvor(
                    Box::new(Exp::Bvand(
                        Box::new($bits),
                        Box::new(Exp::Bvnot(Box::new(Exp::Bvshl(Box::new(mask_lower), Box::new(shift.clone()))))),
                    )),
                    Box::new(Exp::Bvshl(Box::new(update), Box::new(shift))),
                ),
            ));
            Ok(Val::Symbolic(sliced))
        }
    };
}

/// A special case of set_slice! for when $n == 0, and therefore no shift needs to be applied.
macro_rules! set_slice_n0 {
    ($bits_length: expr, $update_length: ident, $bits: expr, $update: expr, $solver: ident, $info: ident) => {
        if $bits_length == 0 {
            Ok(Val::Bits(B::zeros(0)))
        } else if $update_length == 0 {
            $solver.define_const($bits, $info).into()
        } else {
            let mask_lower = smt_mask_lower($bits_length as usize, $update_length as usize);
            let update = if $bits_length == $update_length {
                $update
            } else {
                Exp::ZeroExtend($bits_length - $update_length, Box::new($update))
            };
            let sliced = $solver.fresh();
            $solver.add(Def::DefineConst(
                sliced,
                Exp::Bvor(
                    Box::new(Exp::Bvand(Box::new($bits), Box::new(Exp::Bvnot(Box::new(mask_lower))))),
                    Box::new(update),
                ),
            ));
            Ok(Val::Symbolic(sliced))
        }
    };
}

pub fn set_slice_internal<B: BV>(
    bits: Val<B>,
    n: Val<B>,
    update: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I128, _) if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    let update = replace_mixed_bits(update, solver, info)?;
    let bits_length = length_bits(&bits, solver, info)?;
    let update_length = length_bits(&update, solver, info)?;
    match (bits, n, update) {
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Symbolic(bits), Val::I128(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, Exp::Var(bits), Exp::Var(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, Exp::Var(bits), smt_i128(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Symbolic(bits), Val::I128(n), Val::Bits(update)) => {
            if n == 0 {
                if bits_length == update_length {
                    Ok(Val::Bits(update))
                } else {
                    set_slice_n0!(bits_length, update_length, Exp::Var(bits), smt_sbits(update), solver, info)
                }
            } else {
                set_slice!(bits_length, update_length, Exp::Var(bits), smt_i128(n), smt_sbits(update), solver, info)
            }
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Bits(bits), Val::I128(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, smt_sbits(bits), Exp::Var(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, smt_sbits(bits), smt_i128(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Bits(bits), Val::I128(n), Val::Bits(update)) => Ok(Val::Bits(bits.set_slice(n as u32, update))),
        (bits, n, update) => Err(ExecError::Type(format!("set_slice {:?} {:?} {:?}", &bits, &n, &update), info)),
    }
}

fn set_slice<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // set_slice Sail builtin takes 2 additional integer parameters
    // for the bitvector lengths, which we can ignore.
    set_slice_internal(args[2].clone(), args[3].clone(), args[4].clone(), solver, info)
}

fn set_slice_int_internal<B: BV>(
    int: Val<B>,
    n: Val<B>,
    update: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let update = replace_mixed_bits(update, solver, info)?;
    let update_length = length_bits(&update, solver, info)?;
    match (int, n, update) {
        (Val::Symbolic(int), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(128, update_length, Exp::Var(int), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Symbolic(int), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(128, update_length, Exp::Var(int), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Symbolic(int), Val::I128(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(128, update_length, Exp::Var(int), Exp::Var(update), solver, info)
            } else {
                set_slice!(128, update_length, Exp::Var(int), smt_i128(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Symbolic(int), Val::I128(n), Val::Bits(update)) => {
            if n == 0 {
                set_slice_n0!(128, update_length, Exp::Var(int), smt_sbits(update), solver, info)
            } else {
                set_slice!(128, update_length, Exp::Var(int), smt_i128(n), smt_sbits(update), solver, info)
            }
        }
        (Val::I128(int), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(128, update_length, smt_i128(int), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::I128(int), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(128, update_length, smt_i128(int), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::I128(int), Val::I128(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(128, update_length, smt_i128(int), Exp::Var(update), solver, info)
            } else {
                set_slice!(128, update_length, smt_i128(int), smt_i128(n), Exp::Var(update), solver, info)
            }
        }
        (Val::I128(int), Val::I128(n), Val::Bits(update)) => Ok(Val::I128(B::set_slice_int(int, n as u32, update))),
        (int, n, update) => Err(ExecError::Type(format!("set_slice_int {:?} {:?} {:?}", &int, &n, &update), info)),
    }
}

fn set_slice_int<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // set_slice_int Sail builtin takes 1 additional integer parameter for the bitvector length,
    // which we can ignore.
    set_slice_int_internal(args[1].clone(), args[2].clone(), args[3].clone(), solver, info)
}

/// op_set_slice is just set_slice_internal with 64-bit integers rather than 128-bit.
pub(crate) fn op_set_slice<B: BV>(
    bits: Val<B>,
    n: Val<B>,
    update: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support (MixedBits, I64, _) directly if necessary
    let bits = replace_mixed_bits(bits, solver, info)?;
    let update = replace_mixed_bits(update, solver, info)?;
    let bits_length = length_bits(&bits, solver, info)?;
    let update_length = length_bits(&update, solver, info)?;
    match (bits, n, update) {
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Symbolic(bits), Val::I64(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, Exp::Var(bits), Exp::Var(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, Exp::Var(bits), smt_i64(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Symbolic(bits), Val::I64(n), Val::Bits(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, Exp::Var(bits), smt_sbits(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, Exp::Var(bits), smt_i64(n), smt_sbits(update), solver, info)
            }
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), Exp::Var(update), solver, info)
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), smt_sbits(update), solver, info)
        }
        (Val::Bits(bits), Val::I64(n), Val::Symbolic(update)) => {
            if n == 0 {
                set_slice_n0!(bits_length, update_length, smt_sbits(bits), Exp::Var(update), solver, info)
            } else {
                set_slice!(bits_length, update_length, smt_sbits(bits), smt_i64(n), Exp::Var(update), solver, info)
            }
        }
        (Val::Bits(bits), Val::I64(n), Val::Bits(update)) => Ok(Val::Bits(bits.set_slice(n as u32, update))),
        (bits, n, update) => Err(ExecError::Type(format!("set_slice {:?} {:?} {:?}", &bits, &n, &update), info)),
    }
}

/// `vector_update` is a special case of `set_slice` where the update
/// is a bitvector of length 1. It can also update ordinary (non bit-)
/// vectors.
pub fn vector_update<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    // We could support some MixedBits cases directly, if necessary
    let arg0 = args[0].clone();
    let arg0 = replace_mixed_bits(arg0, solver, info)?;
    match arg0 {
        Val::Vector(mut vec) => match args[1] {
            Val::I128(n) => {
                vec[n as usize] = args[2].clone();
                Ok(Val::Vector(vec))
            }
            Val::I64(n) => {
                vec[n as usize] = args[2].clone();
                Ok(Val::Vector(vec))
            }
            Val::Symbolic(n) => {
                for (i, item) in vec.iter_mut().enumerate() {
                    let var = solver.fresh();
                    solver.add(Def::DefineConst(
                        var,
                        Exp::Ite(
                            Box::new(Exp::Eq(Box::new(Exp::Var(n)), Box::new(bits64(i as u64, 128)))),
                            Box::new(smt_value(&args[2], info)?),
                            Box::new(smt_value(item, info)?),
                        ),
                    ));
                    *item = Val::Symbolic(var);
                }
                Ok(Val::Vector(vec))
            }
            _ => {
                eprintln!("{:?}", args);
                Err(ExecError::Type(format!("vector_update (index) {:?}", &args[1]), info))
            }
        },
        Val::Bits(_) => {
            // If the argument is a bitvector then `vector_update` is a special case of `set_slice`
            // where the update is a bitvector of length 1
            set_slice_internal(arg0, args[1].clone(), args[2].clone(), solver, info)
        }
        Val::Symbolic(v) if solver.is_bitvector(v) => {
            set_slice_internal(arg0, args[1].clone(), args[2].clone(), solver, info)
        }
        _ => Err(ExecError::Type(format!("vector_update {:?}", &arg0), info)),
    }
}

fn vector_update_subrange<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    set_slice_internal(args[0].clone(), args[2].clone(), args[3].clone(), solver, info)
}

fn undefined_vector<B: BV>(len: Val<B>, elem: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    if let Val::I128(len) = len {
        if let Ok(len) = usize::try_from(len) {
            Ok(Val::Vector(vec![elem; len]))
        } else {
            Err(ExecError::Overflow)
        }
    } else {
        Err(ExecError::SymbolicLength("undefined_vector", info))
    }
}

fn bitvector_update<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    op_set_slice(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)
}

fn get_slice_int_internal<B: BV>(
    length: Val<B>,
    n: Val<B>,
    from: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match length {
        Val::I128(length) => match n {
            Val::Symbolic(n) => slice!(128, Exp::Var(n), from, length, solver, info),
            Val::I128(n) => match from {
                Val::I128(from) if length <= B::MAX_WIDTH as i128 => {
                    Ok(Val::Bits(B::get_slice_int(length as u32, n, from as u32)))
                }
                _ => slice!(128, smt_i128(n), from, length, solver, info),
            },
            _ => Err(ExecError::Type(format!("get_slice_int {:?}", &length), info)),
        },
        Val::Symbolic(_) => Err(ExecError::SymbolicLength("get_slice_int", info)),
        _ => Err(ExecError::Type(format!("get_slice_int length is {:?}", &length), info)),
    }
}

fn get_slice_int<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    get_slice_int_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver, info)
}

fn unit_noop<B: BV>(
    _: Vec<Val<B>>,
    _: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn unimplemented<B: BV>(
    _: Vec<Val<B>>,
    _: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    Err(ExecError::Unimplemented)
}

fn eq_string<B: BV>(lhs: Val<B>, rhs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::String(lhs), Val::String(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (lhs, rhs) => Err(ExecError::Type(format!("eq_string {:?} {:?}", &lhs, &rhs), info)),
    }
}

fn concat_str<B: BV>(lhs: Val<B>, rhs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::String(lhs), Val::String(rhs)) => Ok(Val::String(format!("{}{}", lhs, rhs))),
        (lhs, rhs) => Err(ExecError::Type(format!("concat_str {:?} {:?}", &lhs, &rhs), info)),
    }
}

fn hex_str<B: BV>(n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match n {
        Val::I128(n) => Ok(Val::String(format!("0x{:x}", n))),
        Val::Symbolic(v) => Ok(Val::String(format!("0x[{}]", v))),
        _ => Err(ExecError::Type(format!("hex_str {:?}", &n), info)),
    }
}

fn dec_str<B: BV>(n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match n {
        Val::I128(n) => Ok(Val::String(format!("{}", n))),
        Val::Symbolic(v) => Ok(Val::String(format!("[{}]", v))),
        _ => Err(ExecError::Type(format!("dec_str {:?}", &n), info)),
    }
}

// Strings can never be symbolic
fn undefined_string<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Poison)
}

fn string_to_i128<B: BV>(s: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    if let Val::String(s) = s {
        if let Ok(n) = i128::from_str(&s) {
            Ok(Val::I128(n))
        } else {
            Err(ExecError::Overflow)
        }
    } else {
        Err(ExecError::Type(format!("%string->%int {:?}", &s), info))
    }
}

pub fn eq_anything<B: BV>(
    lhs: Val<B>,
    rhs: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (replace_mixed_bits(lhs, solver, info)?, replace_mixed_bits(rhs, solver, info)?) {
        (Val::Symbolic(lhs), Val::Symbolic(rhs)) => {
            solver.define_const(Exp::Eq(Box::new(Exp::Var(lhs)), Box::new(Exp::Var(rhs))), info).into()
        }
        (lhs, Val::Symbolic(rhs)) => {
            solver.define_const(Exp::Eq(Box::new(smt_value(&lhs, info)?), Box::new(Exp::Var(rhs))), info).into()
        }
        (Val::Symbolic(lhs), rhs) => {
            solver.define_const(Exp::Eq(Box::new(Exp::Var(lhs)), Box::new(smt_value(&rhs, info)?)), info).into()
        }

        (Val::Bits(lhs), Val::Bits(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::Enum(lhs), Val::Enum(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::Bool(lhs), Val::Bool(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::I128(lhs), Val::I128(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::I64(lhs), Val::I64(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (Val::Struct(lhs), Val::Struct(rhs)) => {
            let mut vars = vec![];
            for (k, lhs_v) in lhs {
                let rhs_v = match rhs.get(&k) {
                    Some(v) => v,
                    None => return Err(ExecError::Type("eq_anything None".to_string(), info)),
                };
                let result = eq_anything(lhs_v, rhs_v.clone(), solver, info)?;
                match result {
                    Val::Bool(true) => (),
                    Val::Bool(false) => return Ok(Val::Bool(false)),
                    Val::Symbolic(r) => vars.push(r),
                    _ => return Err(ExecError::Type(format!("eq_anything {:?}", &result), info)),
                }
            }
            match vars.pop() {
                None => Ok(Val::Bool(true)),
                Some(init) => {
                    let exp = vars
                        .iter()
                        .map(|v| Exp::Var(*v))
                        .fold(Exp::Var(init), |e1, e2| Exp::And(Box::new(e1), Box::new(e2)));
                    solver.define_const(exp, info).into()
                }
            }
        }
        (Val::Ctor(lhs_name, lhs_val), Val::Ctor(rhs_name, rhs_val)) => {
            if lhs_name == rhs_name {
                eq_anything(*lhs_val, *rhs_val, solver, info)
            } else {
                Ok(Val::Bool(false))
            }
        }
        (Val::Unit, Val::Unit) => Ok(Val::Bool(true)),

        (lhs, rhs) => Err(ExecError::Type(format!("eq_anything {:?} {:?}", &lhs, &rhs), info)),
    }
}

fn neq_anything<B: BV>(lhs: Val<B>, rhs: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (replace_mixed_bits(lhs, solver, info)?, replace_mixed_bits(rhs, solver, info)?) {
        (Val::Symbolic(lhs), Val::Symbolic(rhs)) => {
            solver.define_const(Exp::Neq(Box::new(Exp::Var(lhs)), Box::new(Exp::Var(rhs))), info).into()
        }
        (lhs, Val::Symbolic(rhs)) => {
            solver.define_const(Exp::Neq(Box::new(smt_value(&lhs, info)?), Box::new(Exp::Var(rhs))), info).into()
        }
        (Val::Symbolic(lhs), rhs) => {
            solver.define_const(Exp::Neq(Box::new(Exp::Var(lhs)), Box::new(smt_value(&rhs, info)?)), info).into()
        }

        (lhs, rhs) => not_bool(eq_anything(lhs, rhs, solver, info)?, solver, info),
    }
}

fn string_startswith<B: BV>(
    s: Val<B>,
    prefix: Val<B>,
    _: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (s, prefix) {
        (Val::String(s), Val::String(prefix)) => Ok(Val::Bool(s.starts_with(&prefix))),
        other => Err(ExecError::Type(format!("string_startswith {:?}", &other), info)),
    }
}

fn string_length<B: BV>(s: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    if let Val::String(s) = s {
        Ok(Val::I128(s.len() as i128))
    } else {
        Err(ExecError::Type(format!("string_length {:?}", &s), info))
    }
}

fn string_drop<B: BV>(s: Val<B>, n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (s, n) {
        (Val::String(s), Val::I128(n)) => Ok(Val::String(s.get((n as usize)..).unwrap_or("").to_string())),
        other => Err(ExecError::Type(format!("string_drop {:?}", &other), info)),
    }
}

fn string_take<B: BV>(s: Val<B>, n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (s, n) {
        (Val::String(s), Val::I128(n)) => Ok(Val::String(s.get(..(n as usize)).unwrap_or(&s).to_string())),
        other => Err(ExecError::Type(format!("string_take {:?}", &other), info)),
    }
}

fn string_of_segment<B: BV>(segment: &BitsSegment<B>) -> String {
    match segment {
        BitsSegment::Concrete(bv) => format!("{}", bv),
        BitsSegment::Symbolic(v) => format!("v{}", v),
    }
}

fn string_of_bits<B: BV>(bv: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match bv {
        Val::Bits(bv) => Ok(Val::String(format!("{}", bv))),
        Val::Symbolic(v) => Ok(Val::String(format!("v{}", v))),
        Val::MixedBits(segments) => {
            Ok(Val::String(segments.iter().map(|seg| string_of_segment::<B>(seg)).collect::<Vec<String>>().join(" ")))
        }
        other => Err(ExecError::Type(format!("string_of_bits {:?}", &other), info)),
    }
}

fn decimal_string_of_segment<B: BV>(segment: &BitsSegment<B>) -> String {
    match segment {
        BitsSegment::Concrete(bv) => format!("{}", bv),
        BitsSegment::Symbolic(v) => format!("v{}", v),
    }
}

fn decimal_string_of_bits<B: BV>(bv: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match bv {
        Val::Bits(bv) => Ok(Val::String(format!("{}", bv.signed()))),
        Val::Symbolic(v) => Ok(Val::String(format!("v{}", v))),
        Val::MixedBits(segments) => Ok(Val::String(
            segments.iter().map(|seg| decimal_string_of_segment::<B>(seg)).collect::<Vec<String>>().join(" "),
        )),
        other => Err(ExecError::Type(format!("decimal_string_of_bits {:?}", &other), info)),
    }
}

fn string_of_int<B: BV>(n: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match n {
        Val::I128(n) => Ok(Val::String(format!("{}", n))),
        Val::Symbolic(v) => Ok(Val::String(format!("v{}", v))),
        other => Err(ExecError::Type(format!("string_of_int {:?}", &other), info)),
    }
}

fn putchar<B: BV>(_c: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::I128(c) = c {
    //    eprintln!("Stdout: {}", char::from(c as u8))
    //}
    Ok(Val::Unit)
}

fn print<B: BV>(_message: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::String(message) = message {
    //    eprintln!("Stdout: {}", message)
    //}
    Ok(Val::Unit)
}

fn prerr<B: BV>(_message: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::String(message) = message {
    //    eprintln!("Stderr: {}", message)
    //}
    Ok(Val::Unit)
}

fn print_string<B: BV>(
    _prefix: Val<B>,
    _message: Val<B>,
    _: &mut Solver<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn prerr_string<B: BV>(
    _prefix: Val<B>,
    _message: Val<B>,
    _: &mut Solver<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn print_int<B: BV>(_prefix: Val<B>, _n: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn prerr_int<B: BV>(_prefix: Val<B>, _n: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn print_endline<B: BV>(_message: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn prerr_endline<B: BV>(_message: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn print_bits<B: BV>(_message: Val<B>, _bits: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::String(message) = message {
    //    eprintln!("Stdout: {}{:?}", message, bits)
    //}
    Ok(Val::Unit)
}

fn prerr_bits<B: BV>(_message: Val<B>, _bits: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    //if let Val::String(message) = message {
    //    eprintln!("Stderr: {}{:?}", message, bits)
    //}
    Ok(Val::Unit)
}

fn undefined_bitvector<B: BV>(sz: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    if let Val::I128(sz) = sz {
        solver.declare_const(Ty::BitVec(sz as u32), info).into()
    } else {
        Err(ExecError::Type(format!("undefined_bitvector {:?}", &sz), info))
    }
}

fn undefined_bit<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(Ty::BitVec(1), info).into()
}

fn undefined_bool<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(Ty::Bool, info).into()
}

fn undefined_int<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(Ty::BitVec(128), info).into()
}

fn undefined_nat<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let sym = solver.declare_const(Ty::BitVec(128), info);
    solver.add(Def::Assert(Exp::Bvsge(Box::new(Exp::Var(sym)), Box::new(smt_i128(0)))));
    Ok(Val::Symbolic(sym))
}

fn undefined_range<B: BV>(
    lo: Val<B>,
    hi: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let sym = solver.declare_const(Ty::BitVec(128), info);
    solver.add(Def::Assert(Exp::Bvsle(Box::new(smt_value(&lo, info)?), Box::new(Exp::Var(sym)))));
    solver.add(Def::Assert(Exp::Bvsle(Box::new(Exp::Var(sym)), Box::new(smt_value(&hi, info)?))));
    Ok(Val::Symbolic(sym))
}

fn undefined_unit<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn one_if<B: BV>(condition: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match condition {
        Val::Bool(true) => Ok(Val::Bits(B::BIT_ONE)),
        Val::Bool(false) => Ok(Val::Bits(B::BIT_ZERO)),
        Val::Symbolic(v) => solver
            .define_const(
                Exp::Ite(Box::new(Exp::Var(v)), Box::new(smt_sbits(B::BIT_ONE)), Box::new(smt_sbits(B::BIT_ZERO))),
                info,
            )
            .into(),
        _ => Err(ExecError::Type(format!("one_if {:?}", &condition), info)),
    }
}

fn zero_if<B: BV>(condition: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match condition {
        Val::Bool(true) => Ok(Val::Bits(B::BIT_ZERO)),
        Val::Bool(false) => Ok(Val::Bits(B::BIT_ONE)),
        Val::Symbolic(v) => solver
            .define_const(
                Exp::Ite(Box::new(Exp::Var(v)), Box::new(smt_sbits(B::BIT_ZERO)), Box::new(smt_sbits(B::BIT_ONE))),
                info,
            )
            .into(),
        other => Err(ExecError::Type(format!("one_if {:?}", &other), info)),
    }
}

fn cons<B: BV>(x: Val<B>, xs: Val<B>, _: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        /* TODO: Make this not a hack */
        Val::Poison => Ok(Val::List(vec![x])),
        Val::List(mut xs) => {
            xs.push(x);
            Ok(Val::List(xs))
        }
        _ => Err(ExecError::Type(format!("cons {:?}", &xs), info)),
    }
}

fn choice<B: BV>(xs: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match xs {
        Val::List(mut xs) if !xs.is_empty() => {
            let x = xs.pop().unwrap();
            ite_choice(&x, &xs, solver, info)
        }
        _ => Err(ExecError::Type(format!("choice {:?}", &xs), info)),
    }
}

fn read_mem<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[2].clone(), args[3].clone(), solver, false, ReadOpts::default())
}

fn read_mem_ifetch<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[2].clone(), args[3].clone(), solver, false, ReadOpts::ifetch())
}

fn read_mem_exclusive<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[2].clone(), args[3].clone(), solver, false, ReadOpts::exclusive())
}

fn read_memt<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory().read(args[0].clone(), args[1].clone(), args[2].clone(), solver, true, ReadOpts::default())
}

fn bad_read<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Err(ExecError::BadRead("spec-defined bad read"))
}

fn write_mem<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory_mut().write(args[0].clone(), args[2].clone(), args[4].clone(), solver, None, WriteOpts::default())
}

fn write_mem_exclusive<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory_mut().write(args[0].clone(), args[2].clone(), args[4].clone(), solver, None, WriteOpts::exclusive())
}

fn write_memt<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory_mut().write(
        args[0].clone(),
        args[1].clone(),
        args[3].clone(),
        solver,
        Some(args[4].clone()),
        WriteOpts::default(),
    )
}

fn write_tag<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.memory_mut().write_tag(args[0].clone(), args[1].clone(), args[2].clone(), solver)
}

fn bad_write<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Err(ExecError::BadWrite("spec-defined bad write"))
}

fn cycle_count<B: BV>(_: Val<B>, solver: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.cycle_count();
    Ok(Val::Unit)
}

fn get_cycle_count<B: BV>(_: Val<B>, solver: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::I128(solver.get_cycle_count()))
}

fn get_verbosity<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Bits(B::zeros(64)))
}

fn sleeping<B: BV>(_: Val<B>, _solver: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    // let sym = solver.fresh();
    // solver.add(Def::DeclareConst(sym, Ty::Bool));
    // solver.add_event(Event::Sleeping(sym));
    // Ok(Val::Symbolic(sym))
    Ok(Val::Bool(false))
}

fn wakeup_request<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn sleep_request<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

fn branch_announce<B: BV>(
    _: Val<B>,
    target: Val<B>,
    solver: &mut Solver<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    solver.add_event(Event::Branch { address: target });
    Ok(Val::Unit)
}

fn address_announce<B: BV>(
    _: Val<B>,
    address: Val<B>,
    solver: &mut Solver<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    solver.add_event(Event::AddressAnnounce { address });
    Ok(Val::Unit)
}

fn synchronize_registers<B: BV>(
    _: Vec<Val<B>>,
    _: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    frame.regs_mut().synchronize();
    Ok(Val::Unit)
}

fn elf_entry<B: BV>(
    _: Vec<Val<B>>,
    _: &mut Solver<B>,
    frame: &mut LocalFrame<B>,
    _: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match frame.lets().get(&ELF_ENTRY) {
        Some(UVal::Init(value)) => Ok(value.clone()),
        _ => Err(ExecError::NoElfEntry),
    }
}

fn monomorphize<B: BV>(val: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(val)
}

fn mark_register<B: BV>(r: Val<B>, mark: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    match (r, mark) {
        (Val::Ref(r), Val::String(mark)) => {
            solver.add_event(Event::MarkReg { regs: vec![r], mark });
            Ok(Val::Unit)
        }
        (r, mark) => Err(ExecError::Type(format!("mark_register {:?} {:?}", &r, &mark), info)),
    }
}

fn mark_register_pair_internal<B: BV>(
    r1: Val<B>,
    r2: Val<B>,
    mark: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (r1, r2, mark) {
        (Val::Ref(r1), Val::Ref(r2), Val::String(mark)) => {
            solver.add_event(Event::MarkReg { regs: vec![r1, r2], mark });
            Ok(Val::Unit)
        }
        (r1, r2, mark) => Err(ExecError::Type(format!("mark_register_pair {:?} {:?} {:?}", &r1, &r2, &mark), info)),
    }
}

fn mark_register_pair<B: BV>(
    mut args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() == 3 {
        let mark = args.pop().unwrap();
        let r2 = args.pop().unwrap();
        let r1 = args.pop().unwrap();
        mark_register_pair_internal(r1, r2, mark, solver, info)
    } else {
        Err(ExecError::Type("Incorrect number of arguments for mark_register_pair".to_string(), info))
    }
}

fn align_bits<B: BV>(
    bv: Val<B>,
    alignment: Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let bv_len = length_bits(&bv, solver, info)?;
    match (bv, alignment) {
        // Fast path for small bitvectors with power of two alignments
        (Val::Symbolic(bv), Val::I128(alignment)) if (bv_len <= 64) & ((alignment & (alignment - 1)) == 0) => {
            let mask = !B::new((alignment as u64) - 1, bv_len);
            solver.define_const(Exp::Bvand(Box::new(Exp::Var(bv)), Box::new(smt_sbits(mask))), info).into()
        }
        (bv, alignment) => {
            let x = sail_unsigned(bv, solver, info)?;
            let aligned_x = mult_int(alignment.clone(), udiv_int(x, alignment, solver, info)?, solver, info)?;
            get_slice_int_internal(Val::I128(bv_len as i128), aligned_x, Val::I128(0), solver, info)
        }
    }
}

/// Implement count leading zeros (clz) in the SMT solver as a binary
/// search, splitting on the midpoint of the bitvector.
fn smt_clz<B: BV>(bv: Sym, len: u32, solver: &mut Solver<B>, info: SourceLoc) -> Sym {
    if len == 1 {
        solver.define_const(
            Exp::Ite(
                Box::new(Exp::Eq(Box::new(Exp::Var(bv)), Box::new(smt_zeros(1)))),
                Box::new(smt_i128(1)),
                Box::new(smt_i128(0)),
            ),
            info,
        )
    } else {
        let low_len = len / 2;
        let top_len = len - low_len;

        let top = solver.define_const(Exp::Extract(len - 1, low_len, Box::new(Exp::Var(bv))), info);
        let low = solver.define_const(Exp::Extract(low_len - 1, 0, Box::new(Exp::Var(bv))), info);

        let top_bits_are_zero = Exp::Eq(Box::new(Exp::Var(top)), Box::new(smt_zeros(top_len as i128)));

        let top_clz = smt_clz(top, top_len, solver, info);
        let low_clz = smt_clz(low, low_len, solver, info);

        solver.define_const(
            Exp::Ite(
                Box::new(top_bits_are_zero),
                Box::new(Exp::Bvadd(Box::new(smt_i128(top_len as i128)), Box::new(Exp::Var(low_clz)))),
                Box::new(Exp::Var(top_clz)),
            ),
            info,
        )
    }
}

fn count_leading_zeros<B: BV>(bv: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let bv = replace_mixed_bits(bv, solver, info)?;
    match bv {
        Val::Bits(bv) => Ok(Val::I128(bv.leading_zeros() as i128)),
        Val::Symbolic(bv) => {
            if let Some(len) = solver.length(bv) {
                smt_clz(bv, len, solver, info).into()
            } else {
                Err(ExecError::Type("count_leading_zeros (solver could not determine length)".to_string(), info))
            }
        }
        _ => Err(ExecError::Type(format!("count_leading_zeros {:?}", &bv), info)),
    }
}

fn primop_ite<B: BV>(
    args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    ite(&args[0], &args[1], &args[2], solver, info)
}

pub fn unary_primops<B: BV>() -> HashMap<String, Unary<B>> {
    let mut primops = HashMap::new();
    primops.insert("%i64->%i".to_string(), i64_to_i128 as Unary<B>);
    primops.insert("%i->%i64".to_string(), i128_to_i64 as Unary<B>);
    primops.insert("%string->%i".to_string(), string_to_i128 as Unary<B>);
    primops.insert("bit_to_bool".to_string(), bit_to_bool as Unary<B>);
    primops.insert("assume".to_string(), assume as Unary<B>);
    primops.insert("not".to_string(), not_bool as Unary<B>);
    primops.insert("neg_int".to_string(), neg_int as Unary<B>);
    primops.insert("abs_int".to_string(), abs_int as Unary<B>);
    primops.insert("pow2".to_string(), pow2 as Unary<B>);
    primops.insert("not_bits".to_string(), not_bits as Unary<B>);
    primops.insert("length".to_string(), length as Unary<B>);
    primops.insert("zeros".to_string(), zeros as Unary<B>);
    primops.insert("ones".to_string(), ones as Unary<B>);
    primops.insert("sail_unsigned".to_string(), sail_unsigned as Unary<B>);
    primops.insert("sail_signed".to_string(), sail_signed as Unary<B>);
    primops.insert("sail_putchar".to_string(), putchar as Unary<B>);
    primops.insert("print".to_string(), print as Unary<B>);
    primops.insert("prerr".to_string(), prerr as Unary<B>);
    primops.insert("print_endline".to_string(), print_endline as Unary<B>);
    primops.insert("prerr_endline".to_string(), prerr_endline as Unary<B>);
    primops.insert("count_leading_zeros".to_string(), count_leading_zeros as Unary<B>);
    primops.insert("undefined_bitvector".to_string(), undefined_bitvector as Unary<B>);
    primops.insert("undefined_bit".to_string(), undefined_bit as Unary<B>);
    primops.insert("undefined_bool".to_string(), undefined_bool as Unary<B>);
    primops.insert("undefined_int".to_string(), undefined_int as Unary<B>);
    primops.insert("undefined_nat".to_string(), undefined_nat as Unary<B>);
    primops.insert("undefined_unit".to_string(), undefined_unit as Unary<B>);
    primops.insert("undefined_string".to_string(), undefined_string as Unary<B>);
    primops.insert("one_if".to_string(), one_if as Unary<B>);
    primops.insert("zero_if".to_string(), zero_if as Unary<B>);
    primops.insert("internal_pick".to_string(), choice as Unary<B>);
    primops.insert("bad_read".to_string(), bad_read as Unary<B>);
    primops.insert("bad_write".to_string(), bad_write as Unary<B>);
    primops.insert("hex_str".to_string(), hex_str as Unary<B>);
    primops.insert("dec_str".to_string(), dec_str as Unary<B>);
    primops.insert("string_length".to_string(), string_length as Unary<B>);
    primops.insert("string_of_bits".to_string(), string_of_bits as Unary<B>);
    primops.insert("decimal_string_of_bits".to_string(), decimal_string_of_bits as Unary<B>);
    primops.insert("string_of_int".to_string(), string_of_int as Unary<B>);
    primops.insert("cycle_count".to_string(), cycle_count as Unary<B>);
    primops.insert("get_cycle_count".to_string(), get_cycle_count as Unary<B>);
    primops.insert("sail_get_verbosity".to_string(), get_verbosity as Unary<B>);
    primops.insert("sleeping".to_string(), sleeping as Unary<B>);
    primops.insert("sleep_request".to_string(), sleep_request as Unary<B>);
    primops.insert("wakeup_request".to_string(), wakeup_request as Unary<B>);
    primops.insert("monomorphize".to_string(), monomorphize as Unary<B>);
    primops.extend(float::unary_primops());
    primops
}

pub fn binary_primops<B: BV>() -> HashMap<String, Binary<B>> {
    let mut primops = HashMap::new();
    primops.insert("optimistic_assert".to_string(), optimistic_assert as Binary<B>);
    primops.insert("pessimistic_assert".to_string(), pessimistic_assert as Binary<B>);
    primops.insert("and_bool".to_string(), and_bool as Binary<B>);
    primops.insert("strict_and_bool".to_string(), and_bool as Binary<B>);
    primops.insert("or_bool".to_string(), or_bool as Binary<B>);
    primops.insert("strict_or_bool".to_string(), or_bool as Binary<B>);
    primops.insert("eq_int".to_string(), eq_int as Binary<B>);
    primops.insert("eq_bool".to_string(), eq_bool as Binary<B>);
    primops.insert("lteq".to_string(), lteq_int as Binary<B>);
    primops.insert("gteq".to_string(), gteq_int as Binary<B>);
    primops.insert("lt".to_string(), lt_int as Binary<B>);
    primops.insert("gt".to_string(), gt_int as Binary<B>);
    primops.insert("add_int".to_string(), add_int as Binary<B>);
    primops.insert("sub_int".to_string(), sub_int as Binary<B>);
    primops.insert("sub_nat".to_string(), sub_nat as Binary<B>);
    primops.insert("mult_int".to_string(), mult_int as Binary<B>);
    primops.insert("tdiv_int".to_string(), tdiv_int as Binary<B>);
    primops.insert("tmod_int".to_string(), tmod_int as Binary<B>);
    primops.insert("ediv_int".to_string(), ediv_int as Binary<B>);
    primops.insert("emod_int".to_string(), emod_int as Binary<B>);
    primops.insert("pow_int".to_string(), pow_int as Binary<B>);
    primops.insert("shl_int".to_string(), shl_int as Binary<B>);
    primops.insert("shr_int".to_string(), shr_int as Binary<B>);
    primops.insert("shl_mach_int".to_string(), shl_mach_int as Binary<B>);
    primops.insert("shr_mach_int".to_string(), shr_mach_int as Binary<B>);
    primops.insert("max_int".to_string(), max_int as Binary<B>);
    primops.insert("min_int".to_string(), min_int as Binary<B>);
    primops.insert("eq_bit".to_string(), eq_bits as Binary<B>);
    primops.insert("eq_bits".to_string(), eq_bits as Binary<B>);
    primops.insert("neq_bits".to_string(), neq_bits as Binary<B>);
    primops.insert("xor_bits".to_string(), xor_bits as Binary<B>);
    primops.insert("or_bits".to_string(), or_bits as Binary<B>);
    primops.insert("and_bits".to_string(), and_bits as Binary<B>);
    primops.insert("add_bits".to_string(), add_bits as Binary<B>);
    primops.insert("sub_bits".to_string(), sub_bits as Binary<B>);
    primops.insert("add_bits_int".to_string(), add_bits_int as Binary<B>);
    primops.insert("sub_bits_int".to_string(), sub_bits_int as Binary<B>);
    primops.insert("align_bits".to_string(), align_bits as Binary<B>);
    primops.insert("undefined_range".to_string(), undefined_range as Binary<B>);
    primops.insert("zero_extend".to_string(), zero_extend as Binary<B>);
    primops.insert("sign_extend".to_string(), sign_extend as Binary<B>);
    primops.insert("sail_truncate".to_string(), sail_truncate as Binary<B>);
    primops.insert("sail_truncateLSB".to_string(), sail_truncate_lsb as Binary<B>);
    primops.insert("replicate_bits".to_string(), replicate_bits as Binary<B>);
    primops.insert("shiftr".to_string(), shiftr as Binary<B>);
    primops.insert("shiftl".to_string(), shiftl as Binary<B>);
    primops.insert("arith_shiftr".to_string(), arith_shiftr as Binary<B>);
    primops.insert("shift_bits_right".to_string(), shift_bits_right as Binary<B>);
    primops.insert("shift_bits_left".to_string(), shift_bits_left as Binary<B>);
    primops.insert("append".to_string(), append as Binary<B>);
    primops.insert("append_64".to_string(), append as Binary<B>);
    primops.insert("vector_access".to_string(), vector_access as Binary<B>);
    primops.insert("eq_anything".to_string(), eq_anything as Binary<B>);
    primops.insert("eq_string".to_string(), eq_string as Binary<B>);
    primops.insert("concat_str".to_string(), concat_str as Binary<B>);
    primops.insert("string_startswith".to_string(), string_startswith as Binary<B>);
    primops.insert("string_drop".to_string(), string_drop as Binary<B>);
    primops.insert("string_take".to_string(), string_take as Binary<B>);
    primops.insert("cons".to_string(), cons as Binary<B>);
    primops.insert("undefined_vector".to_string(), undefined_vector as Binary<B>);
    primops.insert("print_string".to_string(), print_string as Binary<B>);
    primops.insert("prerr_string".to_string(), prerr_string as Binary<B>);
    primops.insert("print_int".to_string(), print_int as Binary<B>);
    primops.insert("prerr_int".to_string(), prerr_int as Binary<B>);
    primops.insert("print_bits".to_string(), print_bits as Binary<B>);
    primops.insert("prerr_bits".to_string(), prerr_bits as Binary<B>);
    primops.insert("platform_branch_announce".to_string(), branch_announce as Binary<B>);
    primops.insert("branch_announce".to_string(), branch_announce as Binary<B>);
    primops.insert("address_announce".to_string(), address_announce as Binary<B>);
    primops.insert("mark_register".to_string(), mark_register as Binary<B>);
    primops.extend(float::binary_primops());
    primops
}

pub fn variadic_primops<B: BV>() -> HashMap<String, Variadic<B>> {
    let mut primops = HashMap::new();
    primops.insert("slice".to_string(), slice as Variadic<B>);
    primops.insert("vector_subrange".to_string(), subrange as Variadic<B>);
    primops.insert("vector_update".to_string(), vector_update as Variadic<B>);
    primops.insert("vector_update_subrange".to_string(), vector_update_subrange as Variadic<B>);
    primops.insert("bitvector_update".to_string(), bitvector_update as Variadic<B>);
    primops.insert("set_slice".to_string(), set_slice as Variadic<B>);
    primops.insert("get_slice_int".to_string(), get_slice_int as Variadic<B>);
    primops.insert("set_slice_int".to_string(), set_slice_int as Variadic<B>);
    primops.insert("platform_read_mem".to_string(), read_mem as Variadic<B>);
    primops.insert("platform_read_mem_ifetch".to_string(), read_mem_ifetch as Variadic<B>);
    primops.insert("platform_read_mem_exclusive".to_string(), read_mem_exclusive as Variadic<B>);
    primops.insert("platform_read_memt".to_string(), read_memt as Variadic<B>);
    primops.insert("platform_write_mem".to_string(), write_mem as Variadic<B>);
    primops.insert("platform_write_mem_exclusive".to_string(), write_mem_exclusive as Variadic<B>);
    primops.insert("platform_write_memt".to_string(), write_memt as Variadic<B>);
    primops.insert("platform_write_tag".to_string(), write_tag as Variadic<B>);
    primops.insert("platform_synchronize_registers".to_string(), synchronize_registers as Variadic<B>);
    primops.insert("platform_barrier".to_string(), unit_noop as Variadic<B>);
    primops.insert("elf_entry".to_string(), elf_entry as Variadic<B>);
    primops.insert("ite".to_string(), primop_ite as Variadic<B>);
    primops.insert("mark_register_pair".to_string(), mark_register_pair as Variadic<B>);
    // We explicitly don't handle anything real number related right now
    primops.insert("%string->%real".to_string(), unimplemented as Variadic<B>);
    primops.insert("neg_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("mult_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("sub_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("add_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("div_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("sqrt_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("abs_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("round_down".to_string(), unimplemented as Variadic<B>);
    primops.insert("round_up".to_string(), unimplemented as Variadic<B>);
    primops.insert("to_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("eq_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("lt_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("gt_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("lteq_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("gteq_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("real_power".to_string(), unimplemented as Variadic<B>);
    primops.insert("print_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("prerr_real".to_string(), unimplemented as Variadic<B>);
    primops.insert("undefined_real".to_string(), unimplemented as Variadic<B>);
    primops.extend(float::variadic_primops());
    primops.extend(memory::variadic_primops());
    primops
}

pub struct Primops<B> {
    pub unary: HashMap<String, Unary<B>>,
    pub binary: HashMap<String, Binary<B>>,
    pub variadic: HashMap<String, Variadic<B>>,
    pub consts: HashMap<String, Reset<B>>,
}

impl<B: BV> Default for Primops<B> {
    fn default() -> Self {
        Primops {
            unary: unary_primops(),
            binary: binary_primops(),
            variadic: variadic_primops(),
            consts: HashMap::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::error::ExecError;
    use crate::ir::{BitsSegment, Val};
    use crate::smt::smtlib::Ty;
    use crate::smt::{Config, Context, SmtResult, Solver};
    use crate::source_loc::SourceLoc;

    #[test]
    fn mixed_bits() -> Result<(), ExecError> {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let b1 = B64::new(0b11, 2);
        let p1 = BitsSegment::Concrete(b1);
        let v2 = solver.declare_const(Ty::BitVec(5), SourceLoc::unknown());
        let p2 = BitsSegment::Symbolic(v2);
        let p3 = BitsSegment::Concrete(B64::new(0b101, 3));
        let p4 = BitsSegment::Symbolic(solver.declare_const(Ty::BitVec(4), SourceLoc::unknown()));
        let val = Val::MixedBits(vec![p4, p3, p2, p1]);
        // Check basic flattening
        let _ = optimistic_assert(
            op_eq(val.clone(), Val::Bits(B64::new(0b0110_101_10011_11, 14)), &mut solver, SourceLoc::unknown())?,
            Val::String("mixed_bits 1".to_string()),
            &mut solver,
            SourceLoc::unknown(),
        )?;
        // Check that we can extract a concrete segment
        match op_slice(val.clone(), Val::I64(0), 2, &mut solver, SourceLoc::unknown())? {
            Val::Bits(bits) => assert!(bits == b1),
            _ => assert!(false),
        };
        // Check that we can extract a symbolic segment
        match op_slice(val.clone(), Val::I64(2), 5, &mut solver, SourceLoc::unknown())? {
            Val::Symbolic(v) => assert!(v == v2),
            _ => assert!(false),
        };
        let _ = pessimistic_assert(
            op_eq(
                op_slice(val.clone(), Val::I64(1), 5, &mut solver, SourceLoc::unknown())?,
                append(
                    Val::Bits(B64::new(1, 1)),
                    op_slice(Val::Symbolic(v2), Val::I64(0), 4, &mut solver, SourceLoc::unknown())?,
                    &mut solver,
                    SourceLoc::unknown(),
                )?,
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::String("mixed_bits 2".to_string()),
            &mut solver,
            SourceLoc::unknown(),
        );
        // vector_access
        match vector_access(val.clone(), Val::I128(1), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bit) => assert!(bit == B64::BIT_ONE),
            _ => assert!(false),
        };
        match vector_access(val.clone(), Val::I128(8), &mut solver, SourceLoc::unknown())? {
            Val::Bits(bit) => assert!(bit == B64::BIT_ZERO),
            _ => assert!(false),
        };
        let _ = pessimistic_assert(
            op_eq(
                vector_access(val.clone(), Val::I128(5), &mut solver, SourceLoc::unknown())?,
                op_slice(val, Val::I64(0), 1, &mut solver, SourceLoc::unknown())?,
                &mut solver,
                SourceLoc::unknown(),
            )?,
            Val::String("mixed bits 3".to_string()),
            &mut solver,
            SourceLoc::unknown(),
        );

        assert!(solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat);
        Ok(())
    }
}
