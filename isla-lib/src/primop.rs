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

use std::collections::HashMap;
use std::convert::TryFrom;
use std::ops::{Add, BitAnd, BitOr, BitXor, Not, Shl, Shr, Sub};

use crate::ast::Val;
use crate::concrete::{bzhi_u64, Sbits};
use crate::error::Error;
use crate::smt::smtlib::*;
use crate::smt::*;

pub type Unary = fn(Val, solver: &mut Solver) -> Result<Val, Error>;
pub type Binary = fn(Val, Val, solver: &mut Solver) -> Result<Val, Error>;
pub type Variadic = fn(Vec<Val>, solver: &mut Solver) -> Result<Val, Error>;

#[allow(clippy::needless_range_loop)]
pub fn smt_i128(i: i128) -> Exp {
    let mut bitvec = [false; 128];
    for n in 0..128 {
        if (i >> n & 1) == 1 {
            bitvec[n] = true
        }
    }
    Exp::Bits(bitvec.to_vec())
}

#[allow(clippy::needless_range_loop)]
pub fn smt_i64(i: i64) -> Exp {
    let mut bitvec = [false; 64];
    for n in 0..64 {
        if (i >> n & 1) == 1 {
            bitvec[n] = true
        }
    }
    Exp::Bits(bitvec.to_vec())
}

#[allow(clippy::needless_range_loop)]
pub fn smt_u8(i: u8) -> Exp {
    let mut bitvec = [false; 8];
    for n in 0..8 {
        if (i >> n & 1) == 1 {
            bitvec[n] = true
        }
    }
    Exp::Bits(bitvec.to_vec())
}

#[allow(clippy::needless_range_loop)]
fn smt_mask_lower(len: usize, mask_width: usize) -> Exp {
    let mut bitvec = vec![true; len];
    for i in 0..mask_width {
        bitvec[i] = false
    }
    Exp::Bits(bitvec)
}

fn smt_zeros(i: i128) -> Exp {
    Exp::Bits(vec![false; i as usize])
}

fn smt_ones(i: i128) -> Exp {
    Exp::Bits(vec![true; i as usize])
}

fn smt_sbits(bv: Sbits) -> Exp {
    Exp::Bits64(bv.bits, bv.length)
}

macro_rules! unary_primop_copy {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path) => {
        pub fn $f(x: Val, solver: &mut Solver) -> Result<Val, Error> {
            match x {
                Val::Symbolic(x) => {
                    let y = solver.fresh();
                    solver.add(Def::DefineConst(y, $smt_op(Box::new(Exp::Var(x)))));
                    Ok(Val::Symbolic(y))
                }
                $unwrap(x) => Ok($wrap($concrete_op(x))),
                _ => Err(Error::Type($name)),
            }
        }
    };
}

macro_rules! binary_primop_copy {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path, $to_symbolic:path) => {
        pub fn $f(x: Val, y: Val, solver: &mut Solver) -> Result<Val, Error> {
            match (x, y) {
                (Val::Symbolic(x), Val::Symbolic(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new(Exp::Var(x)), Box::new(Exp::Var(y)))));
                    Ok(Val::Symbolic(z))
                }
                (Val::Symbolic(x), $unwrap(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new(Exp::Var(x)), Box::new($to_symbolic(y)))));
                    Ok(Val::Symbolic(z))
                }
                ($unwrap(x), Val::Symbolic(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new($to_symbolic(x)), Box::new(Exp::Var(y)))));
                    Ok(Val::Symbolic(z))
                }
                ($unwrap(x), $unwrap(y)) => Ok($wrap($concrete_op(x, y))),
                (_, _) => Err(Error::Type($name)),
            }
        }
    };
}

macro_rules! binary_primop {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path, $to_symbolic:path) => {
        pub fn $f(x: Val, y: Val, solver: &mut Solver) -> Result<Val, Error> {
            match (x, y) {
                (Val::Symbolic(x), Val::Symbolic(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new(Exp::Var(x)), Box::new(Exp::Var(y)))));
                    Ok(Val::Symbolic(z))
                }
                (Val::Symbolic(x), $unwrap(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new(Exp::Var(x)), Box::new($to_symbolic(y)))));
                    Ok(Val::Symbolic(z))
                }
                ($unwrap(x), Val::Symbolic(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new($to_symbolic(x)), Box::new(Exp::Var(y)))));
                    Ok(Val::Symbolic(z))
                }
                ($unwrap(x), $unwrap(y)) => Ok($wrap($concrete_op(&x, &y))),
                (_, _) => Err(Error::Type($name)),
            }
        }
    };
}

fn assume(x: Val, solver: &mut Solver) -> Result<Val, Error> {
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
        _ => Err(Error::Type("assert")),
    }
}

// If the assertion can succeed, it will
fn optimistic_assert(x: Val, message: Val, solver: &mut Solver) -> Result<Val, Error> {
    let message = match message {
        Val::String(message) => message,
        _ => return Err(Error::Type("optimistic_assert")),
    };
    match x {
        Val::Symbolic(v) => {
            let test_true = Box::new(Exp::Var(v));
            let can_be_true = solver.check_sat_with(&test_true).is_sat();
            if can_be_true {
                solver.add(Def::Assert(Exp::Var(v)));
                Ok(Val::Unit)
            } else {
                Err(Error::AssertionFailed(message))
            }
        }
        Val::Bool(b) => {
            if b {
                Ok(Val::Unit)
            } else {
                Err(Error::AssertionFailed(message))
            }
        }
        _ => Err(Error::Type("optimistic_assert")),
    }
}

// If the assertion can fail, it will
fn pessimistic_assert(x: Val, message: Val, solver: &mut Solver) -> Result<Val, Error> {
    let message = match message {
        Val::String(message) => message,
        _ => return Err(Error::Type("pessimistic_assert")),
    };
    match x {
        Val::Symbolic(v) => {
            let test_false = Exp::Not(Box::new(Exp::Var(v)));
            let can_be_false = solver.check_sat_with(&test_false).is_sat();
            if can_be_false {
                Err(Error::AssertionFailed(message))
            } else {
                Ok(Val::Unit)
            }
        }
        Val::Bool(b) => {
            if b {
                Ok(Val::Unit)
            } else {
                Err(Error::AssertionFailed(message))
            }
        }
        _ => Err(Error::Type("pessimistic_assert")),
    }
}

// Conversion functions

fn i64_to_i128(x: Val, solver: &mut Solver) -> Result<Val, Error> {
    match x {
        Val::I64(x) => Ok(Val::I128(i128::from(x))),
        Val::Symbolic(x) => {
            let y = solver.fresh();
            solver.add(Def::DefineConst(y, Exp::SignExtend(64, Box::new(Exp::Var(x)))));
            Ok(Val::Symbolic(y))
        }
        _ => Err(Error::Type("%i64->%i")),
    }
}

fn i128_to_i64(x: Val, solver: &mut Solver) -> Result<Val, Error> {
    match x {
        Val::I128(x) => match i64::try_from(x) {
            Ok(y) => Ok(Val::I64(y)),
            Err(_) => Err(Error::Overflow),
        },
        Val::Symbolic(x) => {
            let y = solver.fresh();
            solver.add(Def::DefineConst(y, Exp::Extract(63, 0, Box::new(Exp::Var(x)))));
            Ok(Val::Symbolic(y))
        }
        _ => Err(Error::Type("%i->%i64")),
    }
}

binary_primop!(op_gt, "op_gt", Val::I64, Val::Bool, i64::gt, Exp::Bvsgt, smt_i64);
binary_primop_copy!(op_add, "op_add", Val::I64, Val::I64, i64::wrapping_add, Exp::Bvadd, smt_i64);

pub fn op_bit_to_bool(bit: Val, solver: &mut Solver) -> Result<Val, Error> {
    match bit {
        Val::Bits(bit) => Ok(Val::Bool(bit.bits & 1 == 1)),
        Val::Symbolic(bit) => {
            let boolean = solver.fresh();
            solver
                .add(Def::DefineConst(boolean, Exp::Eq(Box::new(Exp::Bits([true].to_vec())), Box::new(Exp::Var(bit)))));
            Ok(Val::Symbolic(boolean))
        }
        _ => Err(Error::Type("op_bit_to_bool")),
    }
}

pub fn op_unsigned(bits: Val, solver: &mut Solver) -> Result<Val, Error> {
    match bits {
        Val::Bits(bits) => Ok(Val::I64(bits.unsigned() as i64)),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => {
                let i = solver.fresh();
                solver.add(Def::DefineConst(i, Exp::ZeroExtend(64 - length, Box::new(Exp::Var(bits)))));
                Ok(Val::Symbolic(i))
            }
            None => Err(Error::Type("op_unsigned")),
        },
        _ => Err(Error::Type("op_unsigned")),
    }
}

// Basic comparisons

unary_primop_copy!(not_bool, "not", Val::Bool, Val::Bool, bool::not, Exp::Not);
binary_primop_copy!(and_bool, "and_bool", Val::Bool, Val::Bool, bool::bitand, Exp::And, Exp::Bool);
binary_primop_copy!(or_bool, "or_bool", Val::Bool, Val::Bool, bool::bitor, Exp::Or, Exp::Bool);
binary_primop!(eq_int, "eq_int", Val::I128, Val::Bool, i128::eq, Exp::Eq, smt_i128);
binary_primop!(eq_bool, "eq_bool", Val::Bool, Val::Bool, bool::eq, Exp::Eq, Exp::Bool);
binary_primop!(lteq_int, "lteq", Val::I128, Val::Bool, i128::le, Exp::Bvsle, smt_i128);
binary_primop!(gteq_int, "gteq", Val::I128, Val::Bool, i128::ge, Exp::Bvsge, smt_i128);
binary_primop!(lt_int, "lt", Val::I128, Val::Bool, i128::lt, Exp::Bvslt, smt_i128);
binary_primop!(gt_int, "gt", Val::I128, Val::Bool, i128::gt, Exp::Bvsgt, smt_i128);

fn abs_int(x: Val, solver: &mut Solver) -> Result<Val, Error> {
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
        _ => Err(Error::Type("abs_int")),
    }
}

// Arithmetic operations

binary_primop_copy!(add_int, "add_int", Val::I128, Val::I128, i128::wrapping_add, Exp::Bvadd, smt_i128);
binary_primop_copy!(sub_int, "sub_int", Val::I128, Val::I128, i128::wrapping_sub, Exp::Bvsub, smt_i128);
binary_primop_copy!(mult_int, "mult_int", Val::I128, Val::I128, i128::wrapping_mul, Exp::Bvmul, smt_i128);
unary_primop_copy!(neg_int, "neg_int", Val::I128, Val::I128, i128::wrapping_neg, Exp::Bvneg);
binary_primop_copy!(tdiv_int, "tdiv_int", Val::I128, Val::I128, i128::wrapping_div, Exp::Bvsdiv, smt_i128);
binary_primop_copy!(tmod_int, "tmod_int", Val::I128, Val::I128, i128::wrapping_rem, Exp::Bvsmod, smt_i128);
binary_primop_copy!(shl_int, "shl_int", Val::I128, Val::I128, i128::shl, Exp::Bvshl, smt_i128);
binary_primop_copy!(shr_int, "shr_int", Val::I128, Val::I128, i128::shr, Exp::Bvashr, smt_i128);
binary_primop_copy!(shl_mach_int, "shl_mach_int", Val::I64, Val::I64, i64::shl, Exp::Bvshl, smt_i64);
binary_primop_copy!(shr_mach_int, "shr_mach_int", Val::I64, Val::I64, i64::shr, Exp::Bvashr, smt_i64);

// Bitvector operations

fn length(x: Val, solver: &mut Solver) -> Result<Val, Error> {
    match x {
        Val::Symbolic(v) => match solver.length(v) {
            Some(len) => Ok(Val::I128(i128::from(len))),
            None => Err(Error::Type("length")),
        },
        Val::Bits(bv) => Ok(Val::I128(i128::from(bv.length))),
        _ => Err(Error::Type("length")),
    }
}

binary_primop!(eq_bits, "eq_bits", Val::Bits, Val::Bool, Sbits::eq, Exp::Eq, smt_sbits);
binary_primop!(neq_bits, "neq_bits", Val::Bits, Val::Bool, Sbits::ne, Exp::Neq, smt_sbits);
unary_primop_copy!(not_bits, "not_bits", Val::Bits, Val::Bits, Sbits::not, Exp::Bvnot);
binary_primop_copy!(xor_bits, "xor_bits", Val::Bits, Val::Bits, Sbits::bitxor, Exp::Bvxor, smt_sbits);
binary_primop_copy!(or_bits, "or_bits", Val::Bits, Val::Bits, Sbits::bitor, Exp::Bvor, smt_sbits);
binary_primop_copy!(and_bits, "and_bits", Val::Bits, Val::Bits, Sbits::bitand, Exp::Bvand, smt_sbits);
binary_primop_copy!(add_bits, "add_bits", Val::Bits, Val::Bits, Sbits::add, Exp::Bvadd, smt_sbits);
binary_primop_copy!(sub_bits, "sub_bits", Val::Bits, Val::Bits, Sbits::sub, Exp::Bvsub, smt_sbits);

fn zeros(len: Val, solver: &mut Solver) -> Result<Val, Error> {
    match len {
        Val::I128(len) => {
            if len <= 64 {
                Ok(Val::Bits(Sbits::zeros(len as u32)))
            } else {
                let bits = solver.fresh();
                solver.add(Def::DefineConst(bits, smt_zeros(len)));
                Ok(Val::Symbolic(bits))
            }
        }
        Val::Symbolic(_) => Err(Error::SymbolicLength),
        _ => Err(Error::Type("zeros")),
    }
}

fn ones(len: Val, solver: &mut Solver) -> Result<Val, Error> {
    match len {
        Val::I128(len) => {
            if len <= 64 {
                Ok(Val::Bits(Sbits::ones(len as u32)))
            } else {
                let bits = solver.fresh();
                solver.add(Def::DefineConst(bits, smt_ones(len)));
                Ok(Val::Symbolic(bits))
            }
        }
        Val::Symbolic(_) => Err(Error::SymbolicLength),
        _ => Err(Error::Type("ones")),
    }
}

/// The zero_extend and sign_extend functions are essentially the
/// same, so use a macro to define both.
macro_rules! extension {
    ($id: ident, $name: expr, $smt_extension: path, $concrete_extension: path) => {
        fn $id(bits: Val, len: Val, solver: &mut Solver) -> Result<Val, Error> {
            match (bits, len) {
                (Val::Bits(bits), Val::I128(len)) => {
                    let len = len as u32;
                    if len > 64 {
                        let ext = len - bits.length;
                        let extended_bits = solver.fresh();
                        solver.add(Def::DefineConst(extended_bits, $smt_extension(ext, Box::new(smt_sbits(bits)))));
                        Ok(Val::Symbolic(extended_bits))
                    } else {
                        Ok(Val::Bits($concrete_extension(bits, len)))
                    }
                }
                (Val::Symbolic(bits), Val::I128(len)) => {
                    let extended_bits = solver.fresh();
                    let ext = match solver.length(bits) {
                        Some(orig_len) => len as u32 - orig_len,
                        None => return Err(Error::Type($name)),
                    };
                    solver.add(Def::DefineConst(extended_bits, $smt_extension(ext, Box::new(Exp::Var(bits)))));
                    Ok(Val::Symbolic(extended_bits))
                }
                (_, Val::Symbolic(_)) => Err(Error::SymbolicLength),
                (_, _) => Err(Error::Type($name)),
            }
        }
    };
}

extension!(zero_extend, "zero_extend", Exp::ZeroExtend, Sbits::zero_extend);
extension!(sign_extend, "sign_extend", Exp::SignExtend, Sbits::sign_extend);

fn replicate_bits(bits: Val, times: Val, solver: &mut Solver) -> Result<Val, Error> {
    match (bits, times) {
        (Val::Bits(bits), Val::I128(times)) => match bits.replicate(times) {
            Some(replicated) => Ok(Val::Bits(replicated)),
            None => panic!("unimpl"),
        },
        (Val::Symbolic(bits), Val::I128(times)) => panic!("unimpl"),
        (_, _) => Err(Error::Type("replicate_bits")),
    }
}

/// Return the length of a concrete or symbolic bitvector, or return
/// Error::Type if the argument value is not a bitvector.
pub fn length_bits(bits: &Val, solver: &mut Solver) -> Result<u32, Error> {
    match bits {
        Val::Bits(bits) => Ok(bits.length),
        Val::Symbolic(bits) => match solver.length(*bits) {
            Some(len) => Ok(len),
            None => Err(Error::Type("length_bits")),
        },
        _ => Err(Error::Type("length_bits")),
    }
}

/// This macro implements the symbolic slice operation for anything
/// that is implemented as a bitvector in the SMT solver, so it can be
/// used for slice, get_slice_int, etc.
macro_rules! slice {
    ($bits_length: expr, $bits: expr, $from: expr, $slice_length: expr, $solver: ident) => {
        match $from {
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
                $solver.add(Def::DefineConst(
                    sliced,
                    Exp::Extract((from + $slice_length - 1) as u32, from as u32, Box::new($bits)),
                ));
                Ok(Val::Symbolic(sliced))
            }

            Val::I64(from) => {
                let sliced = $solver.fresh();
                $solver.add(Def::DefineConst(
                    sliced,
                    Exp::Extract((from as i128 + $slice_length - 1) as u32, from as u32, Box::new($bits)),
                ));
                Ok(Val::Symbolic(sliced))
            }

            _ => Err(Error::Type("slice!")),
        }
    };
}

pub fn op_slice(bits: Val, from: Val, length: u32, solver: &mut Solver) -> Result<Val, Error> {
    let bits_length = length_bits(&bits, solver)?;
    match bits {
        Val::Symbolic(bits) => slice!(bits_length, Exp::Var(bits), from, length as i128, solver),
        Val::Bits(bits) => match from {
            Val::I64(from) => match bits.slice(from as u32, length) {
                Some(bits) => Ok(Val::Bits(bits)),
                None => Err(Error::Type("op_slice")),
            },
            _ => slice!(bits_length, smt_sbits(bits), from, length as i128, solver),
        },
        _ => Err(Error::Type("op_slice")),
    }
}

fn slice_internal(bits: Val, from: Val, length: Val, solver: &mut Solver) -> Result<Val, Error> {
    let bits_length = length_bits(&bits, solver)?;
    match length {
        Val::I128(length) => match bits {
            Val::Symbolic(bits) => slice!(bits_length, Exp::Var(bits), from, length, solver),
            Val::Bits(bits) => match from {
                Val::I128(from) => match bits.slice(from as u32, length as u32) {
                    Some(bits) => Ok(Val::Bits(bits)),
                    None => Err(Error::Type("slice_internal")),
                },
                _ => slice!(bits_length, smt_sbits(bits), from, length, solver),
            },
            _ => Err(Error::Type("slice_internal")),
        },
        Val::Symbolic(_) => Err(Error::SymbolicLength),
        _ => Err(Error::Type("slice_internal")),
    }
}

fn slice(args: Vec<Val>, solver: &mut Solver) -> Result<Val, Error> {
    slice_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver)
}

fn subrange_internal(bits: Val, high: Val, low: Val, solver: &mut Solver) -> Result<Val, Error> {
    match (bits, high, low) {
        (Val::Symbolic(bits), Val::I128(high), Val::I128(low)) => {
            let sliced = solver.fresh();
            solver.add(Def::DefineConst(sliced, Exp::Extract(high as u32, low as u32, Box::new(Exp::Var(bits)))));
            Ok(Val::Symbolic(sliced))
        }
        (Val::Bits(bits), Val::I128(high), Val::I128(low)) => match bits.extract(high as u32, low as u32) {
            Some(bits) => Ok(Val::Bits(bits)),
            None => Err(Error::Type("subrange_internal")),
        },
        (_, _, Val::Symbolic(_)) => Err(Error::SymbolicLength),
        (_, Val::Symbolic(_), _) => Err(Error::SymbolicLength),
        (_, _, _) => Err(Error::Type("subrange_internal")),
    }
}

fn subrange(args: Vec<Val>, solver: &mut Solver) -> Result<Val, Error> {
    subrange_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver)
}

fn sail_truncate(bits: Val, len: Val, solver: &mut Solver) -> Result<Val, Error> {
    slice_internal(bits, Val::I128(0), len, solver)
}

fn sail_truncate_lsb(bits: Val, len: Val, solver: &mut Solver) -> Result<Val, Error> {
    match (bits, len) {
        (Val::Bits(bits), Val::I128(len)) => match bits.truncate_lsb(len) {
            Some(truncated) => Ok(Val::Bits(truncated)),
            None => Err(Error::Type("sail_truncateLSB")),
        },
        (Val::Symbolic(bits), Val::I128(len)) => {
            if len == 0 {
                Ok(Val::Bits(Sbits::new(0, 0)))
            } else if let Some(orig_len) = solver.length(bits) {
                let low = orig_len - (len as u32);
                let truncated = solver.fresh();
                solver.add(Def::DefineConst(truncated, Exp::Extract(orig_len - 1, low, Box::new(Exp::Var(bits)))));
                Ok(Val::Symbolic(truncated))
            } else {
                Err(Error::Type("sail_truncateLSB"))
            }
        }
        (_, Val::Symbolic(_)) => Err(Error::SymbolicLength),
        (_, _) => Err(Error::Type("sail_truncateLSB")),
    }
}

fn sail_unsigned(bits: Val, solver: &mut Solver) -> Result<Val, Error> {
    match bits {
        Val::Bits(bits) => Ok(Val::I128(bits.unsigned())),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => {
                let i = solver.fresh();
                solver.add(Def::DefineConst(i, Exp::ZeroExtend(128 - length, Box::new(Exp::Var(bits)))));
                Ok(Val::Symbolic(i))
            }
            None => Err(Error::Type("sail_unsigned")),
        },
        _ => Err(Error::Type("sail_unsigned")),
    }
}

fn sail_signed(bits: Val, solver: &mut Solver) -> Result<Val, Error> {
    match bits {
        Val::Bits(bits) => Ok(Val::I128(bits.signed())),
        Val::Symbolic(bits) => match solver.length(bits) {
            Some(length) => {
                let i = solver.fresh();
                solver.add(Def::DefineConst(i, Exp::SignExtend(128 - length, Box::new(Exp::Var(bits)))));
                Ok(Val::Symbolic(i))
            }
            None => Err(Error::Type("sail_signed")),
        },
        _ => Err(Error::Type("sail_signed")),
    }
}

fn shiftr(bits: Val, shift: Val, solver: &mut Solver) -> Result<Val, Error> {
    match (bits, shift) {
        (Val::Symbolic(x), Val::Symbolic(y)) => match solver.length(x) {
            Some(length) => {
                let z = solver.fresh();
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(y)))
                } else {
                    Exp::Var(y)
                };
                solver.add(Def::DefineConst(z, Exp::Bvlshr(Box::new(Exp::Var(x)), Box::new(shift))));
                Ok(Val::Symbolic(z))
            }
            None => Err(Error::Type("shiftr")),
        },
        (Val::Symbolic(x), Val::I128(y)) => match solver.length(x) {
            Some(length) => {
                let z = solver.fresh();
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(y)))
                } else {
                    smt_i128(y)
                };
                solver.add(Def::DefineConst(z, Exp::Bvlshr(Box::new(Exp::Var(x)), Box::new(shift))));
                Ok(Val::Symbolic(z))
            }
            None => Err(Error::Type("shiftr")),
        },
        (Val::Bits(x), Val::Symbolic(y)) => {
            let z = solver.fresh();
            solver.add(Def::DefineConst(
                z,
                Exp::Bvlshr(Box::new(smt_sbits(x)), Box::new(Exp::Extract(x.length - 1, 0, Box::new(Exp::Var(y))))),
            ));
            Ok(Val::Symbolic(z))
        }
        (Val::Bits(x), Val::I128(y)) => Ok(Val::Bits(x.shiftr(y))),
        (_, _) => Err(Error::Type("shiftr")),
    }
}

fn shiftl(bits: Val, len: Val, solver: &mut Solver) -> Result<Val, Error> {
    match (bits, len) {
        (Val::Symbolic(x), Val::Symbolic(y)) => match solver.length(x) {
            Some(length) => {
                let z = solver.fresh();
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(y)))
                } else {
                    Exp::Var(y)
                };
                solver.add(Def::DefineConst(z, Exp::Bvshl(Box::new(Exp::Var(x)), Box::new(shift))));
                Ok(Val::Symbolic(z))
            }
            None => Err(Error::Type("shiftl")),
        },
        (Val::Symbolic(x), Val::I128(y)) => match solver.length(x) {
            Some(length) => {
                let z = solver.fresh();
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(smt_i128(y)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(smt_i128(y)))
                } else {
                    smt_i128(y)
                };
                solver.add(Def::DefineConst(z, Exp::Bvshl(Box::new(Exp::Var(x)), Box::new(shift))));
                Ok(Val::Symbolic(z))
            }
            None => Err(Error::Type("shiftl")),
        },
        (Val::Bits(x), Val::Symbolic(y)) => {
            let z = solver.fresh();
            solver.add(Def::DefineConst(
                z,
                Exp::Bvshl(Box::new(smt_sbits(x)), Box::new(Exp::Extract(x.length - 1, 0, Box::new(Exp::Var(y))))),
            ));
            Ok(Val::Symbolic(z))
        }
        (Val::Bits(x), Val::I128(y)) => Ok(Val::Bits(x.shiftl(y))),
        (_, _) => Err(Error::Type("shiftl")),
    }
}

fn append(lhs: Val, rhs: Val, solver: &mut Solver) -> Result<Val, Error> {
    match (lhs, rhs) {
        (Val::Symbolic(x), Val::Symbolic(y)) => {
            let z = solver.fresh();
            solver.add(Def::DefineConst(z, Exp::Concat(Box::new(Exp::Var(x)), Box::new(Exp::Var(y)))));
            Ok(Val::Symbolic(z))
        }
        (Val::Symbolic(x), Val::Bits(y)) => {
            let z = solver.fresh();
            if y.length == 0 {
                solver.add(Def::DefineConst(z, Exp::Var(x)))
            } else {
                solver.add(Def::DefineConst(z, Exp::Concat(Box::new(Exp::Var(x)), Box::new(smt_sbits(y)))))
            }
            Ok(Val::Symbolic(z))
        }
        (Val::Bits(x), Val::Symbolic(y)) => {
            let z = solver.fresh();
            if x.length == 0 {
                solver.add(Def::DefineConst(z, Exp::Var(y)))
            } else {
                solver.add(Def::DefineConst(z, Exp::Concat(Box::new(smt_sbits(x)), Box::new(Exp::Var(y)))))
            }
            Ok(Val::Symbolic(z))
        }
        (Val::Bits(x), Val::Bits(y)) => match x.append(y) {
            Some(z) => Ok(Val::Bits(z)),
            None => {
                let z = solver.fresh();
                solver.add(Def::DefineConst(z, Exp::Concat(Box::new(smt_sbits(x)), Box::new(smt_sbits(y)))));
                Ok(Val::Symbolic(z))
            }
        },
        (_, _) => Err(Error::Type("append")),
    }
}

fn vector_access(bits: Val, n: Val, solver: &mut Solver) -> Result<Val, Error> {
    match (bits, n) {
        (Val::Symbolic(bits), Val::Symbolic(n)) => match solver.length(bits) {
            Some(length) => {
                let shift = if length < 128 {
                    Exp::Extract(length - 1, 0, Box::new(Exp::Var(n)))
                } else if length > 128 {
                    Exp::ZeroExtend(length - 128, Box::new(Exp::Var(n)))
                } else {
                    Exp::Var(n)
                };
                let bit = solver.fresh();
                solver.add(Def::DefineConst(
                    bit,
                    Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(Exp::Var(bits)), Box::new(shift)))),
                ));
                Ok(Val::Symbolic(bit))
            }
            None => Err(Error::Type("vector_access")),
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
                let bit = solver.fresh();
                solver.add(Def::DefineConst(
                    bit,
                    Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(Exp::Var(bits)), Box::new(shift)))),
                ));
                Ok(Val::Symbolic(bit))
            }
            None => Err(Error::Type("vector_access")),
        },
        (Val::Bits(bits), Val::Symbolic(n)) => {
            let shift = Exp::Extract(bits.length - 1, 0, Box::new(Exp::Var(n)));
            let bit = solver.fresh();
            solver.add(Def::DefineConst(
                bit,
                Exp::Extract(0, 0, Box::new(Exp::Bvlshr(Box::new(smt_sbits(bits)), Box::new(shift)))),
            ));
            Ok(Val::Symbolic(bit))
        }
        (Val::Bits(bits), Val::I128(n)) => match bits.slice(n as u32, 1) {
            Some(bit) => Ok(Val::Bits(bit)),
            None => Err(Error::Type("vector_access")),
        },
        (_, _) => Err(Error::Type("vector_access")),
    }
}

/// The set_slice! macro implements the Sail set_slice builtin for any
/// combination of symbolic or concrete operands, with the result
/// always being symbolic. The argument order is the same as the Sail
/// function it implements, plus the solver as a final argument.
macro_rules! set_slice {
    ($bits_length: ident, $update_length: ident, $bits: expr, $n: expr, $update: expr, $solver: ident) => {{
        let mask_lower = smt_mask_lower($bits_length as usize, $update_length as usize);
        let update = Exp::ZeroExtend($bits_length - $update_length, Box::new($update));
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
                    Box::new(Exp::Bvshl(Box::new(mask_lower), Box::new(shift.clone()))),
                )),
                Box::new(Exp::Bvshl(Box::new(update), Box::new(shift))),
            ),
        ));
        Ok(Val::Symbolic(sliced))
    }};
}

fn set_slice_internal(bits: Val, n: Val, update: Val, solver: &mut Solver) -> Result<Val, Error> {
    let bits_length = length_bits(&bits, solver)?;
    let update_length = length_bits(&update, solver)?;
    match (bits, n, update) {
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), Exp::Var(update), solver)
        }
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), smt_sbits(update), solver)
        }
        (Val::Symbolic(bits), Val::I128(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), smt_i128(n), Exp::Var(update), solver)
        }
        (Val::Symbolic(bits), Val::I128(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), smt_i128(n), smt_sbits(update), solver)
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), Exp::Var(update), solver)
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), smt_sbits(update), solver)
        }
        (Val::Bits(bits), Val::I128(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), smt_i128(n), Exp::Var(update), solver)
        }
        (Val::Bits(bits), Val::I128(n), Val::Bits(update)) => Ok(Val::Bits(bits.set_slice(n as u32, update))),
        (_, _, _) => Err(Error::Type("set_slice")),
    }
}

fn set_slice(args: Vec<Val>, solver: &mut Solver) -> Result<Val, Error> {
    // set_slice Sail builtin takes 2 additional integer parameters
    // for the bitvector lengths, which we can ignore.
    set_slice_internal(args[2].clone(), args[3].clone(), args[4].clone(), solver)
}

/// op_set_slice is just set_slice_internal with 64-bit integers rather than 128-bit.
pub fn op_set_slice(bits: Val, n: Val, update: Val, solver: &mut Solver) -> Result<Val, Error> {
    let bits_length = length_bits(&bits, solver)?;
    let update_length = length_bits(&update, solver)?;
    match (bits, n, update) {
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), Exp::Var(update), solver)
        }
        (Val::Symbolic(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), Exp::Var(n), smt_sbits(update), solver)
        }
        (Val::Symbolic(bits), Val::I64(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), smt_i64(n), Exp::Var(update), solver)
        }
        (Val::Symbolic(bits), Val::I64(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, Exp::Var(bits), smt_i64(n), smt_sbits(update), solver)
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), Exp::Var(update), solver)
        }
        (Val::Bits(bits), Val::Symbolic(n), Val::Bits(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), Exp::Var(n), smt_sbits(update), solver)
        }
        (Val::Bits(bits), Val::I64(n), Val::Symbolic(update)) => {
            set_slice!(bits_length, update_length, smt_sbits(bits), smt_i64(n), Exp::Var(update), solver)
        }
        (Val::Bits(bits), Val::I64(n), Val::Bits(update)) => Ok(Val::Bits(bits.set_slice(n as u32, update))),
        (_, _, _) => Err(Error::Type("set_slice")),
    }
}

/// `vector_update` is a special case of `set_slice` where the update
/// is a bitvector of length 1
fn vector_update(args: Vec<Val>, solver: &mut Solver) -> Result<Val, Error> {
    let arg0 = args[0].clone();
    match arg0 {
        Val::Vector(mut vec) => match args[1] {
            Val::I128(n) => {
                vec[n as usize] = args[2].clone();
                Ok(Val::Vector(vec))
            }
            _ => {
                println!("{:?}", args);
                Err(Error::Type("vector_update (index)"))
            }
        },
        Val::Bits(_) => {
            // If the argument is a bitvector then `vector_update` is a special case of `set_slice`
            // where the update is a bitvector of length 1
            set_slice_internal(arg0, args[1].clone(), args[2].clone(), solver)
        }
        _ => Err(Error::Type("vector_update")),
    }
}

fn bitvector_update(args: Vec<Val>, solver: &mut Solver) -> Result<Val, Error> {
    let arg0 = args[0].clone();
    match arg0 {
        Val::Bits(_) => op_set_slice(arg0, args[1].clone(), args[2].clone(), solver),
        _ => Err(Error::Type("bitvector_update")),
    }
}

fn get_slice_int_internal(length: Val, n: Val, from: Val, solver: &mut Solver) -> Result<Val, Error> {
    match length {
        Val::I128(length) => match n {
            Val::Symbolic(n) => slice!(128, Exp::Var(n), from, length, solver),
            Val::I128(n) => match from {
                Val::I128(from) if length <= 64 => {
                    let slice = bzhi_u64((n >> from) as u64, length as u32);
                    Ok(Val::Bits(Sbits::new(slice, length as u32)))
                }
                _ => slice!(128, smt_i128(n), from, length, solver),
            },
            _ => Err(Error::Type("get_slice_int")),
        },
        Val::Symbolic(_) => Err(Error::SymbolicLength),
        _ => Err(Error::Type("get_slice_int")),
    }
}

fn get_slice_int(args: Vec<Val>, solver: &mut Solver) -> Result<Val, Error> {
    get_slice_int_internal(args[0].clone(), args[1].clone(), args[2].clone(), solver)
}

fn unimplemented(_: Vec<Val>, _: &mut Solver) -> Result<Val, Error> {
    Err(Error::Unimplemented)
}

fn eq_string(lhs: Val, rhs: Val, _: &mut Solver) -> Result<Val, Error> {
    match (lhs, rhs) {
        (Val::String(lhs), Val::String(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (_, _) => Err(Error::Type("eq_string")),
    }
}

fn eq_anything(lhs: Val, rhs: Val, solver: &mut Solver) -> Result<Val, Error> {
    match (lhs, rhs) {
        (Val::Symbolic(lhs), Val::Symbolic(rhs)) => {
            let boolean = solver.fresh();
            solver.add(Def::DefineConst(boolean, Exp::Eq(Box::new(Exp::Var(lhs)), Box::new(Exp::Var(rhs)))));
            Ok(Val::Symbolic(boolean))
        }
        (Val::Bits(lhs), Val::Symbolic(rhs)) => {
            let boolean = solver.fresh();
            solver.add(Def::DefineConst(boolean, Exp::Eq(Box::new(smt_sbits(lhs)), Box::new(Exp::Var(rhs)))));
            Ok(Val::Symbolic(boolean))
        }
        (Val::Symbolic(lhs), Val::Bits(rhs)) => {
            let boolean = solver.fresh();
            solver.add(Def::DefineConst(boolean, Exp::Eq(Box::new(Exp::Var(lhs)), Box::new(smt_sbits(rhs)))));
            Ok(Val::Symbolic(boolean))
        }
        (Val::Bits(lhs), Val::Bits(rhs)) => Ok(Val::Bool(lhs == rhs)),
        (_, _) => Err(Error::Type("eq_anything")),
    }
}

fn putchar(c: Val, _: &mut Solver) -> Result<Val, Error> {
    if let Val::I128(c) = c {
        println!("Stdout: {}", char::from(c as u8))
    }
    Ok(Val::Unit)
}

fn prerr(message: Val, _: &mut Solver) -> Result<Val, Error> {
    if let Val::String(message) = message {
        println!("Stderr: {}", message)
    }
    Ok(Val::Unit)
}

fn undefined_bitvector(sz: Val, solver: &mut Solver) -> Result<Val, Error> {
    if let Val::I128(sz) = sz {
        let sym = solver.fresh();
        solver.add(Def::DeclareConst(sym, Ty::BitVec(sz as u32)));
        Ok(Val::Symbolic(sym))
    } else {
        Err(Error::Type("undefined_bitvector"))
    }
}

fn undefined_bool(_: Val, solver: &mut Solver) -> Result<Val, Error> {
    let sym = solver.fresh();
    solver.add(Def::DeclareConst(sym, Ty::Bool));
    Ok(Val::Symbolic(sym))
}

fn undefined_int(_: Val, solver: &mut Solver) -> Result<Val, Error> {
    let sym = solver.fresh();
    solver.add(Def::DeclareConst(sym, Ty::BitVec(128)));
    Ok(Val::Symbolic(sym))
}

fn one_if(condition: Val, solver: &mut Solver) -> Result<Val, Error> {
    match condition {
        Val::Bool(true) => Ok(Val::Bits(Sbits::BIT_ONE)),
        Val::Bool(false) => Ok(Val::Bits(Sbits::BIT_ZERO)),
        Val::Symbolic(v) => {
            let bit = solver.fresh();
            solver.add(Def::DefineConst(
                bit,
                Exp::Ite(
                    Box::new(Exp::Var(v)),
                    Box::new(smt_sbits(Sbits::BIT_ONE)),
                    Box::new(smt_sbits(Sbits::BIT_ZERO)),
                ),
            ));
            Ok(Val::Symbolic(bit))
        }
        _ => Err(Error::Type("one_if")),
    }
}

fn zero_if(condition: Val, solver: &mut Solver) -> Result<Val, Error> {
    match condition {
        Val::Bool(true) => Ok(Val::Bits(Sbits::BIT_ZERO)),
        Val::Bool(false) => Ok(Val::Bits(Sbits::BIT_ONE)),
        Val::Symbolic(v) => {
            let bit = solver.fresh();
            solver.add(Def::DefineConst(
                bit,
                Exp::Ite(
                    Box::new(Exp::Var(v)),
                    Box::new(smt_sbits(Sbits::BIT_ZERO)),
                    Box::new(smt_sbits(Sbits::BIT_ONE)),
                ),
            ));
            Ok(Val::Symbolic(bit))
        }
        _ => Err(Error::Type("one_if")),
    }
}

lazy_static! {
    pub static ref UNARY_PRIMOPS: HashMap<String, Unary> = {
        let mut primops = HashMap::new();
        primops.insert("%i64->%i".to_string(), i64_to_i128 as Unary);
        primops.insert("%i->%i64".to_string(), i128_to_i64 as Unary);
        primops.insert("assume".to_string(), assume as Unary);
        primops.insert("not".to_string(), not_bool as Unary);
        primops.insert("neg_int".to_string(), neg_int as Unary);
        primops.insert("abs_int".to_string(), abs_int as Unary);
        primops.insert("not_bits".to_string(), not_bits as Unary);
        primops.insert("length".to_string(), length as Unary);
        primops.insert("zeros".to_string(), zeros as Unary);
        primops.insert("ones".to_string(), ones as Unary);
        primops.insert("sail_unsigned".to_string(), sail_unsigned as Unary);
        primops.insert("sail_signed".to_string(), sail_signed as Unary);
        primops.insert("sail_putchar".to_string(), putchar as Unary);
        primops.insert("prerr".to_string(), prerr as Unary);
        primops.insert("undefined_bitvector".to_string(), undefined_bitvector as Unary);
        primops.insert("undefined_bool".to_string(), undefined_bool as Unary);
        primops.insert("undefined_int".to_string(), undefined_int as Unary);
        primops.insert("one_if".to_string(), one_if as Unary);
        primops.insert("zero_if".to_string(), zero_if as Unary);
        primops
    };
    pub static ref BINARY_PRIMOPS: HashMap<String, Binary> = {
        let mut primops = HashMap::new();
        primops.insert("optimistic_assert".to_string(), optimistic_assert as Binary);
        primops.insert("pessimistic_assert".to_string(), pessimistic_assert as Binary);
        primops.insert("and_bool".to_string(), and_bool as Binary);
        primops.insert("or_bool".to_string(), or_bool as Binary);
        primops.insert("eq_int".to_string(), eq_int as Binary);
        primops.insert("eq_bool".to_string(), eq_bool as Binary);
        primops.insert("lteq".to_string(), lteq_int as Binary);
        primops.insert("gteq".to_string(), gteq_int as Binary);
        primops.insert("lt".to_string(), lt_int as Binary);
        primops.insert("gt".to_string(), gt_int as Binary);
        primops.insert("add_int".to_string(), add_int as Binary);
        primops.insert("sub_int".to_string(), sub_int as Binary);
        primops.insert("mult_int".to_string(), mult_int as Binary);
        primops.insert("tdiv_int".to_string(), tdiv_int as Binary);
        primops.insert("tmod_int".to_string(), tmod_int as Binary);
        // FIXME: use correct euclidian operations
        primops.insert("ediv_int".to_string(), tdiv_int as Binary);
        primops.insert("emod_int".to_string(), tmod_int as Binary);
        primops.insert("shl_int".to_string(), shl_int as Binary);
        primops.insert("shr_int".to_string(), shr_int as Binary);
        primops.insert("shl_mach_int".to_string(), shl_mach_int as Binary);
        primops.insert("shr_mach_int".to_string(), shr_mach_int as Binary);
        primops.insert("eq_bit".to_string(), eq_bits as Binary);
        primops.insert("eq_bits".to_string(), eq_bits as Binary);
        primops.insert("neq_bits".to_string(), neq_bits as Binary);
        primops.insert("xor_bits".to_string(), xor_bits as Binary);
        primops.insert("or_bits".to_string(), or_bits as Binary);
        primops.insert("and_bits".to_string(), and_bits as Binary);
        primops.insert("add_bits".to_string(), add_bits as Binary);
        primops.insert("sub_bits".to_string(), sub_bits as Binary);
        primops.insert("zero_extend".to_string(), zero_extend as Binary);
        primops.insert("sign_extend".to_string(), sign_extend as Binary);
        primops.insert("sail_truncate".to_string(), sail_truncate as Binary);
        primops.insert("sail_truncateLSB".to_string(), sail_truncate_lsb as Binary);
        primops.insert("replicate_bits".to_string(), replicate_bits as Binary);
        primops.insert("shiftr".to_string(), shiftr as Binary);
        primops.insert("shiftl".to_string(), shiftl as Binary);
        primops.insert("append".to_string(), append as Binary);
        primops.insert("append_64".to_string(), append as Binary);
        primops.insert("vector_access".to_string(), vector_access as Binary);
        primops.insert("eq_anything".to_string(), eq_anything as Binary);
        primops.insert("eq_string".to_string(), eq_string as Binary);
        primops
    };
    pub static ref VARIADIC_PRIMOPS: HashMap<String, Variadic> = {
        let mut primops = HashMap::new();
        primops.insert("slice".to_string(), slice as Variadic);
        primops.insert("vector_subrange".to_string(), subrange as Variadic);
        primops.insert("vector_update".to_string(), vector_update as Variadic);
        primops.insert("bitvector_update".to_string(), bitvector_update as Variadic);
        primops.insert("set_slice".to_string(), set_slice as Variadic);
        primops.insert("get_slice_int".to_string(), get_slice_int as Variadic);
        primops.insert("%string->%real".to_string(), unimplemented as Variadic);
        primops.insert("neg_real".to_string(), unimplemented as Variadic);
        primops.insert("mult_real".to_string(), unimplemented as Variadic);
        primops.insert("sub_real".to_string(), unimplemented as Variadic);
        primops.insert("add_real".to_string(), unimplemented as Variadic);
        primops.insert("div_real".to_string(), unimplemented as Variadic);
        primops.insert("sqrt_real".to_string(), unimplemented as Variadic);
        primops.insert("abs_real".to_string(), unimplemented as Variadic);
        primops.insert("round_down".to_string(), unimplemented as Variadic);
        primops.insert("round_up".to_string(), unimplemented as Variadic);
        primops.insert("to_real".to_string(), unimplemented as Variadic);
        primops.insert("eq_real".to_string(), unimplemented as Variadic);
        primops.insert("lt_real".to_string(), unimplemented as Variadic);
        primops.insert("gt_real".to_string(), unimplemented as Variadic);
        primops.insert("lteq_real".to_string(), unimplemented as Variadic);
        primops.insert("gteq_real".to_string(), unimplemented as Variadic);
        primops.insert("real_power".to_string(), unimplemented as Variadic);
        primops.insert("print_real".to_string(), unimplemented as Variadic);
        primops.insert("prerr_real".to_string(), unimplemented as Variadic);
        primops
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn div_rem_is_truncating() {
        assert!(i128::wrapping_div(3, 2) == 1);
        assert!(i128::wrapping_div(-3, 2) == -1)
    }
}
