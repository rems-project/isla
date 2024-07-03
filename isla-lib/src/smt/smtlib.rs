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

//! This module defines a subset of the SMTLIB format we use to
//! interact with the SMT solver, which mostly corresponds to the
//! theory of quantifier-free bitvectors and arrays.

use ahash;

use std::collections::{HashMap, HashSet};
use std::ops::{Add, BitAnd, BitOr, BitXor, Deref, Shr, Sub};

use super::{EnumId, EnumMember, Sym};
use crate::bitvector::b64::B64;
use crate::bitvector::{ParsedBits, BV};
use crate::ir::Name;

#[derive(Clone, Debug)]
pub enum Ty {
    Bool,
    BitVec(u32),
    Enum(EnumId),
    Array(Box<Ty>, Box<Ty>),
    Float(u32, u32),
    RoundingMode,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum FPRoundingMode {
    RoundNearestTiesToEven,
    RoundNearestTiesToAway,
    RoundTowardPositive,
    RoundTowardNegative,
    RoundTowardZero,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum FPConstant {
    NaN,
    /// If negative is true, then -∞ rather than +∞, and similarly for the Zero constructor
    Inf {
        negative: bool,
    },
    Zero {
        negative: bool,
    },
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum FPUnary {
    Abs,
    Neg,
    IsNormal,
    IsSubnormal,
    IsZero,
    IsInfinite,
    IsNaN,
    IsNegative,
    IsPositive,
    /// Create a floating point number from a bitvector in IEEE 754-2008 interchange format
    FromIEEE(u32, u32),
}

impl FPUnary {
    fn result_ty(self) -> Option<Ty> {
        use FPUnary::*;
        match self {
            FromIEEE(sbits, ebits) => Some(Ty::Float(ebits, sbits)),
            IsNormal | IsSubnormal | IsZero | IsInfinite | IsNaN | IsNegative | IsPositive => Some(Ty::Bool),
            Abs | Neg => None,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum FPRoundingUnary {
    Sqrt,
    RoundToIntegral,
    Convert(u32, u32),
    FromSigned(u32, u32),
    FromUnsigned(u32, u32),
    ToSigned(u32),
    ToUnsigned(u32),
}

impl FPRoundingUnary {
    fn result_ty(self) -> Option<Ty> {
        use FPRoundingUnary::*;
        match self {
            Convert(ebits, sbits) | FromSigned(ebits, sbits) | FromUnsigned(ebits, sbits) => {
                Some(Ty::Float(ebits, sbits))
            }
            ToSigned(sz) | ToUnsigned(sz) => Some(Ty::BitVec(sz)),
            Sqrt | RoundToIntegral => None,
        }
    }
}

/// Note that SMTLIB is slightly inconsistent w.r.t. whether it uses
/// le or leq as a suffix for less than or equal to between bitvectors
/// and floating point. We follow SMTLIB exactly here.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum FPBinary {
    Rem,
    Min,
    Max,
    Leq,
    Lt,
    Geq,
    Gt,
    /// IEEE 754-2008 equality, which differs from regular SMTLIB equality
    Eq,
}

impl FPBinary {
    fn is_predicate(self) -> bool {
        use FPBinary::*;
        matches!(self, Leq | Lt | Geq | Gt | Eq)
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum FPRoundingBinary {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Exp<V> {
    Var(V),
    Bits(Vec<bool>),
    Bits64(B64),
    Enum(EnumMember),
    Bool(bool),
    Eq(Box<Exp<V>>, Box<Exp<V>>),
    Neq(Box<Exp<V>>, Box<Exp<V>>),
    And(Box<Exp<V>>, Box<Exp<V>>),
    Or(Box<Exp<V>>, Box<Exp<V>>),
    Not(Box<Exp<V>>),
    Bvnot(Box<Exp<V>>),
    Bvand(Box<Exp<V>>, Box<Exp<V>>),
    Bvor(Box<Exp<V>>, Box<Exp<V>>),
    Bvxor(Box<Exp<V>>, Box<Exp<V>>),
    Bvnand(Box<Exp<V>>, Box<Exp<V>>),
    Bvnor(Box<Exp<V>>, Box<Exp<V>>),
    Bvxnor(Box<Exp<V>>, Box<Exp<V>>),
    Bvneg(Box<Exp<V>>),
    Bvadd(Box<Exp<V>>, Box<Exp<V>>),
    Bvsub(Box<Exp<V>>, Box<Exp<V>>),
    Bvmul(Box<Exp<V>>, Box<Exp<V>>),
    Bvudiv(Box<Exp<V>>, Box<Exp<V>>),
    Bvsdiv(Box<Exp<V>>, Box<Exp<V>>),
    Bvurem(Box<Exp<V>>, Box<Exp<V>>),
    Bvsrem(Box<Exp<V>>, Box<Exp<V>>),
    Bvsmod(Box<Exp<V>>, Box<Exp<V>>),
    Bvult(Box<Exp<V>>, Box<Exp<V>>),
    Bvslt(Box<Exp<V>>, Box<Exp<V>>),
    Bvule(Box<Exp<V>>, Box<Exp<V>>),
    Bvsle(Box<Exp<V>>, Box<Exp<V>>),
    Bvuge(Box<Exp<V>>, Box<Exp<V>>),
    Bvsge(Box<Exp<V>>, Box<Exp<V>>),
    Bvugt(Box<Exp<V>>, Box<Exp<V>>),
    Bvsgt(Box<Exp<V>>, Box<Exp<V>>),
    Extract(u32, u32, Box<Exp<V>>),
    ZeroExtend(u32, Box<Exp<V>>),
    SignExtend(u32, Box<Exp<V>>),
    Bvshl(Box<Exp<V>>, Box<Exp<V>>),
    Bvlshr(Box<Exp<V>>, Box<Exp<V>>),
    Bvashr(Box<Exp<V>>, Box<Exp<V>>),
    Concat(Box<Exp<V>>, Box<Exp<V>>),
    Ite(Box<Exp<V>>, Box<Exp<V>>, Box<Exp<V>>),
    App(Sym, Vec<Exp<V>>),
    Select(Box<Exp<V>>, Box<Exp<V>>),
    Store(Box<Exp<V>>, Box<Exp<V>>, Box<Exp<V>>),
    Distinct(Vec<Exp<V>>),
    FPConstant(FPConstant, u32, u32),
    FPRoundingMode(FPRoundingMode),
    FPUnary(FPUnary, Box<Exp<V>>),
    FPRoundingUnary(FPRoundingUnary, Box<Exp<V>>, Box<Exp<V>>),
    FPBinary(FPBinary, Box<Exp<V>>, Box<Exp<V>>),
    FPRoundingBinary(FPRoundingBinary, Box<Exp<V>>, Box<Exp<V>>, Box<Exp<V>>),
    FPfma(Box<Exp<V>>, Box<Exp<V>>, Box<Exp<V>>, Box<Exp<V>>),
}

#[allow(clippy::needless_range_loop)]
pub fn bits64<V>(bits: u64, size: u32) -> Exp<V> {
    if size <= 64 {
        Exp::Bits64(B64::new(bits, size))
    } else {
        let size = size as usize;
        let mut bitvec = vec![false; size];
        for n in 0..size {
            if n < 64 && (bits >> n & 1) == 1 {
                bitvec[n] = true
            }
        }
        Exp::Bits(bitvec)
    }
}

pub fn smt_bits_from_str<V>(s: &str) -> Option<Exp<V>> {
    Some(match B64::from_str_long(s)? {
        ParsedBits::Short(bv) => bits64(bv.lower_u64(), bv.len()),
        ParsedBits::Long(bv) => Exp::Bits(bv),
    })
}

fn is_bits64<V>(exp: &Exp<V>) -> bool {
    matches!(exp, Exp::Bits64(_))
}

fn is_bits<V>(exp: &Exp<V>) -> bool {
    matches!(exp, Exp::Bits(_))
}

fn extract_bits64<V>(exp: &Exp<V>) -> B64 {
    match *exp {
        Exp::Bits64(bv) => bv,
        _ => unreachable!(),
    }
}

fn extract_bits<V>(exp: Exp<V>) -> Vec<bool> {
    match exp {
        Exp::Bits(bv) => bv,
        _ => unreachable!(),
    }
}

fn extract_bool<V>(exp: &Exp<V>) -> Option<bool> {
    match exp {
        Exp::Bool(b) => Some(*b),
        _ => None,
    }
}

macro_rules! binary_eval {
    ($eval:path, $exp_op:path, $small_op:path, $lhs:ident, $rhs:ident) => {{
        *$lhs = $lhs.eval();
        *$rhs = $rhs.eval();
        if is_bits64(&$lhs) & is_bits64(&$rhs) {
            Exp::Bits64($small_op(extract_bits64(&$lhs), extract_bits64(&$rhs)))
        } else {
            $exp_op($lhs, $rhs)
        }
    }};
}

macro_rules! under_binary_eval {
    ($exp_op:path, $lhs:ident, $rhs:ident) => {{
        *$lhs = $lhs.eval();
        *$rhs = $rhs.eval();
        $exp_op($lhs, $rhs)
    }};
}

fn collapsing_bvor<V>(lhs: Box<Exp<V>>, rhs: Box<Exp<V>>) -> Exp<V> {
    match (lhs.deref(), rhs.deref()) {
        (Exp::Bits64(bits), _) if bits.is_zero() => *rhs,
        (Exp::Bits(bits), _) if bits.iter().all(|b| !b) => *rhs,
        (_, Exp::Bits64(bits)) if bits.is_zero() => *lhs,
        (_, Exp::Bits(bits)) if bits.iter().all(|b| !b) => *lhs,
        _ => Exp::Bvor(lhs, rhs),
    }
}

fn collapsing_bvand<V>(lhs: Box<Exp<V>>, rhs: Box<Exp<V>>) -> Exp<V> {
    match (lhs.deref(), rhs.deref()) {
        (Exp::Bits64(bits), _) if bits.is_zero() => Exp::Bits64(B64::zeros(bits.len())),
        (Exp::Bits(bits), _) if bits.iter().all(|b| !b) => bits64(0, bits.len() as u32),
        (_, Exp::Bits64(bits)) if bits.is_zero() => Exp::Bits64(B64::zeros(bits.len())),
        (_, Exp::Bits(bits)) if bits.iter().all(|b| !b) => bits64(0, bits.len() as u32),
        _ => Exp::Bvand(lhs, rhs),
    }
}

fn eval_extract<V>(hi: u32, lo: u32, exp: Box<Exp<V>>) -> Exp<V> {
    if is_bits64(&exp) {
        Exp::Bits64(extract_bits64(&exp).extract(hi, lo).unwrap())
    } else if is_bits(&exp) {
        let orig_vec = extract_bits(*exp);
        let len = (hi - lo) + 1;
        if len <= 64 {
            let mut bv = B64::zeros(len);
            for n in 0..len {
                if orig_vec[(n + lo) as usize] {
                    bv = bv.set_slice(n, B64::ones(1))
                }
            }
            Exp::Bits64(bv)
        } else {
            let mut vec = vec![false; len as usize];
            for n in 0..len {
                if orig_vec[(n + lo) as usize] {
                    vec[n as usize] = true
                }
            }
            Exp::Bits(vec)
        }
    } else {
        Exp::Extract(hi, lo, exp)
    }
}

fn eval_zero_extend<V>(len: u32, exp: Box<Exp<V>>) -> Exp<V> {
    if is_bits64(&exp) {
        let bv = extract_bits64(&exp);
        if bv.len() + len <= 64 {
            Exp::Bits64(bv.zero_extend(bv.len() + len))
        } else {
            let mut bits = bv.to_vec();
            bits.resize((bv.len() + len) as usize, false);
            Exp::Bits(bits)
        }
    } else if is_bits(&exp) {
        let mut bits = extract_bits(*exp).clone();
        bits.resize(bits.len() + len as usize, false);
        Exp::Bits(bits)
    } else {
        Exp::ZeroExtend(len, exp)
    }
}

fn eval_sign_extend<V>(len: u32, exp: Box<Exp<V>>) -> Exp<V> {
    if is_bits64(&exp) {
        let bv = extract_bits64(&exp);
        if bv.len() + len <= 64 {
            Exp::Bits64(bv.sign_extend(bv.len() + len))
        } else {
            let mut bits = bv.to_vec();
            bits.resize((bv.len() + len) as usize, *bits.last().unwrap_or(&false));
            Exp::Bits(bits)
        }
    } else if is_bits(&exp) {
        let mut bits = extract_bits(*exp).clone();
        bits.resize(bits.len() + len as usize, *bits.last().unwrap_or(&false));
        Exp::Bits(bits)
    } else {
        Exp::SignExtend(len, exp)
    }
}

fn bits_to_i128(bits: &[bool]) -> Option<i128> {
    let mut v: u128 = 0;
    let mut len = bits.len();
    if len > 128 {
        for i in 128..len {
            if bits[i] {
                return None;
            }
        }
        len = 128
    };
    for i in (0..len).rev() {
        v = (v << 1) + if bits[i] { 1 } else { 0 };
    }
    Some(v as i128)
}

fn eval_bvshl<V>(lhs: Box<Exp<V>>, rhs: Box<Exp<V>>) -> Exp<V> {
    let shift = match rhs.deref() {
        Exp::Bits64(bv) => bv.unsigned(),
        Exp::Bits(bits) => match bits_to_i128(bits) {
            None => return Exp::Bvshl(lhs, rhs),
            Some(v) => v,
        },
        _ => return Exp::Bvshl(lhs, rhs),
    };
    match lhs.deref() {
        Exp::Bits64(bv) => Exp::Bits64(bv.shiftl(shift)),
        Exp::Bits(bits) => {
            let shift = match usize::try_from(shift) {
                Ok(v) => v,
                Err(_) => return Exp::Bvshl(lhs, rhs),
            };
            let mut r = vec![false; bits.len()];
            for i in shift..bits.len() {
                r[i] = bits[i - shift];
            }
            Exp::Bits(r)
        }
        _ => Exp::Bvshl(lhs, rhs),
    }
}

impl<V: PartialEq> Exp<V> {
    pub fn eval(self) -> Self {
        use Exp::*;
        match self {
            Bvnot(mut exp) => {
                *exp = exp.eval();
                match *exp {
                    Bits64(bv) => Bits64(!bv),
                    Bits(mut vec) => {
                        vec.iter_mut().for_each(|b| *b = !*b);
                        Bits(vec)
                    }
                    _ => Bvnot(exp),
                }
            }
            Eq(mut lhs, mut rhs) => under_binary_eval!(Eq, lhs, rhs),
            Neq(mut lhs, mut rhs) => under_binary_eval!(Neq, lhs, rhs),
            And(mut lhs, mut rhs) => {
                *lhs = lhs.eval();
                *rhs = rhs.eval();
                match (extract_bool(&lhs), extract_bool(&rhs)) {
                    (Some(blhs), Some(brhs)) => Bool(blhs & brhs),
                    (Some(false), _) => Bool(false),
                    (Some(true), _) => *rhs,
                    (_, Some(false)) => Bool(false),
                    (_, Some(true)) => *lhs,
                    _ => match (lhs.deref(), rhs.deref()) {
                        (Var(var1), Not(neg)) | (Not(neg), Var(var1)) => match neg.deref() {
                            Var(var2) if var1 == var2 => Bool(false),
                            _ => And(lhs, rhs),
                        },
                        _ => And(lhs, rhs),
                    },
                }
            }
            Or(mut lhs, mut rhs) => {
                *lhs = lhs.eval();
                *rhs = rhs.eval();
                match (extract_bool(&lhs), extract_bool(&rhs)) {
                    (Some(blhs), Some(brhs)) => Bool(blhs | brhs),
                    (Some(false), _) => *rhs,
                    (Some(true), _) => Bool(true),
                    (_, Some(false)) => *lhs,
                    (_, Some(true)) => Bool(true),
                    _ => match (lhs.deref(), rhs.deref()) {
                        (Var(var1), Not(neg)) | (Not(neg), Var(var1)) => match neg.deref() {
                            Var(var2) if var1 == var2 => Bool(true),
                            _ => Or(lhs, rhs),
                        },
                        _ => Or(lhs, rhs),
                    },
                }
            }
            Not(mut exp) => {
                *exp = exp.eval();
                if let Some(b) = extract_bool(&exp) {
                    Bool(!b)
                } else {
                    Not(exp)
                }
            }
            Bvand(mut lhs, mut rhs) => binary_eval!(Exp::eval, collapsing_bvand, B64::bitand, lhs, rhs),
            Bvor(mut lhs, mut rhs) => binary_eval!(Exp::eval, collapsing_bvor, B64::bitor, lhs, rhs),
            Bvxor(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvxor, B64::bitxor, lhs, rhs),
            Bvadd(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvadd, B64::add, lhs, rhs),
            Bvsub(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvsub, B64::sub, lhs, rhs),
            Bvlshr(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvlshr, B64::shr, lhs, rhs),
            Bvshl(mut lhs, mut rhs) => {
                *lhs = lhs.eval();
                *rhs = rhs.eval();
                eval_bvshl(lhs, rhs)
            }

            Bvneg(mut exp) => {
                *exp = exp.eval();
                Bvneg(exp)
            }
            Bvnand(mut lhs, mut rhs) => under_binary_eval!(Bvnand, lhs, rhs),
            Bvnor(mut lhs, mut rhs) => under_binary_eval!(Bvnor, lhs, rhs),
            Bvxnor(mut lhs, mut rhs) => under_binary_eval!(Bvxnor, lhs, rhs),
            Bvmul(mut lhs, mut rhs) => under_binary_eval!(Bvmul, lhs, rhs),
            Bvudiv(mut lhs, mut rhs) => under_binary_eval!(Bvudiv, lhs, rhs),
            Bvsdiv(mut lhs, mut rhs) => under_binary_eval!(Bvsdiv, lhs, rhs),
            Bvurem(mut lhs, mut rhs) => under_binary_eval!(Bvurem, lhs, rhs),
            Bvsrem(mut lhs, mut rhs) => under_binary_eval!(Bvsrem, lhs, rhs),
            Bvsmod(mut lhs, mut rhs) => under_binary_eval!(Bvsmod, lhs, rhs),
            Bvashr(mut lhs, mut rhs) => under_binary_eval!(Bvashr, lhs, rhs),

            Bvult(mut lhs, mut rhs) => under_binary_eval!(Bvult, lhs, rhs),
            Bvslt(mut lhs, mut rhs) => under_binary_eval!(Bvslt, lhs, rhs),
            Bvule(mut lhs, mut rhs) => under_binary_eval!(Bvule, lhs, rhs),
            Bvsle(mut lhs, mut rhs) => under_binary_eval!(Bvsle, lhs, rhs),
            Bvuge(mut lhs, mut rhs) => under_binary_eval!(Bvuge, lhs, rhs),
            Bvsge(mut lhs, mut rhs) => under_binary_eval!(Bvsge, lhs, rhs),
            Bvugt(mut lhs, mut rhs) => under_binary_eval!(Bvugt, lhs, rhs),
            Bvsgt(mut lhs, mut rhs) => under_binary_eval!(Bvsgt, lhs, rhs),

            Extract(hi, lo, mut exp) => {
                *exp = exp.eval();
                eval_extract(hi, lo, exp)
            }
            ZeroExtend(len, mut exp) => {
                *exp = exp.eval();
                eval_zero_extend(len, exp)
            }
            SignExtend(len, mut exp) => {
                *exp = exp.eval();
                eval_sign_extend(len, exp)
            }
            Concat(mut lhs, mut rhs) => {
                *lhs = lhs.eval();
                *rhs = rhs.eval();
                if is_bits64(&lhs) & is_bits64(&rhs) {
                    let lh_bits = extract_bits64(&lhs);
                    let rh_bits = extract_bits64(&rhs);
                    lh_bits.append(rh_bits).map(Exp::Bits64).unwrap_or(Exp::Concat(lhs, rhs))
                } else {
                    Exp::Concat(lhs, rhs)
                }
            }
            Ite(mut guard, mut true_exp, mut false_exp) => {
                *guard = guard.eval();
                *true_exp = true_exp.eval();
                *false_exp = false_exp.eval();
                match extract_bool(&guard) {
                    Some(true) => *true_exp,
                    Some(false) => *false_exp,
                    None => Ite(guard, true_exp, false_exp),
                }
            }
            _ => self,
        }
    }

    /// Recursivly apply the supplied function to each sub-expression in a bottom-up order
    pub fn modify<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Exp<V>),
    {
        use Exp::*;
        match self {
            Var(_) | Bits(_) | Bits64(_) | Enum(_) | Bool(_) | FPConstant(..) | FPRoundingMode(_) => (),
            Not(exp)
            | Bvnot(exp)
            | Bvneg(exp)
            | Extract(_, _, exp)
            | ZeroExtend(_, exp)
            | SignExtend(_, exp)
            | FPUnary(_, exp) => exp.modify(f),
            Eq(lhs, rhs)
            | Neq(lhs, rhs)
            | And(lhs, rhs)
            | Or(lhs, rhs)
            | Bvand(lhs, rhs)
            | Bvor(lhs, rhs)
            | Bvxor(lhs, rhs)
            | Bvnand(lhs, rhs)
            | Bvnor(lhs, rhs)
            | Bvxnor(lhs, rhs)
            | Bvadd(lhs, rhs)
            | Bvsub(lhs, rhs)
            | Bvmul(lhs, rhs)
            | Bvudiv(lhs, rhs)
            | Bvsdiv(lhs, rhs)
            | Bvurem(lhs, rhs)
            | Bvsrem(lhs, rhs)
            | Bvsmod(lhs, rhs)
            | Bvult(lhs, rhs)
            | Bvslt(lhs, rhs)
            | Bvule(lhs, rhs)
            | Bvsle(lhs, rhs)
            | Bvuge(lhs, rhs)
            | Bvsge(lhs, rhs)
            | Bvugt(lhs, rhs)
            | Bvsgt(lhs, rhs)
            | Bvshl(lhs, rhs)
            | Bvlshr(lhs, rhs)
            | Bvashr(lhs, rhs)
            | Concat(lhs, rhs)
            | FPBinary(_, lhs, rhs) => {
                lhs.modify(f);
                rhs.modify(f);
            }
            Ite(cond, then_exp, else_exp) => {
                cond.modify(f);
                then_exp.modify(f);
                else_exp.modify(f)
            }
            App(_, args) => {
                for exp in args {
                    exp.modify(f)
                }
            }
            Select(array, index) => {
                array.modify(f);
                index.modify(f);
            }
            Store(array, index, val) => {
                array.modify(f);
                index.modify(f);
                val.modify(f);
            }
            Distinct(exps) => {
                for exp in exps {
                    exp.modify(f)
                }
            }
            FPRoundingUnary(_, rm, exp) => {
                rm.modify(f);
                exp.modify(f);
            }
            FPRoundingBinary(_, rm, lhs, rhs) => {
                rm.modify(f);
                lhs.modify(f);
                rhs.modify(f);
            }
            FPfma(rm, x, y, z) => {
                rm.modify(f);
                x.modify(f);
                y.modify(f);
                z.modify(f);
            }
        };
        f(self)
    }

    /// Recursivly apply the supplied function to each sub-expression in a top down order
    pub fn modify_top_down<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Exp<V>),
    {
        use Exp::*;
        f(self);
        match self {
            Var(_) | Bits(_) | Bits64(_) | Enum(_) | Bool(_) | FPConstant(..) | FPRoundingMode(_) => (),
            Not(exp)
            | Bvnot(exp)
            | Bvneg(exp)
            | Extract(_, _, exp)
            | ZeroExtend(_, exp)
            | SignExtend(_, exp)
            | FPUnary(_, exp) => exp.modify(f),
            Eq(lhs, rhs)
            | Neq(lhs, rhs)
            | And(lhs, rhs)
            | Or(lhs, rhs)
            | Bvand(lhs, rhs)
            | Bvor(lhs, rhs)
            | Bvxor(lhs, rhs)
            | Bvnand(lhs, rhs)
            | Bvnor(lhs, rhs)
            | Bvxnor(lhs, rhs)
            | Bvadd(lhs, rhs)
            | Bvsub(lhs, rhs)
            | Bvmul(lhs, rhs)
            | Bvudiv(lhs, rhs)
            | Bvsdiv(lhs, rhs)
            | Bvurem(lhs, rhs)
            | Bvsrem(lhs, rhs)
            | Bvsmod(lhs, rhs)
            | Bvult(lhs, rhs)
            | Bvslt(lhs, rhs)
            | Bvule(lhs, rhs)
            | Bvsle(lhs, rhs)
            | Bvuge(lhs, rhs)
            | Bvsge(lhs, rhs)
            | Bvugt(lhs, rhs)
            | Bvsgt(lhs, rhs)
            | Bvshl(lhs, rhs)
            | Bvlshr(lhs, rhs)
            | Bvashr(lhs, rhs)
            | Concat(lhs, rhs)
            | FPBinary(_, lhs, rhs) => {
                lhs.modify(f);
                rhs.modify(f);
            }
            Ite(cond, then_exp, else_exp) => {
                cond.modify(f);
                then_exp.modify(f);
                else_exp.modify(f)
            }
            App(_, args) => {
                for exp in args {
                    exp.modify(f)
                }
            }
            Select(array, index) => {
                array.modify(f);
                index.modify(f);
            }
            Store(array, index, val) => {
                array.modify(f);
                index.modify(f);
                val.modify(f);
            }
            Distinct(exps) => {
                for exp in exps {
                    exp.modify(f)
                }
            }
            FPRoundingUnary(_, rm, exp) => {
                rm.modify(f);
                exp.modify(f);
            }
            FPRoundingBinary(_, rm, lhs, rhs) => {
                rm.modify(f);
                lhs.modify(f);
                rhs.modify(f);
            }
            FPfma(rm, x, y, z) => {
                rm.modify(f);
                x.modify(f);
                y.modify(f);
                z.modify(f);
            }
        }
    }

    #[allow(clippy::type_complexity)]
    fn binary_commute_extract(self) -> Result<(fn(Box<Self>, Box<Self>) -> Self, Box<Self>, Box<Self>), Self> {
        use Exp::*;
        match self {
            Bvand(lhs, rhs) => Ok((Bvand, lhs, rhs)),
            Bvor(lhs, rhs) => Ok((Bvor, lhs, rhs)),
            Bvxor(lhs, rhs) => Ok((Bvxor, lhs, rhs)),
            Bvnand(lhs, rhs) => Ok((Bvnand, lhs, rhs)),
            Bvnor(lhs, rhs) => Ok((Bvnor, lhs, rhs)),
            Bvxnor(lhs, rhs) => Ok((Bvxnor, lhs, rhs)),
            Bvadd(lhs, rhs) => Ok((Bvadd, lhs, rhs)),
            Bvsub(lhs, rhs) => Ok((Bvsub, lhs, rhs)),
            _ => Err(self),
        }
    }

    pub fn commute_extract(&mut self) {
        use Exp::*;
        if let Extract(hi, lo, exp) = self {
            match std::mem::replace(&mut **exp, Bool(false)).binary_commute_extract() {
                Ok((op, lhs, rhs)) => *self = op(Box::new(Extract(*hi, *lo, lhs)), Box::new(Extract(*hi, *lo, rhs))),
                Err(mut orig_exp) => {
                    std::mem::swap(&mut **exp, &mut orig_exp);
                }
            }
        }
    }
}

impl<'a, V: 'a> Exp<V> {
    pub fn map_var<F, Err, V2>(&'a self, f: &mut F) -> Result<Exp<V2>, Err>
    where
        F: FnMut(&'a V) -> Result<Exp<V2>, Err>,
    {
        use Exp::*;
        match self {
            Var(v) => Ok(f(v)?),
            Bits(bv) => Ok(Bits(bv.clone())),
            Bits64(bs) => Ok(Bits64(*bs)),
            Enum(mem) => Ok(Enum(*mem)),
            Bool(b) => Ok(Bool(*b)),
            Not(exp) => Ok(Not(Box::new(exp.map_var(f)?))),
            Bvnot(exp) => Ok(Bvnot(Box::new(exp.map_var(f)?))),
            Bvneg(exp) => Ok(Bvneg(Box::new(exp.map_var(f)?))),
            Extract(hi, lo, exp) => Ok(Extract(*hi, *lo, Box::new(exp.map_var(f)?))),
            ZeroExtend(n, exp) => Ok(ZeroExtend(*n, Box::new(exp.map_var(f)?))),
            SignExtend(n, exp) => Ok(SignExtend(*n, Box::new(exp.map_var(f)?))),
            Eq(lhs, rhs) => Ok(Eq(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Neq(lhs, rhs) => Ok(Neq(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            And(lhs, rhs) => Ok(And(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Or(lhs, rhs) => Ok(Or(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvand(lhs, rhs) => Ok(Bvand(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvor(lhs, rhs) => Ok(Bvor(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvxor(lhs, rhs) => Ok(Bvxor(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvnand(lhs, rhs) => Ok(Bvnand(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvnor(lhs, rhs) => Ok(Bvnor(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvxnor(lhs, rhs) => Ok(Bvxnor(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvadd(lhs, rhs) => Ok(Bvadd(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvsub(lhs, rhs) => Ok(Bvsub(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvmul(lhs, rhs) => Ok(Bvmul(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvudiv(lhs, rhs) => Ok(Bvudiv(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvsdiv(lhs, rhs) => Ok(Bvsdiv(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvurem(lhs, rhs) => Ok(Bvurem(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvsrem(lhs, rhs) => Ok(Bvsrem(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvsmod(lhs, rhs) => Ok(Bvsmod(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvult(lhs, rhs) => Ok(Bvult(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvslt(lhs, rhs) => Ok(Bvslt(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvule(lhs, rhs) => Ok(Bvule(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvsle(lhs, rhs) => Ok(Bvsle(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvuge(lhs, rhs) => Ok(Bvuge(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvsge(lhs, rhs) => Ok(Bvsge(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvugt(lhs, rhs) => Ok(Bvugt(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvsgt(lhs, rhs) => Ok(Bvsgt(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvshl(lhs, rhs) => Ok(Bvshl(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvlshr(lhs, rhs) => Ok(Bvlshr(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Bvashr(lhs, rhs) => Ok(Bvashr(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Concat(lhs, rhs) => Ok(Concat(Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            Ite(cond, then_exp, else_exp) => {
                Ok(Ite(Box::new(cond.map_var(f)?), Box::new(then_exp.map_var(f)?), Box::new(else_exp.map_var(f)?)))
            }
            App(name, args) => Ok(App(*name, args.iter().map(|exp| exp.map_var(f)).collect::<Result<Vec<_>, _>>()?)),
            Select(array, index) => Ok(Select(Box::new(array.map_var(f)?), Box::new(index.map_var(f)?))),
            Store(array, index, val) => {
                Ok(Store(Box::new(array.map_var(f)?), Box::new(index.map_var(f)?), Box::new(val.map_var(f)?)))
            }
            Distinct(exps) => Ok(Distinct(exps.iter().map(|exp| exp.map_var(f)).collect::<Result<Vec<_>, _>>()?)),
            FPConstant(c, sbits, ebits) => Ok(FPConstant(*c, *sbits, *ebits)),
            FPRoundingMode(rm) => Ok(FPRoundingMode(*rm)),
            FPUnary(op, exp) => Ok(FPUnary(*op, Box::new(exp.map_var(f)?))),
            FPRoundingUnary(op, rm, exp) => {
                Ok(FPRoundingUnary(*op, Box::new(rm.map_var(f)?), Box::new(exp.map_var(f)?)))
            }
            FPBinary(op, lhs, rhs) => Ok(FPBinary(*op, Box::new(lhs.map_var(f)?), Box::new(rhs.map_var(f)?))),
            FPRoundingBinary(op, rm, lhs, rhs) => Ok(FPRoundingBinary(
                *op,
                Box::new(rm.map_var(f)?),
                Box::new(lhs.map_var(f)?),
                Box::new(rhs.map_var(f)?),
            )),
            FPfma(rm, x, y, z) => Ok(FPfma(
                Box::new(rm.map_var(f)?),
                Box::new(x.map_var(f)?),
                Box::new(y.map_var(f)?),
                Box::new(z.map_var(f)?),
            )),
        }
    }
}

impl Exp<Sym> {
    pub fn clone_expand(&self, defs: &HashMap<Sym, &Exp<Sym>>) -> Self {
        self.map_var(&mut |v| {
            Ok::<_, ()>(match defs.get(v) {
                Some(exp) => exp.clone_expand(defs),
                None => Exp::Var(*v),
            })
        })
        .unwrap()
    }

    pub fn collect_variables(&self, vars: &mut HashSet<Sym, ahash::RandomState>) {
        use Exp::*;
        match self {
            Var(v) => {
                vars.insert(*v);
            }
            Bits(_) | Bits64(_) | Enum(_) | Bool(_) | FPConstant(..) | FPRoundingMode(_) => (),
            Not(exp)
            | Bvnot(exp)
            | Bvneg(exp)
            | Extract(_, _, exp)
            | ZeroExtend(_, exp)
            | SignExtend(_, exp)
            | FPUnary(_, exp) => exp.collect_variables(vars),
            Eq(lhs, rhs)
            | Neq(lhs, rhs)
            | And(lhs, rhs)
            | Or(lhs, rhs)
            | Bvand(lhs, rhs)
            | Bvor(lhs, rhs)
            | Bvxor(lhs, rhs)
            | Bvnand(lhs, rhs)
            | Bvnor(lhs, rhs)
            | Bvxnor(lhs, rhs)
            | Bvadd(lhs, rhs)
            | Bvsub(lhs, rhs)
            | Bvmul(lhs, rhs)
            | Bvudiv(lhs, rhs)
            | Bvsdiv(lhs, rhs)
            | Bvurem(lhs, rhs)
            | Bvsrem(lhs, rhs)
            | Bvsmod(lhs, rhs)
            | Bvult(lhs, rhs)
            | Bvslt(lhs, rhs)
            | Bvule(lhs, rhs)
            | Bvsle(lhs, rhs)
            | Bvuge(lhs, rhs)
            | Bvsge(lhs, rhs)
            | Bvugt(lhs, rhs)
            | Bvsgt(lhs, rhs)
            | Bvshl(lhs, rhs)
            | Bvlshr(lhs, rhs)
            | Bvashr(lhs, rhs)
            | Concat(lhs, rhs)
            | FPBinary(_, lhs, rhs) => {
                lhs.collect_variables(vars);
                rhs.collect_variables(vars);
            }
            Ite(cond, then_exp, else_exp) => {
                cond.collect_variables(vars);
                then_exp.collect_variables(vars);
                else_exp.collect_variables(vars)
            }
            App(_, args) => {
                for exp in args {
                    exp.collect_variables(vars)
                }
            }
            Select(array, index) => {
                array.collect_variables(vars);
                index.collect_variables(vars);
            }
            Store(array, index, val) => {
                array.collect_variables(vars);
                index.collect_variables(vars);
                val.collect_variables(vars);
            }
            Distinct(exps) => {
                for exp in exps {
                    exp.collect_variables(vars)
                }
            }
            FPRoundingUnary(_, rm, exp) => {
                rm.collect_variables(vars);
                exp.collect_variables(vars);
            }
            FPRoundingBinary(_, rm, lhs, rhs) => {
                rm.collect_variables(vars);
                lhs.collect_variables(vars);
                rhs.collect_variables(vars);
            }
            FPfma(rm, x, y, z) => {
                rm.collect_variables(vars);
                x.collect_variables(vars);
                y.collect_variables(vars);
                z.collect_variables(vars);
            }
        }
    }

    pub fn variables(&self) -> HashSet<Sym, ahash::RandomState> {
        let mut vars = HashSet::default();
        self.collect_variables(&mut vars);
        vars
    }

    pub fn subst_once_in_place(&mut self, substs: &mut HashMap<Sym, Option<Self>>) {
        use Exp::*;
        match self {
            Var(v) => {
                if let Some(exp) = substs.get_mut(v) {
                    if let Some(exp) = exp.take() {
                        *self = exp
                    } else {
                        panic!("Tried to substitute {:?} twice in subst_once_in_place", v)
                    }
                }
            }
            Bits(_) | Bits64(_) | Enum(_) | Bool(_) | FPConstant(..) | FPRoundingMode(_) => (),
            Not(exp)
            | Bvnot(exp)
            | Bvneg(exp)
            | Extract(_, _, exp)
            | ZeroExtend(_, exp)
            | SignExtend(_, exp)
            | FPUnary(_, exp) => exp.subst_once_in_place(substs),
            Eq(lhs, rhs)
            | Neq(lhs, rhs)
            | And(lhs, rhs)
            | Or(lhs, rhs)
            | Bvand(lhs, rhs)
            | Bvor(lhs, rhs)
            | Bvxor(lhs, rhs)
            | Bvnand(lhs, rhs)
            | Bvnor(lhs, rhs)
            | Bvxnor(lhs, rhs)
            | Bvadd(lhs, rhs)
            | Bvsub(lhs, rhs)
            | Bvmul(lhs, rhs)
            | Bvudiv(lhs, rhs)
            | Bvsdiv(lhs, rhs)
            | Bvurem(lhs, rhs)
            | Bvsrem(lhs, rhs)
            | Bvsmod(lhs, rhs)
            | Bvult(lhs, rhs)
            | Bvslt(lhs, rhs)
            | Bvule(lhs, rhs)
            | Bvsle(lhs, rhs)
            | Bvuge(lhs, rhs)
            | Bvsge(lhs, rhs)
            | Bvugt(lhs, rhs)
            | Bvsgt(lhs, rhs)
            | Bvshl(lhs, rhs)
            | Bvlshr(lhs, rhs)
            | Bvashr(lhs, rhs)
            | Concat(lhs, rhs)
            | FPBinary(_, lhs, rhs) => {
                lhs.subst_once_in_place(substs);
                rhs.subst_once_in_place(substs);
            }
            Ite(cond, then_exp, else_exp) => {
                cond.subst_once_in_place(substs);
                then_exp.subst_once_in_place(substs);
                else_exp.subst_once_in_place(substs)
            }
            App(_, args) => {
                for exp in args {
                    exp.subst_once_in_place(substs)
                }
            }
            Select(array, index) => {
                array.subst_once_in_place(substs);
                index.subst_once_in_place(substs);
            }
            Store(array, index, val) => {
                array.subst_once_in_place(substs);
                index.subst_once_in_place(substs);
                val.subst_once_in_place(substs);
            }
            Distinct(exps) => {
                for exp in exps {
                    exp.subst_once_in_place(substs)
                }
            }
            FPRoundingUnary(_, rm, exp) => {
                rm.subst_once_in_place(substs);
                exp.subst_once_in_place(substs);
            }
            FPRoundingBinary(_, rm, lhs, rhs) => {
                rm.subst_once_in_place(substs);
                lhs.subst_once_in_place(substs);
                rhs.subst_once_in_place(substs);
            }
            FPfma(rm, x, y, z) => {
                rm.subst_once_in_place(substs);
                x.subst_once_in_place(substs);
                y.subst_once_in_place(substs);
                z.subst_once_in_place(substs);
            }
        }
    }

    /// Infer the type of an already well-formed SMTLIB expression
    pub fn infer(&self, tcx: &HashMap<Sym, Ty>, ftcx: &HashMap<Sym, (Vec<Ty>, Ty)>) -> Option<Ty> {
        use Exp::*;
        match self {
            Var(v) => tcx.get(v).map(Ty::clone),
            Bits(bv) => Some(Ty::BitVec(bv.len() as u32)),
            Bits64(bv) => Some(Ty::BitVec(bv.len())),
            Enum(e) => Some(Ty::Enum(e.enum_id)),
            Bool(_)
            | Not(_)
            | Eq(_, _)
            | Neq(_, _)
            | And(_, _)
            | Or(_, _)
            | Bvult(_, _)
            | Bvslt(_, _)
            | Bvule(_, _)
            | Bvsle(_, _)
            | Bvuge(_, _)
            | Bvsge(_, _)
            | Bvugt(_, _)
            | Bvsgt(_, _)
            | Distinct(_) => Some(Ty::Bool),
            Bvnot(exp) | Bvneg(exp) => exp.infer(tcx, ftcx),
            Extract(i, j, _) => Some(Ty::BitVec((i - j) + 1)),
            ZeroExtend(ext, exp) | SignExtend(ext, exp) => match exp.infer(tcx, ftcx) {
                Some(Ty::BitVec(sz)) => Some(Ty::BitVec(sz + ext)),
                _ => None,
            },
            Bvand(lhs, _)
            | Bvor(lhs, _)
            | Bvxor(lhs, _)
            | Bvnand(lhs, _)
            | Bvnor(lhs, _)
            | Bvxnor(lhs, _)
            | Bvadd(lhs, _)
            | Bvsub(lhs, _)
            | Bvmul(lhs, _)
            | Bvudiv(lhs, _)
            | Bvsdiv(lhs, _)
            | Bvurem(lhs, _)
            | Bvsrem(lhs, _)
            | Bvsmod(lhs, _)
            | Bvshl(lhs, _)
            | Bvlshr(lhs, _)
            | Bvashr(lhs, _) => lhs.infer(tcx, ftcx),
            Concat(lhs, rhs) => match (lhs.infer(tcx, ftcx), rhs.infer(tcx, ftcx)) {
                (Some(Ty::BitVec(lsz)), Some(Ty::BitVec(rsz))) => Some(Ty::BitVec(lsz + rsz)),
                (_, _) => None,
            },
            Ite(_, then_exp, _) => then_exp.infer(tcx, ftcx),
            App(f, _) => ftcx.get(f).map(|x| x.1.clone()),
            Select(array, _) => match array.infer(tcx, ftcx) {
                Some(Ty::Array(_, codom_ty)) => Some(*codom_ty),
                _ => None,
            },
            Store(array, _, _) => array.infer(tcx, ftcx),
            FPConstant(_, ebits, sbits) => Some(Ty::Float(*ebits, *sbits)),
            FPRoundingMode(_) => Some(Ty::RoundingMode),
            FPUnary(op, exp) => {
                if let Some(ty) = op.result_ty() {
                    Some(ty)
                } else {
                    exp.infer(tcx, ftcx)
                }
            }
            FPRoundingUnary(op, _, exp) => {
                if let Some(ty) = op.result_ty() {
                    Some(ty)
                } else {
                    exp.infer(tcx, ftcx)
                }
            }
            FPBinary(op, lhs, _) => {
                if op.is_predicate() {
                    Some(Ty::Bool)
                } else {
                    lhs.infer(tcx, ftcx)
                }
            }
            FPRoundingBinary(_, _, lhs, _) => lhs.infer(tcx, ftcx),
            FPfma(_, x, _, _) => x.infer(tcx, ftcx),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Def {
    DeclareConst(Sym, Ty),
    DeclareFun(Sym, Vec<Ty>, Ty),
    DefineConst(Sym, Exp<Sym>),
    DefineEnum(Name, usize),
    Assert(Exp<Sym>),
}

#[cfg(test)]
mod tests {
    use super::Def::*;
    use super::Exp::*;
    use super::*;
    use crate::smt::{Config, Context, Solver, Unsat};
    use crate::source_loc::SourceLoc;

    #[test]
    fn bits_to_i128_test() {
        assert_eq!(bits_to_i128(&extract_bits(bits64::<Sym>(123, 128))), Some(123));
    }

    fn exp_eval(syms: &[(Sym, Ty)], exp: Exp<Sym>) {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        for (sym, ty) in syms {
            solver.add(DeclareConst(*sym, ty.clone()));
        }
        let post_eval = exp.clone().eval();
        assert_ne!(exp, post_eval);
        solver.add(Assert(Neq(Box::new(exp.clone()), Box::new(post_eval.clone()))));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), Unsat, "Mismatch {:?} and {:?}", exp, post_eval);
    }

    fn exp_eval_unchanged(exp: Exp<Sym>) {
        assert_eq!(exp, exp.clone().eval());
    }

    #[test]
    fn exp_eval_tests() {
        let v0 = Sym::from_u32(0);
        let v1 = Sym::from_u32(1);

        exp_eval(&[(v0, Ty::Bool)], And(Box::new(Var(v0)), Box::new(Not(Box::new(Var(v0))))));
        exp_eval_unchanged(And(Box::new(Var(v0)), Box::new(Not(Box::new(Var(v1))))));
        exp_eval(&[(v0, Ty::Bool)], Or(Box::new(Var(v0)), Box::new(Not(Box::new(Var(v0))))));
        exp_eval_unchanged(Or(Box::new(Var(v0)), Box::new(Not(Box::new(Var(v1))))));
        exp_eval(&[], Concat(Box::new(bits64(0x1234, 16)), Box::new(bits64(0x5678, 16))));
        exp_eval(&[(v0, Ty::BitVec(4))], Bvor(Box::new(bits64(0, 4)), Box::new(Var(v0))));
        exp_eval(&[(v0, Ty::BitVec(4))], Bvand(Box::new(bits64(0, 4)), Box::new(Var(v0))));
        exp_eval(&[(v0, Ty::BitVec(96))], Bvor(Box::new(bits64(0, 96)), Box::new(Var(v0))));
        exp_eval(&[(v0, Ty::BitVec(96))], Bvand(Box::new(bits64(0, 96)), Box::new(Var(v0))));
        exp_eval(&[(v0, Ty::BitVec(4))], Bvor(Box::new(Var(v0)), Box::new(bits64(0, 4))));
        exp_eval(&[(v0, Ty::BitVec(4))], Bvand(Box::new(Var(v0)), Box::new(bits64(0, 4))));
        exp_eval(&[(v0, Ty::BitVec(96))], Bvor(Box::new(Var(v0)), Box::new(bits64(0, 96))));
        exp_eval(&[(v0, Ty::BitVec(96))], Bvand(Box::new(Var(v0)), Box::new(bits64(0, 96))));

        exp_eval(&[], Exp::ZeroExtend(2, Box::new(bits64(123, 32))));
        exp_eval(&[], Exp::ZeroExtend(2, Box::new(bits64(123, 64))));
        exp_eval(&[], Exp::ZeroExtend(2, Box::new(Bits(vec![true; 65]))));
        exp_eval(&[], Exp::SignExtend(2, Box::new(bits64(123, 32))));
        exp_eval(&[], Exp::SignExtend(2, Box::new(bits64(123, 64))));
        {
            let mut bits = vec![true; 65];
            *(bits.last_mut().unwrap()) = false;
            exp_eval(&[], Exp::SignExtend(2, Box::new(Bits(bits))));
        }
        exp_eval(&[], Exp::SignExtend(2, Box::new(bits64(0x80000123, 32))));
        exp_eval(&[], Exp::SignExtend(2, Box::new(bits64(0x8000000000000123, 64))));
        {
            let mut bits = vec![true; 65];
            *(bits.first_mut().unwrap()) = false;
            exp_eval(&[], Exp::SignExtend(2, Box::new(Bits(bits))));
        }

        exp_eval(&[], Bvshl(Box::new(bits64(5, 64)), Box::new(bits64(3, 64))));
        {
            let mut shift = vec![false; 64];
            shift[0] = true;
            shift[2] = true;
            exp_eval(&[], Bvshl(Box::new(bits64(5, 64)), Box::new(Bits(shift))));
        }
        {
            let mut bits = vec![false; 65];
            bits[0] = true;
            exp_eval(&[], Bvshl(Box::new(Bits(bits)), Box::new(bits64(5, 65))));
        }

        exp_eval(&[], Bvshl(Box::new(bits64(0x8000000000000005, 64)), Box::new(bits64(3, 64))));
        {
            let mut shift = vec![false; 64];
            shift[0] = true;
            shift[2] = true;
            exp_eval(&[], Bvshl(Box::new(bits64(0x8000000000000005, 64)), Box::new(Bits(shift))));
        }
        {
            let mut bits = vec![false; 65];
            bits[0] = true;
            bits[64] = true;
            exp_eval(&[], Bvshl(Box::new(Bits(bits)), Box::new(bits64(5, 65))));
        }
    }
}
