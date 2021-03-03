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

use std::collections::HashMap;
use std::fmt;
use std::ops::{BitAnd, BitOr, BitXor, Add, Sub, Shl, Shr};

use super::Sym;
use crate::bitvector::b64::B64;
use crate::bitvector::BV;
use crate::ir::EnumMember;

#[derive(Clone, Debug)]
pub enum Ty {
    Bool,
    BitVec(u32),
    Enum(usize),
    Array(Box<Ty>, Box<Ty>),
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Ty::*;
        match self {
            Bool => write!(f, "Bool"),
            BitVec(sz) => write!(f, "(_ BitVec {})", sz),
            Enum(e) => write!(f, "Enum{}", e),
            Array(dom, codom) => {
                write!(f, "(Array ")?;
                dom.fmt(f)?;
                write!(f, " ")?;
                codom.fmt(f)?;
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum Exp {
    Var(Sym),
    Bits(Vec<bool>),
    Bits64(B64),
    Enum(EnumMember),
    Bool(bool),
    Eq(Box<Exp>, Box<Exp>),
    Neq(Box<Exp>, Box<Exp>),
    And(Box<Exp>, Box<Exp>),
    Or(Box<Exp>, Box<Exp>),
    Not(Box<Exp>),
    Bvnot(Box<Exp>),
    Bvand(Box<Exp>, Box<Exp>),
    Bvor(Box<Exp>, Box<Exp>),
    Bvxor(Box<Exp>, Box<Exp>),
    Bvnand(Box<Exp>, Box<Exp>),
    Bvnor(Box<Exp>, Box<Exp>),
    Bvxnor(Box<Exp>, Box<Exp>),
    Bvneg(Box<Exp>),
    Bvadd(Box<Exp>, Box<Exp>),
    Bvsub(Box<Exp>, Box<Exp>),
    Bvmul(Box<Exp>, Box<Exp>),
    Bvudiv(Box<Exp>, Box<Exp>),
    Bvsdiv(Box<Exp>, Box<Exp>),
    Bvurem(Box<Exp>, Box<Exp>),
    Bvsrem(Box<Exp>, Box<Exp>),
    Bvsmod(Box<Exp>, Box<Exp>),
    Bvult(Box<Exp>, Box<Exp>),
    Bvslt(Box<Exp>, Box<Exp>),
    Bvule(Box<Exp>, Box<Exp>),
    Bvsle(Box<Exp>, Box<Exp>),
    Bvuge(Box<Exp>, Box<Exp>),
    Bvsge(Box<Exp>, Box<Exp>),
    Bvugt(Box<Exp>, Box<Exp>),
    Bvsgt(Box<Exp>, Box<Exp>),
    Extract(u32, u32, Box<Exp>),
    ZeroExtend(u32, Box<Exp>),
    SignExtend(u32, Box<Exp>),
    Bvshl(Box<Exp>, Box<Exp>),
    Bvlshr(Box<Exp>, Box<Exp>),
    Bvashr(Box<Exp>, Box<Exp>),
    Concat(Box<Exp>, Box<Exp>),
    Ite(Box<Exp>, Box<Exp>, Box<Exp>),
    App(Sym, Vec<Exp>),
    Select(Box<Exp>, Box<Exp>),
    Store(Box<Exp>, Box<Exp>, Box<Exp>),
}

#[allow(clippy::needless_range_loop)]
pub fn bits64(bits: u64, size: u32) -> Exp {
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

fn is_bits64(exp: &Exp) -> bool {
    matches!(exp, Exp::Bits64(_))
}

fn is_bits(exp: &Exp) -> bool {
    matches!(exp, Exp::Bits(_))
}

fn extract_bits64(exp: &Exp) -> B64 {
    match *exp {
        Exp::Bits64(bv) => bv,
        _ => unreachable!(),
    }
}

fn extract_bits(exp: Exp) -> Vec<bool> {
    match exp {
        Exp::Bits(bv) => bv,
        _ => unreachable!(),
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

fn eval_extract(hi: u32, lo: u32, exp: Box<Exp>) -> Exp {
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

fn eval_zero_extend(len: u32, exp: Box<Exp>) -> Exp {
    if is_bits64(&exp) {
        let bv = extract_bits64(&exp);
        Exp::Bits64(bv.zero_extend(bv.len() + len))
    } else {
        Exp::ZeroExtend(len, exp)
    }
}

fn eval_sign_extend(len: u32, exp: Box<Exp>) -> Exp {
    if is_bits64(&exp) {
        let bv = extract_bits64(&exp);
        Exp::Bits64(bv.sign_extend(bv.len() + len))
    } else {
        Exp::SignExtend(len, exp)
    }
}

impl Exp {
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
            Eq(mut lhs, mut rhs) => {
                *lhs = lhs.eval();
                *rhs = rhs.eval();
                Eq(lhs, rhs)
            }
            Bvand(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvand, B64::bitand, lhs, rhs),
            Bvor(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvor, B64::bitor, lhs, rhs),
            Bvxor(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvxor, B64::bitxor, lhs, rhs),
            Bvadd(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvadd, B64::add, lhs, rhs),
            Bvsub(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvsub, B64::sub, lhs, rhs),
            Bvlshr(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvlshr, B64::shr, lhs, rhs),
            Bvshl(mut lhs, mut rhs) => binary_eval!(Exp::eval, Bvshl, B64::shl, lhs, rhs),
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
            _ => self,
        }
    }

    /// Recursivly apply the supplied function to each sub-expression in a bottom-up order
    pub fn modify<F>(&mut self, f: &F)
    where
        F: Fn(&mut Exp),
    {
        use Exp::*;
        match self {
            Var(_) | Bits(_) | Bits64(_) | Enum { .. } | Bool(_) => (),
            Not(exp) | Bvnot(exp) | Bvneg(exp) | Extract(_, _, exp) | ZeroExtend(_, exp) | SignExtend(_, exp) => {
                exp.modify(f)
            }
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
            | Concat(lhs, rhs) => {
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
        };
        f(self)
    }

    /// Recursivly apply the supplied function to each sub-expression in a top down order
    pub fn modify_top_down<F>(&mut self, f: &F)
    where
        F: Fn(&mut Exp),
    {
        use Exp::*;
        f(self);
        match self {
            Var(_) | Bits(_) | Bits64(_) | Enum { .. } | Bool(_) => (),
            Not(exp) | Bvnot(exp) | Bvneg(exp) | Extract(_, _, exp) | ZeroExtend(_, exp) | SignExtend(_, exp) => {
                exp.modify(f)
            }
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
            | Concat(lhs, rhs) => {
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
        }
    }

    fn binary_commute_extract(self) -> Result<(fn (Box<Self>, Box<Self>) -> Self, Box<Self>, Box<Self>), Self> {
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
                Ok((op, lhs, rhs)) => {
                    *self = op(Box::new(Extract(*hi, *lo, lhs)), Box::new(Extract(*hi, *lo, rhs)))
                }
                Err(mut orig_exp) => {
                    std::mem::swap(&mut **exp, &mut orig_exp);
                }
            }
        }
    }

    pub fn subst_once_in_place(&mut self, substs: &mut HashMap<Sym, Option<Exp>>) {
        use Exp::*;
        match self {
            Var(v) => {
                if let Some(exp) = substs.get_mut(v) {
                    if let Some(exp) = exp.take() {
                        *self = exp
                    } else {
                        panic!("Tried to substitute twice in subst_once_in_place")
                    }
                }
            }
            Bits(_) | Bits64(_) | Enum { .. } | Bool(_) => (),
            Not(exp) | Bvnot(exp) | Bvneg(exp) | Extract(_, _, exp) | ZeroExtend(_, exp) | SignExtend(_, exp) => {
                exp.subst_once_in_place(substs)
            }
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
            | Concat(lhs, rhs) => {
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
            | Bvsgt(_, _) => Some(Ty::Bool),
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
        }
    }
}

#[derive(Clone, Debug)]
pub enum Def {
    DeclareConst(Sym, Ty),
    DeclareFun(Sym, Vec<Ty>, Ty),
    DefineConst(Sym, Exp),
    DefineEnum(Sym, usize),
    Assert(Exp),
}
