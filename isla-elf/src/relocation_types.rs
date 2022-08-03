// BSD 2-Clause License
//
// Copyright (c) 2021 Alasdair Armstrong
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

use std::ops;

use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::ir::{BitsSegment, Val};
use isla_lib::smt::{self, smtlib, Solver};
use isla_lib::source_loc::SourceLoc;

#[derive(Debug)]
pub enum Operation {
    S,
    A,
    P,
    Add(Box<Operation>, Box<Operation>),
    Sub(Box<Operation>, Box<Operation>),
    Page(Box<Operation>), // Page(X) = X & !0xFFF
}

pub fn page(op: Operation) -> Operation {
    Page(Box::new(op))
}

use Operation::*;

impl ops::Add<Operation> for Operation {
    type Output = Operation;

    fn add(self, rhs: Self) -> Self {
        Operation::Add(Box::new(self), Box::new(rhs))
    }
}

impl ops::Sub<Operation> for Operation {
    type Output = Operation;

    fn sub(self, rhs: Self) -> Self {
        Operation::Sub(Box::new(self), Box::new(rhs))
    }
}

impl Operation {
    pub fn eval(&self, symbol: u64, addend: i64, place: u64) -> u64 {
        match self {
            S => symbol,
            A => addend as u64,
            P => place,
            Add(lhs, rhs) => lhs.eval(symbol, addend, place) + rhs.eval(symbol, addend, place),
            Sub(lhs, rhs) => lhs.eval(symbol, addend, place) - rhs.eval(symbol, addend, place),
            Page(exp) => exp.eval(symbol, addend, place) & !0xFFF,
        }
    }

    pub fn smt(&self, symbol: smt::Sym, addend: i64, place: smt::Sym) -> smtlib::Exp<smt::Sym> {
        use smtlib::*;
        use Operation::*;

        match self {
            S => Exp::Var(symbol),
            A => Exp::Bits64(B64::from_u64(addend as u64)),
            P => Exp::Var(place),
            Add(lhs, rhs) => {
                Exp::Bvadd(Box::new(lhs.smt(symbol, addend, place)), Box::new(rhs.smt(symbol, addend, place)))
            }
            Sub(lhs, rhs) => {
                Exp::Bvsub(Box::new(lhs.smt(symbol, addend, place)), Box::new(rhs.smt(symbol, addend, place)))
            }
            Page(exp) => {
                Exp::Bvand(Box::new(exp.smt(symbol, addend, place)), Box::new(Exp::Bits64(B64::from_u64(!0xFFF))))
            }
        }
    }
}

pub type OverflowCheck = Option<(i64, i64)>;

/// Construct an overflow check in the range `-2^lo <= x < 2^hi`.
pub const fn bounds(lo: u32, hi: u32) -> OverflowCheck {
    Some((-i64::pow(2, lo), i64::pow(2, hi)))
}

#[derive(Copy, Clone, Debug)]
pub struct Slice {
    hi: u32,
    lo: u32,
}

pub const SLICE64: Slice = Slice { hi: 63, lo: 0 };
pub const SLICE32: Slice = Slice { hi: 31, lo: 0 };
pub const SLICE16: Slice = Slice { hi: 15, lo: 0 };

#[warn(clippy::len_without_is_empty)]
impl Slice {
    pub const fn new(hi: u32, lo: u32) -> Self {
        Slice { hi, lo }
    }

    #[allow(clippy::len_without_is_empty)]
    pub const fn len(self) -> u32 {
        (self.hi - self.lo) + 1
    }

    pub fn symbolic<B: BV>(self, x: smt::Sym, solver: &mut Solver<B>, info: SourceLoc) -> smt::Sym {
        use smtlib::*;
        solver.define_const(Exp::Extract(self.hi, self.lo, Box::new(Exp::Var(x))), info)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Immediate {
    NoImm,
    Imm2(u32, u32),
    Imm4(u32, u32, u32, u32),
}

use Immediate::*;

fn push_concrete<B: BV>(segments: &mut Vec<BitsSegment<B>>, bv: B, high: u32, low: u32) {
    assert!(high >= low);
    if (high - low) + 1 > 0 {
        segments.push(BitsSegment::Concrete(bv.extract(high, low).unwrap()))
    }
}

fn push_symbolic<B: BV>(segments: &mut Vec<BitsSegment<B>>, bv: smt::Sym) {
    segments.push(BitsSegment::Symbolic(bv))
}

impl Immediate {
    #[allow(clippy::len_without_is_empty)]
    pub const fn len(self) -> u32 {
        match self {
            NoImm => 32,
            Imm2(hi, lo) => (hi - lo) + 1,
            Imm4(hi1, lo1, hi2, lo2) => (hi1 - lo1) + (hi2 - lo2) + 2,
        }
    }

    /// Apply a symbolic relocation to a concrete opcode. A bitslice
    /// which must have the _exact width_ of all the immediate fields
    /// is taken from the result of a relocation operation (which we
    /// call X following ARM convention). This bitslice is used to
    /// create a `MixedBits` isla bitvector, where the immediate
    /// fields are symbolic bit segments.
    ///
    /// # Panics
    ///
    /// Panics if the slice length does not match the immediate
    /// lengths. Also panics if `opcode.len()` is not greater than or
    /// equal to `slice.len()` or `slice.len()` is not greater than 0.
    ///
    /// Panics if self is `NoImm` and slice is not `None`.
    pub fn symbolic<B: BV>(
        self,
        opcode: B,
        x: smt::Sym,
        slice: Slice,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Val<B> {
        use smtlib::*;

        assert!(slice.len() == self.len());
        assert!(opcode.len() >= slice.len() && slice.len() > 0);

        let val = match self {
            NoImm => Val::Symbolic(x),

            Imm2(hi, lo) => {
                let imm = slice.symbolic(x, solver, info);
                let mut segments = Vec::new();
                push_concrete(&mut segments, opcode, opcode.len() - 1, hi + 1);
                push_symbolic(&mut segments, imm);
                push_concrete(&mut segments, opcode, lo - 1, 0);
                Val::MixedBits(segments)
            }

            // This is for when the immediate is split into two
            // disjoint fields in the bitvector. The low part of the
            // immediate immlo might come before the high part of the
            // immediate immhi, e.g. the ADRP instruction in AArch64.
            Imm4(hi1, lo1, hi2, lo2) => {
                let x_slice = slice.symbolic(x, solver, info);
                let mid = hi2 - lo2;
                let immhi =
                    solver.define_const(Exp::Extract(self.len() - 1, mid + 1, Box::new(Exp::Var(x_slice))), info);
                let immlo = solver.define_const(Exp::Extract(mid, 0, Box::new(Exp::Var(x_slice))), info);
                let mut segments = Vec::new();
                if hi1 > hi2 {
                    // immhi before immlo in instruction
                    push_concrete(&mut segments, opcode, opcode.len() - 1, hi1 + 1);
                    push_symbolic(&mut segments, immhi);
                    push_concrete(&mut segments, opcode, lo1 - 1, hi2 + 1);
                    push_symbolic(&mut segments, immlo);
                    push_concrete(&mut segments, opcode, lo2 - 1, 0);
                } else {
                    // immlo before immhi in instruction
                    push_concrete(&mut segments, opcode, opcode.len() - 1, hi2 + 1);
                    push_symbolic(&mut segments, immlo);
                    push_concrete(&mut segments, opcode, lo2 - 1, hi1 + 1);
                    push_symbolic(&mut segments, immhi);
                    push_concrete(&mut segments, opcode, lo1 - 1, 0);
                }
                Val::MixedBits(segments)
            }
        };

        // Check that the length is what we expect
        assert!(isla_lib::primop_util::length_bits(&val, solver, info).unwrap() == opcode.len());

        val
    }
}

pub struct TableEntry<C> {
    pub code: C,
    pub operation: Operation,
    pub overflow_check: OverflowCheck,
    pub slice: Slice,
    pub immediate: Immediate,
}

pub fn entry<C>(
    code: C,
    operation: Operation,
    overflow_check: OverflowCheck,
    slice: Slice,
    immediate: Immediate,
) -> TableEntry<C> {
    TableEntry { code, operation, overflow_check, slice, immediate }
}

pub struct SymbolicRelocation<B> {
    pub symbol: smt::Sym,
    pub place: smt::Sym,
    pub opcode: Val<B>,
}

impl<C> TableEntry<C> {
    pub fn symbolic<B: BV>(
        &self,
        opcode: B,
        addend: i64,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> SymbolicRelocation<B> {
        use smtlib::*;
        use Exp::*;

        let symbol = solver.declare_const(Ty::BitVec(64), info);
        let place = solver.declare_const(Ty::BitVec(64), info);

        let x = solver.define_const(self.operation.smt(symbol, addend, place), info);

        match self.overflow_check {
            None => (),
            Some((lo, hi)) => {
                solver.assert(Bvsle(Box::new(Bits64(B64::from_u64(lo as u64))), Box::new(Exp::Var(x))));
                solver.assert(Bvslt(Box::new(Exp::Var(x)), Box::new(Bits64(B64::from_u64(hi as u64)))));
            }
        }

        let opcode_value = self.immediate.symbolic(opcode, x, self.slice, solver, info);

        SymbolicRelocation { symbol, place, opcode: opcode_value }
    }
}
