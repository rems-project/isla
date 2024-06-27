// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
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

use std::collections::{hash_map, HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use isla_lib::bitvector::BV;
use isla_lib::error::ExecError;
use isla_lib::ir::{Name, Reset, Symtab, Val};
use isla_lib::memory::Memory;
use isla_lib::smt::Solver;
use isla_lib::source_loc::SourceLoc;
use isla_lib::{primop, zencode};

use super::{label_from_objdump, Objdump};
use crate::page_table::{self, PageAttrs, S1PageAttrs, S2PageAttrs, TranslationTableWalk, VirtualAddress};

pub enum ExpParseError {
    Lex { pos: usize },
    Int { error: std::num::ParseIntError },
    NoRegister { name: String },
    NoAddress { name: String },
}

impl fmt::Display for ExpParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ExpParseError::*;
        match self {
            Lex { pos } => write!(f, "Lexical error at position: {}", pos),
            Int { error } => write!(f, "{}", error),
            NoRegister { name } => write!(f, "No register {} in architecture", name),
            NoAddress { name } => write!(f, "No address {} in litmus file", name),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Loc<A> {
    Register { reg: Name, thread_id: usize },
    LastWriteTo { address: A, bytes: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exp<A> {
    EqLoc(Loc<A>, Box<Exp<A>>),
    Loc(A),
    Label(String),
    True,
    False,
    Bin(String),
    Hex(String),
    Bits64(u64, u32),
    Nat(u64),
    And(Vec<Exp<A>>),
    Or(Vec<Exp<A>>),
    Not(Box<Exp<A>>),
    App(String, Vec<Exp<A>>, HashMap<String, Exp<A>>),
    Implies(Box<Exp<A>>, Box<Exp<A>>),
}

pub fn translation_table_walk<B: BV>(
    mut args: Vec<Val<B>>,
    memory: &Memory<B>,
    caller: &str,
) -> Result<TranslationTableWalk, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type(
            format!("{} must have two arguments ({} provided)", caller, args.len()),
            SourceLoc::unknown(),
        ));
    }

    let table_addr = args.pop().unwrap();
    let va = args.pop().unwrap();

    let va = if let Val::Bits(bv) = va {
        VirtualAddress::from_u64(bv.lower_u64())
    } else {
        return Err(ExecError::Type(
            format!("Virtual address {:?} in {} must be a concrete bitvector", va, caller),
            SourceLoc::unknown(),
        ));
    };

    let table_addr = if let Val::Bits(bv) = table_addr {
        bv.lower_u64()
    } else {
        return Err(ExecError::Type(
            format!("Table address {:?} in {} must be a concrete bitvector", table_addr, caller),
            SourceLoc::unknown(),
        ));
    };

    page_table::initial_translation_table_walk(va, table_addr, memory)
}

pub struct KwArgs<B> {
    kw_args: HashMap<String, Val<B>>,
}

impl<B: BV> KwArgs<B> {
    pub fn new() -> Self {
        KwArgs { kw_args: HashMap::new() }
    }

    pub fn remove(&mut self, caller: &str, kw: &str) -> Result<Val<B>, ExecError> {
        self.kw_args.remove(kw).ok_or_else(|| {
            ExecError::Type(format!("{} must have a {} keyword argument", caller, kw), SourceLoc::unknown())
        })
    }

    pub fn remove_or(&mut self, kw: &str, or: Val<B>) -> (bool, Val<B>) {
        if let Some(val) = self.kw_args.remove(kw) {
            (true, val)
        } else {
            (false, or)
        }
    }

    pub fn drain(&mut self) -> hash_map::Drain<'_, String, Val<B>> {
        self.kw_args.drain()
    }
}

impl<B: BV> Default for KwArgs<B> {
    fn default() -> Self {
        Self::new()
    }
}

pub type LitmusFn<B> = fn(Vec<Val<B>>, KwArgs<B>, &Memory<B>, &mut Solver<B>) -> Result<Val<B>, ExecError>;

fn pte0<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, "pte0")?;
    Ok(Val::Bits(B::from_u64(walk.l0pte)))
}

fn pte1<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, "pte1")?;
    Ok(Val::Bits(B::from_u64(walk.l1pte)))
}

fn pte2<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, "pte2")?;
    Ok(Val::Bits(B::from_u64(walk.l2pte)))
}

fn pte3<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, "pte3")?;
    Ok(Val::Bits(B::from_u64(walk.l3pte)))
}

fn desc0<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, "desc0")?;
    Ok(Val::Bits(B::from_u64(walk.l0desc)))
}

fn desc1<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, "desc1")?;
    Ok(Val::Bits(B::from_u64(walk.l1desc)))
}

fn desc2<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, "desc2")?;
    Ok(Val::Bits(B::from_u64(walk.l2desc)))
}

fn desc3<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, "desc3")?;
    Ok(Val::Bits(B::from_u64(walk.l3desc)))
}

pub fn pa<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, "pa")?;
    Ok(Val::Bits(B::from_u64(walk.pa)))
}

pub fn pa_u64<B: BV>(args: Vec<Val<B>>, _: KwArgs<B>, memory: &Memory<B>, _: &mut Solver<B>) -> Result<u64, ExecError> {
    let walk = translation_table_walk(args, memory, "pa_u64")?;
    Ok(walk.pa)
}

fn bvand<B: BV>(
    mut args: Vec<Val<B>>,
    _: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type(
            format!("bvand must have two arguments ({} provided)", args.len()),
            SourceLoc::unknown(),
        ));
    }

    let rhs = args.pop().unwrap();
    let lhs = args.pop().unwrap();

    primop::and_bits(lhs, rhs, solver, SourceLoc::unknown())
}

fn bvor<B: BV>(
    mut args: Vec<Val<B>>,
    _: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type(
            format!("bvor must have two arguments ({} provided)", args.len()),
            SourceLoc::unknown(),
        ));
    }

    let rhs = args.pop().unwrap();
    let lhs = args.pop().unwrap();

    primop::or_bits(lhs, rhs, solver, SourceLoc::unknown())
}

fn bvxor<B: BV>(
    mut args: Vec<Val<B>>,
    _: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type(
            format!("bvxor must have two arguments ({} provided)", args.len()),
            SourceLoc::unknown(),
        ));
    }

    let rhs = args.pop().unwrap();
    let lhs = args.pop().unwrap();

    primop::xor_bits(lhs, rhs, solver, SourceLoc::unknown())
}

fn bvlshr<B: BV>(
    mut args: Vec<Val<B>>,
    _: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type(
            format!("bvlshr must have two arguments ({} provided)", args.len()),
            SourceLoc::unknown(),
        ));
    }

    let rhs = args.pop().unwrap();
    let lhs = args.pop().unwrap();

    primop::shift_bits_right(lhs, rhs, solver, SourceLoc::unknown())
}

fn bvshl<B: BV>(
    mut args: Vec<Val<B>>,
    _: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type(
            format!("bvshl must have two arguments ({} provided)", args.len()),
            SourceLoc::unknown(),
        ));
    }

    let rhs = args.pop().unwrap();
    let lhs = args.pop().unwrap();

    primop::shift_bits_left(lhs, rhs, solver, SourceLoc::unknown())
}

#[allow(clippy::manual_range_contains)]
fn index<B: BV>(_: Vec<Val<B>>, mut kw_args: KwArgs<B>, _: &Memory<B>, _: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let level = kw_args.remove("index", "level")?;
    let (have_va, va) = kw_args.remove_or("va", Val::Bits(B::from_u64(0)));
    let (have_ipa, ipa) = kw_args.remove_or("ipa", Val::Bits(B::from_u64(0)));

    if have_va == have_ipa {
        return Err(ExecError::Type(
            "index must have either a va or an ipa argument".to_string(),
            SourceLoc::unknown(),
        ));
    }

    match (if have_va { va } else { ipa }, level) {
        (Val::Bits(bv), Val::I128(i)) if 0 <= i && i <= 3 => {
            Ok(Val::I128(VirtualAddress::from_u64(bv.lower_u64()).level_index(i as u64) as i128))
        }
        (_, _) => Err(ExecError::Type(
            "index must have concrete arguments, with index being between 0 and 3".to_string(),
            SourceLoc::unknown(),
        )),
    }
}

#[allow(clippy::manual_range_contains)]
fn offset<B: BV>(
    _: Vec<Val<B>>,
    mut kw_args: KwArgs<B>,
    _: &Memory<B>,
    _: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    let level = kw_args.remove("offset", "level")?;
    let (have_va, va) = kw_args.remove_or("va", Val::Bits(B::from_u64(0)));
    let (have_ipa, ipa) = kw_args.remove_or("ipa", Val::Bits(B::from_u64(0)));

    if have_va == have_ipa {
        return Err(ExecError::Type(
            "offset must have either a va or an ipa argument".to_string(),
            SourceLoc::unknown(),
        ));
    }

    match (if have_va { va } else { ipa }, level) {
        (Val::Bits(bv), Val::I128(i)) if 0 <= i && i <= 3 => {
            let i = i as u64;
            let index = VirtualAddress::from_u64(bv.lower_u64()).level_index(i);
            Ok(Val::Bits(B::from_u64(index as u64 * 8)))
        }
        (_, _) => Err(ExecError::Type(
            "index must have concrete arguments, with index being between 0 and 3".to_string(),
            SourceLoc::unknown(),
        )),
    }
}

fn ttbr<B: BV>(
    _: Vec<Val<B>>,
    mut kw_args: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    let base = kw_args.remove("ttbr", "base")?;
    let (have_asid, asid) = kw_args.remove_or("asid", Val::Bits(B::from_u16(0)));
    let (have_vmid, vmid) = kw_args.remove_or("vmid", Val::Bits(B::from_u16(0)));
    let (_, cnp) = kw_args.remove_or("CnP", Val::Bits(B::BIT_ZERO));

    if have_asid == have_vmid {
        return Err(ExecError::Type(
            "ttbr must have either a vmid or an asid argument".to_string(),
            SourceLoc::unknown(),
        ));
    }

    if have_asid {
        let bits = primop::set_slice_internal(base, Val::I128(48), asid, solver, SourceLoc::unknown())?;
        primop::set_slice_internal(bits, Val::I128(0), cnp, solver, SourceLoc::unknown())
    } else {
        let bits = primop::set_slice_internal(base, Val::I128(48), vmid, solver, SourceLoc::unknown())?;
        primop::set_slice_internal(bits, Val::I128(0), cnp, solver, SourceLoc::unknown())
    }
}

fn asid<B: BV>(
    mut pos_args: Vec<Val<B>>,
    _: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    if let Some(asid) = pos_args.pop() {
        primop::set_slice_internal(Val::Bits(B::from_u64(0)), Val::I128(48), asid, solver, SourceLoc::unknown())
    } else {
        Err(ExecError::Type("asid(v) takes 1 argument".to_string(), SourceLoc::unknown()))
    }
}

fn mkdesc<B: BV>(
    _: Vec<Val<B>>,
    mut kw_args: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    let (have_table, table) = kw_args.remove_or("table", Val::Bits(B::from_u64(0)));
    let (have_oa, oa) = kw_args.remove_or("oa", Val::Bits(B::from_u16(0)));

    if have_table == have_oa {
        return Err(ExecError::Type(
            "mkdesc must have either a table or an oa argument".to_string(),
            SourceLoc::unknown(),
        ));
    }

    if have_table {
        primop::or_bits(table, Val::Bits(B::from_u64(0b11)), solver, SourceLoc::unknown())
    } else {
        let (attrs, _) = S1PageAttrs::default().bits();
        primop::or_bits(
            primop::or_bits(oa, Val::Bits(B::from_u64(0b01)), solver, SourceLoc::unknown())?,
            Val::Bits(B::from_u64(attrs)),
            solver,
            SourceLoc::unknown(),
        )
    }
}

fn mkdesc3<B: BV, P: Default + PageAttrs>(
    _: Vec<Val<B>>,
    mut kw_args: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    let oa = kw_args.remove("mkdesc3", "oa")?;
    let mut attrs = P::default();

    for (attr, arg) in kw_args.drain() {
        let arg = match arg {
            Val::Bits(bv) => bv,
            _ => {
                return Err(ExecError::Type(
                    format!("mkdesc3 attribute {} must be a bitvector", attr),
                    SourceLoc::unknown(),
                ))
            }
        };
        if attrs.set_field(&attr, arg).is_none() {
            return Err(ExecError::Type(
                format!("mkdesc3 attribute {} length is incorrect, or attribute does not exist", attr),
                SourceLoc::unknown(),
            ));
        }
    }

    let (attrs, _) = attrs.bits();

    primop::or_bits(
        primop::or_bits(oa, Val::Bits(B::from_u64(0b11)), solver, SourceLoc::unknown())?,
        Val::Bits(B::from_u64(attrs)),
        solver,
        SourceLoc::unknown(),
    )
}

fn page<B: BV>(
    mut args: Vec<Val<B>>,
    _: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    if args.len() != 1 {
        return Err(ExecError::Type("page must have 1 argument".to_string(), SourceLoc::unknown()));
    }

    let bits = args.pop().unwrap();

    primop::subrange_internal(bits, Val::I128(48), Val::I128(12), solver, SourceLoc::unknown())
}

fn extz<B: BV>(
    mut args: Vec<Val<B>>,
    _: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type("extz must have 2 arguments".to_string(), SourceLoc::unknown()));
    }

    let len = args.pop().unwrap();
    let bits = args.pop().unwrap();

    primop::zero_extend(bits, len, solver, SourceLoc::unknown())
}

fn exts<B: BV>(
    mut args: Vec<Val<B>>,
    _: KwArgs<B>,
    _: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type("exts must have 2 arguments".to_string(), SourceLoc::unknown()));
    }

    let len = args.pop().unwrap();
    let bits = args.pop().unwrap();

    primop::sign_extend(bits, len, solver, SourceLoc::unknown())
}

pub fn litmus_primops<B: BV>() -> HashMap<String, LitmusFn<B>> {
    let mut primops = HashMap::new();
    primops.insert("pte0".to_string(), pte0 as LitmusFn<B>);
    primops.insert("pte1".to_string(), pte1 as LitmusFn<B>);
    primops.insert("pte2".to_string(), pte2 as LitmusFn<B>);
    primops.insert("pte3".to_string(), pte3 as LitmusFn<B>);
    primops.insert("desc0".to_string(), desc0 as LitmusFn<B>);
    primops.insert("desc1".to_string(), desc1 as LitmusFn<B>);
    primops.insert("desc2".to_string(), desc2 as LitmusFn<B>);
    primops.insert("desc3".to_string(), desc3 as LitmusFn<B>);
    primops.insert("pa".to_string(), pa as LitmusFn<B>);
    primops.insert("page".to_string(), page as LitmusFn<B>);
    primops.insert("extz".to_string(), extz as LitmusFn<B>);
    primops.insert("exts".to_string(), exts as LitmusFn<B>);
    primops.insert("ttbr".to_string(), ttbr as LitmusFn<B>);
    primops.insert("asid".to_string(), asid as LitmusFn<B>);
    primops.insert("vmid".to_string(), asid as LitmusFn<B>);
    primops.insert("mkdesc1".to_string(), mkdesc as LitmusFn<B>);
    primops.insert("mkdesc2".to_string(), mkdesc as LitmusFn<B>);
    primops.insert("mkdesc3".to_string(), mkdesc3::<B, S1PageAttrs> as LitmusFn<B>);
    primops.insert("s2mkdesc3".to_string(), mkdesc3::<B, S2PageAttrs> as LitmusFn<B>);
    primops.insert("bvand".to_string(), bvand as LitmusFn<B>);
    primops.insert("bvor".to_string(), bvor as LitmusFn<B>);
    primops.insert("bvxor".to_string(), bvxor as LitmusFn<B>);
    primops.insert("bvlshr".to_string(), bvlshr as LitmusFn<B>);
    primops.insert("bvshl".to_string(), bvshl as LitmusFn<B>);
    primops.insert("index".to_string(), index as LitmusFn<B>);
    primops.insert("offset".to_string(), offset as LitmusFn<B>);
    primops
}

pub enum Partial<A, B> {
    Unevaluated(Exp<A>),
    Evaluated(Val<B>),
}

impl<A, B: BV> Partial<A, B> {
    pub fn into_exp(self) -> Result<Exp<A>, ExecError> {
        match self {
            Partial::Unevaluated(exp) => Ok(exp),
            Partial::Evaluated(val) => match val {
                Val::Bits(bv) => Ok(Exp::Bits64(bv.lower_u64(), bv.len())),
                Val::Bool(true) => Ok(Exp::True),
                Val::Bool(false) => Ok(Exp::False),
                Val::I128(n) => Ok(Exp::Nat(n as u64)),
                _ => Err(ExecError::Type("Cannot partially evaluate".to_string(), SourceLoc::unknown())),
            },
        }
    }

    fn unwrap(self) -> Val<B> {
        match self {
            Partial::Unevaluated(_) => panic!("Attemped to unwrap unevaluated value"),
            Partial::Evaluated(val) => val,
        }
    }

    fn is_evaluated(&self) -> bool {
        matches!(self, Partial::Evaluated(_))
    }
}

pub fn eval_loc(loc: &Loc<String>, physical_addrs: &HashMap<String, u64>) -> Loc<u64> {
    match loc {
        Loc::LastWriteTo { address, bytes } => {
            if let Some(pa) = physical_addrs.get(address) {
                Loc::LastWriteTo { address: *pa, bytes: *bytes }
            } else {
                // FIXME: Proper error
                Loc::LastWriteTo { address: 0, bytes: *bytes }
            }
        }
        Loc::Register { reg, thread_id } => Loc::Register { reg: *reg, thread_id: *thread_id },
    }
}

pub fn partial_eval<B: BV>(
    exp: &Exp<String>,
    memory: &Memory<B>,
    addrs: &HashMap<String, u64>,
    pas: &HashMap<String, u64>,
    objdump: &Objdump,
    solver: &mut Solver<B>,
) -> Result<Partial<u64, B>, ExecError> {
    use Partial::*;
    let primops = litmus_primops();
    match exp {
        Exp::EqLoc(loc, exp) => Ok(Unevaluated(Exp::EqLoc(
            eval_loc(loc, pas),
            Box::new(partial_eval(exp, memory, addrs, pas, objdump, solver)?.into_exp()?),
        ))),

        Exp::Loc(addr) => {
            let bits = addrs
                .get(addr)
                .copied()
                .ok_or_else(|| ExecError::Type(format!("No address {} found", addr), SourceLoc::unknown()))?;
            Ok(Evaluated(Val::Bits(B::from_u64(bits))))
        }

        Exp::Label(label) => {
            let addr = label_from_objdump(label, objdump)
                .ok_or_else(|| ExecError::Type(format!("No label {} found", label), SourceLoc::unknown()))?;
            Ok(Evaluated(Val::Bits(B::from_u64(addr))))
        }

        Exp::True => Ok(Evaluated(Val::Bool(true))),

        Exp::False => Ok(Evaluated(Val::Bool(false))),

        Exp::Bits64(bits, len) => Ok(Evaluated(Val::Bits(B::new(*bits, *len)))),

        Exp::Nat(n) => Ok(Evaluated(Val::I128(*n as i128))),

        Exp::Bin(bin) => {
            let len = bin.len();
            if len <= 64 {
                Ok(Evaluated(Val::Bits(B::new(u64::from_str_radix(bin, 2).unwrap(), len as u32))))
            } else {
                Err(ExecError::Unimplemented)
            }
        }

        Exp::Hex(hex) => {
            let len = hex.len();
            if len <= 16 {
                Ok(Evaluated(Val::Bits(B::new(u64::from_str_radix(hex, 16).unwrap(), len as u32 * 4))))
            } else {
                Err(ExecError::Unimplemented)
            }
        }

        Exp::App(f, args, kw_args) => {
            let mut args: Vec<Partial<u64, B>> = args
                .iter()
                .map(|arg| partial_eval(arg, memory, addrs, pas, objdump, solver))
                .collect::<Result<_, _>>()?;
            let mut kw_args: HashMap<String, Partial<u64, B>> = kw_args
                .iter()
                .map(|(name, arg)| Ok((name.clone(), partial_eval(arg, memory, addrs, pas, objdump, solver)?)))
                .collect::<Result<_, _>>()?;

            if args.iter().all(|arg| arg.is_evaluated()) && kw_args.values().all(|arg| arg.is_evaluated()) {
                let f = primops
                    .get(f)
                    .ok_or_else(|| ExecError::Type(format!("Unknown function {}", f), SourceLoc::unknown()))?;
                Ok(Evaluated(f(
                    args.drain(..).map(|arg| arg.unwrap()).collect(),
                    KwArgs { kw_args: kw_args.drain().map(|(kw, arg)| (kw, arg.unwrap())).collect() },
                    memory,
                    solver,
                )?))
            } else {
                Ok(Unevaluated(Exp::App(
                    f.clone(),
                    args.drain(..).map(|arg| arg.into_exp()).collect::<Result<_, _>>()?,
                    kw_args.drain().map(|(kw, arg)| Ok((kw, arg.into_exp()?))).collect::<Result<_, _>>()?,
                )))
            }
        }

        Exp::And(exps) => Ok(Unevaluated(Exp::And(
            exps.iter()
                .map(|exp| partial_eval(exp, memory, addrs, pas, objdump, solver).and_then(Partial::into_exp))
                .collect::<Result<_, _>>()?,
        ))),

        Exp::Or(exps) => Ok(Unevaluated(Exp::Or(
            exps.iter()
                .map(|exp| partial_eval(exp, memory, addrs, pas, objdump, solver).and_then(Partial::into_exp))
                .collect::<Result<_, _>>()?,
        ))),

        Exp::Implies(exp1, exp2) => Ok(Unevaluated(Exp::Implies(
            Box::new(partial_eval(exp1, memory, addrs, pas, objdump, solver)?.into_exp()?),
            Box::new(partial_eval(exp2, memory, addrs, pas, objdump, solver)?.into_exp()?),
        ))),

        Exp::Not(exp) => {
            Ok(Unevaluated(Exp::Not(Box::new(partial_eval(exp, memory, addrs, pas, objdump, solver)?.into_exp()?))))
        }
    }
}

pub fn eval<B: BV>(
    exp: &Exp<String>,
    memory: &Memory<B>,
    addrs: &HashMap<String, u64>,
    objdump: &Objdump,
    solver: &mut Solver<B>,
) -> Result<Val<B>, ExecError> {
    match partial_eval(exp, memory, addrs, &HashMap::new(), objdump, solver)? {
        Partial::Evaluated(val) => Ok(val),
        Partial::Unevaluated(_) => Err(ExecError::Unimplemented),
    }
}

pub fn reset_eval<B: BV>(exp: &Exp<String>, addrs: &HashMap<String, u64>, objdump: &Objdump) -> Reset<B> {
    let exp = exp.clone();
    let addrs = addrs.clone();
    let objdump = objdump.clone();
    Arc::new(move |memory, _, solver| eval(&exp, memory, &addrs, &objdump, solver))
}

pub fn collect_locs<'litmus>(exp: &'litmus Exp<String>, target: &mut HashSet<&'litmus Loc<String>>) {
    use Exp::*;
    match exp {
        EqLoc(loc, exp) => {
            target.insert(loc);
            collect_locs(exp, target);
        }
        Loc(_) | Label(_) | True | False | Bin(_) | Hex(_) | Bits64(_, _) | Nat(_) => (),
        And(v) => v.iter().for_each(|e| collect_locs(e, target)),
        Or(v) => v.iter().for_each(|e| collect_locs(e, target)),
        Not(e) => collect_locs(e, target),
        App(_, args, kwargs) => args.iter().chain(kwargs.values()).for_each(|e| collect_locs(e, target)),
        Implies(lhs, rhs) => {
            collect_locs(lhs, target);
            collect_locs(rhs, target);
        }
    }
}

// === impl Display for Loc ===

pub struct LocDisplay<'l, 's, 'ir, A: fmt::Display> {
    loc: &'l Loc<A>,
    symtab: &'s Symtab<'ir>,
}

impl<'l, 's, 'ir, A: fmt::Display> LocDisplay<'l, 's, 'ir, A> {
    fn new(loc: &'l Loc<A>, symtab: &'s Symtab<'ir>) -> Self {
        Self { loc, symtab }
    }
}

impl<'l, 's, 'ir, A: fmt::Display> fmt::Display for LocDisplay<'l, 's, 'ir, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Loc::*;
        match self.loc {
            Register { reg, thread_id } => {
                let unmangled = self.symtab.to_str_demangled(*reg);
                let reg_name = zencode::try_decode(unmangled).unwrap_or(unmangled.to_string());
                write!(f, "{}:{}", thread_id, reg_name)
            }
            LastWriteTo { address, .. } => {
                write!(f, "{}", address)
            }
        }
    }
}

impl<A: fmt::Display> Loc<A> {
    pub fn display<'l, 's, 'ir>(&'l self, symtab: &'s Symtab<'ir>) -> LocDisplay<'l, 's, 'ir, A> {
        LocDisplay::new(self, symtab)
    }
}

// === impl Display for Exp ===

pub struct ExpDisplay<'e, 's, 'ir, A: fmt::Display> {
    exp: &'e Exp<A>,
    symtab: &'s Symtab<'ir>,
    precedence: usize,
}

impl<'e, 's, 'ir, A: fmt::Display> ExpDisplay<'e, 's, 'ir, A> {
    fn new(exp: &'e Exp<A>, symtab: &'s Symtab<'ir>, precedence: usize) -> Self {
        Self { exp, symtab, precedence }
    }
}

impl<'e, 's, 'ir, A: fmt::Display> fmt::Display for ExpDisplay<'e, 's, 'ir, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Exp::*;

        if self.precedence > self.exp.precedence() {
            write!(f, "(")?;
        }

        match self.exp {
            EqLoc(loc, val) => {
                write!(f, "{}={}", loc.display(self.symtab), val.display(self.symtab, self.exp.precedence()))
            }
            Loc(l) => {
                write!(f, "{}", l)
            }
            Label(l) => write!(f, "{}:", l),
            True => write!(f, "true"),
            False => write!(f, "false"),
            Bin(s) => write!(f, "{}", s),
            Hex(s) => write!(f, "{}", s),
            Bits64(b, _) => write!(f, "{:x}", b),
            Nat(n) => write!(f, "{}", n),
            And(elems) => {
                let elems: Vec<String> =
                    elems.iter().map(|e| format!("{}", e.display(self.symtab, e.precedence()))).collect();
                write!(f, "{}", elems.join(" /\\ "))
            }
            Or(elems) => {
                let elems: Vec<String> =
                    elems.iter().map(|e| format!("{}", e.display(self.symtab, e.precedence()))).collect();
                write!(f, "{}", elems.join(" \\/ "))
            }
            Not(e) => {
                write!(f, "{}", e.display(self.symtab, self.exp.precedence()))
            }
            App(name, args, kwargs) => {
                let args: Vec<String> = args
                    .iter()
                    .map(|e| format!("{}", e.display(self.symtab, e.precedence())))
                    .chain(kwargs.iter().map(|(kw, e)| format!("{}={}", kw, e.display(self.symtab, e.precedence()))))
                    .collect();
                write!(f, "{}({})", name, args.join(", "))
            }
            Implies(lhs, rhs) => {
                write!(
                    f,
                    "{}-->{},",
                    lhs.display(self.symtab, lhs.precedence()),
                    rhs.display(self.symtab, rhs.precedence())
                )
            }
        }?;

        if self.precedence > self.exp.precedence() {
            write!(f, ")")?;
        }

        Ok(())
    }
}

impl<'e, 's, 'ir, A: fmt::Display> Exp<A> {
    pub fn display(&'e self, symtab: &'s Symtab<'ir>, precedence: usize) -> ExpDisplay<'e, 's, 'ir, A> {
        ExpDisplay::new(self, symtab, precedence)
    }
}

impl<A> Exp<A> {
    /// Relative operator precedence of the node
    /// lower number = higher precedence
    pub fn precedence(&self) -> usize {
        use Exp::*;
        match self {
            Loc(_) | EqLoc(_, _) | Label(_) | True | False | Bin(_) | Hex(_) | Bits64(_, _) | Nat(_) => 0,
            App(_, _, _) => 1,
            Not(_) => 2,
            And(_) => 3,
            Or(_) => 4,
            Implies(_, _) => 5,
        }
    }
}
