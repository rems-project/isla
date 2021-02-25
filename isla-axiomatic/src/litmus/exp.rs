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

use isla_lib::bitvector::{bzhi_u64, BV};
use isla_lib::error::ExecError;
use isla_lib::ir::{Name, Reset, Val};
use isla_lib::memory::Memory;
use isla_lib::smt::Solver;
use isla_lib::primop;

use crate::page_table::VirtualAddress;

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Loc {
    Register { reg: Name, thread_id: usize },
    LastWriteTo { address: u64, bytes: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exp {
    EqLoc(Loc, Box<Exp>),
    True,
    False,
    Bin(String),
    Hex(String),
    Bits64(u64, u32),
    Nat(u64),
    And(Vec<Exp>),
    Or(Vec<Exp>),
    Not(Box<Exp>),
    App(String, Vec<Exp>),
    Implies(Box<Exp>, Box<Exp>),
}

pub type LitmusFn<B> = fn(Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError>;

pub struct TranslationTableWalk {
    l0pte: u64,
    l0desc: u64,
    l1pte: u64,
    l1desc: u64,
    l2pte: u64,
    l2desc: u64,
    l3pte: u64,
    l3desc: u64,
    pa: u64,
}

fn desc_to_u64<B: BV>(desc: Val<B>) -> Result<u64, ExecError> {
    match desc {
        Val::Bits(bv) => Ok(bv.lower_u64()),
        _ => Err(ExecError::BadRead("symbolic descriptor")),
    }
}

/// To compute the various bits of translation table information we
/// might need in the initial state, we have a function that does a
/// simple translation table walk and records each intermedate
/// descriptor address in the l0pte to l3pte fields of the
/// `TranslationTableWalk` struct, and the descriptor values in the
/// l0desc to l3desc fields. All the flags in the descriptors are
/// ignored.
///
/// For now we assume a 4K page size.
pub fn translation_table_walk<B: BV>(
    mut args: Vec<Val<B>>,
    memory: &Memory<B>,
    _solver: &mut Solver<B>,
) -> Result<TranslationTableWalk, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type(format!("translate must have two arguments ({} provided)", args.len())))
    }
    
    let table_addr = args.pop().unwrap();
    let va = args.pop().unwrap();

    let va = if let Val::Bits(bv) = va {
        VirtualAddress::from_u64(bv.lower_u64())
    } else {
        return Err(ExecError::Type(format!("virtual address {:?} is not a concrete bitvector for translation", va)))
    };

    let table_addr = if let Val::Bits(bv) = table_addr {
        bv.lower_u64()
    } else {
        return Err(ExecError::Type(format!(
            "Table address {:?} is not a concrete bitvector for translation",
            table_addr
        )));
    };

    eprintln!("va = {:?}, table_addr = 0x{:x}", va, table_addr);

    let l0pte = table_addr + va.level_index(0) as u64 * 8;
    eprintln!("l0pte = 0x{:x}", l0pte);
    let l0desc = memory.read_initial(l0pte, 8).and_then(desc_to_u64)?;
    let l1pte = (l0desc & !0b11) + va.level_index(1) as u64 * 8;
    eprintln!("l1pte = 0x{:x}", l1pte);
    let l1desc = memory.read_initial(l1pte, 8).and_then(desc_to_u64)?;
    let l2pte = (l1desc & !0b11) + va.level_index(2) as u64 * 8;
    eprintln!("l2pte = 0x{:x}", l2pte);
    let l2desc = memory.read_initial(l2pte, 8).and_then(desc_to_u64)?;
    let l3pte = (l2desc & !0b11) + va.level_index(3) as u64 * 8;
    eprintln!("l3pte = 0x{:x}", l3pte);
    let l3desc = memory.read_initial(l3pte, 8).and_then(desc_to_u64)?;
    let pa = (l3desc & bzhi_u64(!0xFFF, 48)) + va.page_offset();
    eprintln!("pa = 0x{:x}", pa);

    Ok(TranslationTableWalk { l0pte, l0desc, l1pte, l1desc, l2pte, l2desc, l3pte, l3desc, pa })
}

fn pte0<B: BV>(args: Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, solver)?;
    Ok(Val::Bits(B::from_u64(walk.l0pte)))
}

fn pte1<B: BV>(args: Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, solver)?;
    Ok(Val::Bits(B::from_u64(walk.l1pte)))
}

fn pte2<B: BV>(args: Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, solver)?;
    Ok(Val::Bits(B::from_u64(walk.l2pte)))
}

fn pte3<B: BV>(args: Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, solver)?;
    Ok(Val::Bits(B::from_u64(walk.l3pte)))
}

fn desc0<B: BV>(args: Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, solver)?;
    Ok(Val::Bits(B::from_u64(walk.l0desc)))
}

fn desc1<B: BV>(args: Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, solver)?;
    Ok(Val::Bits(B::from_u64(walk.l1desc)))
}

fn desc2<B: BV>(args: Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, solver)?;
    Ok(Val::Bits(B::from_u64(walk.l2desc)))
}

fn desc3<B: BV>(args: Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, solver)?;
    Ok(Val::Bits(B::from_u64(walk.l3desc)))
}

fn pa<B: BV>(args: Vec<Val<B>>, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let walk = translation_table_walk(args, memory, solver)?;
    Ok(Val::Bits(B::from_u64(walk.pa)))
}

fn page<B: BV>(mut args: Vec<Val<B>>, _: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    if args.len() != 1 {
        return Err(ExecError::Type("page must have 1 argument".to_string()))
    }
    
    let bits = args.pop().unwrap();
 
    primop::subrange_internal(bits, Val::I128(48), Val::I128(12), solver)
}

fn extz<B: BV>(mut args: Vec<Val<B>>, _: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type("extz must have 2 arguments".to_string()))
    }

    let len = args.pop().unwrap();
    let bits = args.pop().unwrap();

    primop::zero_extend(bits, len, solver)
}

fn exts<B: BV>(mut args: Vec<Val<B>>, _: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    if args.len() != 2 {
        return Err(ExecError::Type("exts must have 2 arguments".to_string()))
    }

    let len = args.pop().unwrap();
    let bits = args.pop().unwrap();

    primop::sign_extend(bits, len, solver)
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
    primops
}

pub fn eval<B: BV>(exp: &Exp, memory: &Memory<B>, solver: &mut Solver<B>) -> Result<Val<B>, ExecError> {
    let primops = litmus_primops();
    match exp {
        Exp::EqLoc(_, _) => Err(ExecError::Unimplemented),
        Exp::True => Ok(Val::Bool(true)),
        Exp::False => Ok(Val::Bool(false)),
        Exp::Bits64(bits, len) => Ok(Val::Bits(B::new(*bits, *len))),
        Exp::Nat(n) => Ok(Val::I128(*n as i128)),
        Exp::Bin(bin) => {
            let len = bin.len();
            if len <= 64 {
                Ok(Val::Bits(B::new(u64::from_str_radix(bin, 2).unwrap(), len as u32)))
            } else {
                Err(ExecError::Unimplemented)
            }
        }
        Exp::Hex(hex) => {
            let len = hex.len();
            if len <= 16 {
                Ok(Val::Bits(B::new(u64::from_str_radix(hex, 16).unwrap(), len as u32 * 4)))
            } else {
                Err(ExecError::Unimplemented)
            }
        }
        Exp::App(f, args) => {
            let args = args.iter().map(|arg| eval(arg, memory, solver)).collect::<Result<_, _>>()?;
            let f = primops.get(f).ok_or_else(|| ExecError::Type(format!("Unknown function {}", f)))?;
            f(args, memory, solver)
        }
        _ => Err(ExecError::Unimplemented),
    }
}

pub fn reset_eval<B: BV>(exp: &Exp) -> Reset<B> {
    let exp = exp.clone();
    Arc::new(move |memory, solver| eval(&exp, memory, solver))
}

/*
pub enum Ty {
    BitVec(u32),
    Bool,
}

pub enum TyError {
    TyError
}

fn infer(exp: &Exp) -> Result<Ty, TyError> {
    use Exp::*;
    match exp {
        EqLoc(loc, exp) => {
            let ty = infer_loc(loc)?;
            let _: () = check(exp, &ty)?;
            Ok(Ty::Bool)
        },
        True | False => Ok(Ty::Bool),
        _ => Ok(Ty::Bool),
    }
}

fn check(exp: &Exp, ty: &Ty) -> Result<(), TyError> {
    Ok(())
}

fn infer_loc(loc: &Loc) -> Result<Ty, TyError> {
    Ok(Ty::Bool)
}
*/
