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

//! This module defines and implements functions for working with the
//! *Jib* IR (intermediate representation) that is produced by
//! Sail. It is a simple goto/conditional branch language, where each
//! function can declare and use an arbitrary amount of variables.
//!
//! All the IR types are parametric in the identifier type. They are
//! initially parsed as e.g. `Def<String>` but then the names are
//! interned into a symbol table ([Symtab]) and they are replaced by
//! values of type [Name], which is a wrapper around `u32`.
//!
//! To conveniently initialize the IR for a Sail architecture
//! specification see the [crate::init] module.

use ahash;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::io::Write;
use std::sync::Arc;

use crate::bitvector::{b64::B64, BV};
use crate::error::ExecError;
use crate::memory::Memory;
use crate::primop::{self, Binary, Primops, Unary, Variadic};
use crate::smt::{smtlib, EnumMember, Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;

pub mod linearize;
pub mod partial_linearize;
pub mod serialize;
pub mod ssa;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct Name {
    id: u32,
}

impl Name {
    pub fn from_u32(id: u32) -> Self {
        Name { id }
    }

    pub fn to_smt<V>(self) -> smtlib::Exp<V> {
        smtlib::Exp::Bits64(B64::from_u32(self.id))
    }

    pub fn smt_ty() -> smtlib::Ty {
        smtlib::Ty::BitVec(32)
    }
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub struct FPTy {
    ebits: u32,
    sbits: u32,
}

impl FPTy {
    pub fn exponent_width(self) -> u32 {
        self.ebits
    }

    pub fn significand_width(self) -> u32 {
        self.sbits
    }

    pub fn fp16() -> Self {
        FPTy { ebits: 5, sbits: 11 }
    }

    pub fn fp32() -> Self {
        FPTy { ebits: 8, sbits: 24 }
    }

    pub fn fp64() -> Self {
        FPTy { ebits: 11, sbits: 53 }
    }

    pub fn fp128() -> Self {
        FPTy { ebits: 15, sbits: 113 }
    }

    pub fn to_smt(self) -> smtlib::Ty {
        smtlib::Ty::Float(self.ebits, self.sbits)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Ty<A> {
    I64,
    I128,
    AnyBits,
    Bits(u32),
    Unit,
    Bool,
    Bit,
    String,
    Real,
    Enum(A),
    Struct(A),
    Union(A),
    Vector(Box<Ty<A>>),
    FixedVector(u32, Box<Ty<A>>),
    List(Box<Ty<A>>),
    Ref(Box<Ty<A>>),
    Float(FPTy),
    RoundingMode,
}

/// A [Loc] is a location that can be assigned to.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Loc<A> {
    Id(A),
    Field(Box<Loc<A>>, A),
    Addr(Box<Loc<A>>),
}

impl<A: Clone> Loc<A> {
    pub fn id(&self) -> A {
        match self {
            Loc::Id(id) => id.clone(),
            Loc::Field(loc, _) | Loc::Addr(loc) => loc.id(),
        }
    }

    pub fn id_mut(&mut self) -> &mut A {
        match self {
            Loc::Id(id) => id,
            Loc::Field(loc, _) | Loc::Addr(loc) => loc.id_mut(),
        }
    }
}

impl fmt::Display for Loc<String> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Loc::Id(a) => write!(f, "{}", zencode::decode(a)),
            Loc::Field(loc, a) => write!(f, "{}.{}", loc, a),
            Loc::Addr(a) => write!(f, "{}*", a),
        }
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum Op {
    Not,
    Or,
    And,
    Eq,
    Neq,
    Lteq,
    Lt,
    Gteq,
    Gt,
    Add,
    Sub,
    Slice(u32),
    SetSlice,
    Signed(u32),
    Unsigned(u32),
    ZeroExtend(u32),
    Bvnot,
    Bvor,
    Bvxor,
    Bvand,
    Bvadd,
    Bvsub,
    Bvaccess,
    Concat,
    Head,
    Tail,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BitsSegment<B> {
    Symbolic(Sym),
    Concrete(B),
}

/// A value is either a symbolic value, represented as `Symbolic(n)`
/// for where n is the identifier of the variable in the SMT solver,
/// or one of the concrete values in this enum.
///
/// An additional `MixedBits` constructor provides bitvectors made out
/// of symbolic and concrete parts to make traces of instructions with
/// symbolic operands more pleasant.  At the time of writing they are
/// not introduced internally.
///
/// Note that the equality trait implements a literal equality, see
/// [crate::primop] for a semantic comparison.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val<B> {
    Symbolic(Sym),
    I64(i64),
    I128(i128),
    Bool(bool),
    Bits(B),
    MixedBits(Vec<BitsSegment<B>>),
    String(String),
    Unit,
    Vector(Vec<Val<B>>),
    List(Vec<Val<B>>),
    Enum(EnumMember),
    Struct(HashMap<Name, Val<B>, ahash::RandomState>),
    Ctor(Name, Box<Val<B>>),
    SymbolicCtor(Sym, HashMap<Name, Val<B>>),
    Ref(Name),
    Poison,
}

impl<B: BV> From<&BitsSegment<B>> for Val<B> {
    fn from(segment: &BitsSegment<B>) -> Self {
        match segment {
            BitsSegment::Symbolic(v) => Val::Symbolic(*v),
            BitsSegment::Concrete(bv) => Val::Bits(*bv),
        }
    }
}

impl<B: BV> Val<B> {
    fn collect_symbolic_variables(&self, vars: &mut HashSet<Sym>) {
        use Val::*;
        match self {
            Symbolic(v) => {
                vars.insert(*v);
            }
            MixedBits(bs) => {
                for b in bs.iter() {
                    match b {
                        BitsSegment::Symbolic(v) => {
                            vars.insert(*v);
                        }
                        BitsSegment::Concrete(_) => (),
                    }
                }
            }
            I64(_) | I128(_) | Bool(_) | Bits(_) | Enum(_) | String(_) | Unit | Ref(_) | Poison => (),
            Vector(vals) | List(vals) => vals.iter().for_each(|val| val.collect_symbolic_variables(vars)),
            Struct(vals) => vals.iter().for_each(|(_, val)| val.collect_symbolic_variables(vars)),
            Ctor(_, val) => val.collect_symbolic_variables(vars),
            SymbolicCtor(_, vals) => vals.iter().for_each(|(_, val)| val.collect_symbolic_variables(vars)),
        }
    }

    pub fn symbolic_variables(&self) -> HashSet<Sym> {
        let mut vars = HashSet::new();
        self.collect_symbolic_variables(&mut vars);
        vars
    }

    pub fn is_symbolic(&self) -> bool {
        !self.symbolic_variables().is_empty()
    }

    pub fn as_bits(&self) -> Option<&B> {
        match self {
            Val::Bits(bv) => Some(bv),
            _ => None,
        }
    }

    pub fn write(&self, buf: &mut dyn Write, symtab: &Symtab) -> std::io::Result<()> {
        use Val::*;
        match self {
            Symbolic(v) => write!(buf, "v{}", v),
            I64(n) => write!(buf, "(_ bv{} 64)", n),
            I128(n) => write!(buf, "(_ bv{} 128)", n),
            Bool(b) => write!(buf, "{}", b),
            Bits(bv) => write!(buf, "{}", bv),
            MixedBits(bs) => {
                write!(buf, "(")?;
                for (i, segment) in bs.iter().enumerate() {
                    match segment {
                        BitsSegment::Symbolic(v) => write!(buf, "v{}", v)?,
                        BitsSegment::Concrete(b) => write!(buf, "{}", b)?,
                    };
                    if i < bs.len() - 1 {
                        write!(buf, " @ ")?
                    }
                }
                write!(buf, ")")
            }
            String(s) => write!(buf, "\"{}\"", s),
            Enum(EnumMember { enum_id, member }) => write!(buf, "e{}_{}", enum_id.to_usize(), member),
            Unit => write!(buf, "(_ unit)"),
            List(vec) => {
                write!(buf, "(_ list ")?;
                if let Some((last, elems)) = vec.split_last() {
                    for elem in elems {
                        elem.write(buf, symtab)?;
                        write!(buf, " ")?
                    }
                    last.write(buf, symtab)?;
                } else {
                    write!(buf, "nil")?
                }
                write!(buf, ")")
            }
            Vector(vec) => {
                write!(buf, "(_ vec ")?;
                if let Some((last, elems)) = vec.split_last() {
                    for elem in elems {
                        elem.write(buf, symtab)?;
                        write!(buf, " ")?
                    }
                    last.write(buf, symtab)?;
                } else {
                    write!(buf, "nil")?
                }
                write!(buf, ")")
            }
            Struct(fields) => {
                write!(buf, "(_ struct ")?;
                if fields.is_empty() {
                    write!(buf, "nil")?
                } else {
                    for (i, (k, v)) in fields.iter().enumerate() {
                        write!(buf, "(|{}| ", zencode::decode(symtab.to_str(*k)))?;
                        v.write(buf, symtab)?;
                        write!(buf, ")")?;
                        if i < fields.len() - 1 {
                            write!(buf, " ")?
                        }
                    }
                }
                write!(buf, ")")
            }
            Ctor(ctor, v) => {
                write!(buf, "(|{}| ", zencode::decode(symtab.to_str_demangled(*ctor)))?;
                v.write(buf, symtab)?;
                write!(buf, ")")
            }
            SymbolicCtor(v, possibilities) => {
                write!(buf, "(_ ctor v{} ", v)?;
                if possibilities.is_empty() {
                    write!(buf, "nil")?
                } else {
                    for (i, (k, v)) in possibilities.iter().enumerate() {
                        write!(buf, "(|{}| ", zencode::decode(symtab.to_str_demangled(*k)))?;
                        v.write(buf, symtab)?;
                        write!(buf, ")")?;
                        if i < possibilities.len() - 1 {
                            write!(buf, " ")?
                        }
                    }
                }
                write!(buf, ")")
            }
            Ref(reg) => write!(buf, "(_ reg |{}|)", zencode::decode(symtab.to_str(*reg))),
            Poison => write!(buf, "(_ poison)"),
        }
    }

    pub fn to_string(&self, symtab: &Symtab) -> String {
        let mut buf = Vec::new();
        self.write(&mut buf, symtab).unwrap();
        String::from_utf8(buf).unwrap()
    }

    /// Just enough of a type check to pick up bad default registers
    pub fn plausible<N: std::fmt::Debug>(&self, ty: &Ty<N>, symtab: &Symtab) -> Result<(), String> {
        match (self, ty) {
            (Val::Symbolic(_), _) => Ok(()),
            (Val::I64(_), Ty::I64) => Ok(()),
            (Val::I128(_), Ty::I128) => Ok(()),
            (Val::Bool(_), Ty::Bool) => Ok(()),
            (Val::Bits(_), Ty::AnyBits) => Ok(()),
            (Val::Bits(bv), Ty::Bits(n)) => {
                if bv.len() == *n {
                    Ok(())
                } else {
                    Err(format!("value {} doesn't appear to match type {:?}", self.to_string(symtab), ty))
                }
            }
            (Val::String(_), Ty::String) => Ok(()),
            (Val::Unit, Ty::Unit) => Ok(()),
            (Val::Vector(_), Ty::Vector(_)) => Ok(()), // TODO: element type
            (Val::Vector(_), Ty::FixedVector(_, _)) => Ok(()), // TODO: element type
            (Val::List(_), Ty::List(_)) => Ok(()),     // TODO: element type
            (Val::Enum(_), Ty::Enum(_)) => Ok(()),     // TODO: element type
            (Val::Struct(_), Ty::Struct(_)) => Ok(()), // TODO: element type
            (Val::Ctor(_, _), _) => Ok(()),            // TODO
            (Val::Ref(_), _) => Ok(()),                // TODO
            (Val::Poison, _) => Ok(()),
            (_, _) => Err(format!("value {} doesn't appear to match type {:?}", self.to_string(symtab), ty)),
        }
    }
}

/// A [UVal] is a potentially uninitialized [Val].
#[derive(Clone, Debug)]
pub enum UVal<'ir, B> {
    Uninit(&'ir Ty<Name>),
    Init(Val<B>),
}

/// A [URVal] is a potentially uninitialized [Val] used by the register reset functionality
pub enum URVal<B> {
    Uninit(Ty<Name>),
    Init(Val<B>),
}

/// A map from identifers to potentially uninitialized values.
pub type Bindings<'ir, B> = HashMap<Name, UVal<'ir, B>, ahash::RandomState>;

/// A reference to either the declaration of a variable or a usage
/// location.
pub enum Variable<'a, A> {
    Declaration(&'a mut A),
    Usage(&'a mut A),
}

/// An iterator over the [Variable] type for modifying variable usages
/// and declarations.
pub struct Variables<'a, A> {
    vec: Vec<Variable<'a, A>>,
}

impl<'a, A> Variables<'a, A> {
    pub fn from_vec(vec: Vec<Variable<'a, A>>) -> Self {
        Variables { vec }
    }
}

impl<'a, A> Iterator for Variables<'a, A> {
    type Item = Variable<'a, A>;

    fn next(&mut self) -> Option<Self::Item> {
        self.vec.pop()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Exp<A> {
    Id(A),
    Ref(A),
    Bool(bool),
    Bits(B64),
    String(String),
    Unit,
    I64(i64),
    I128(i128),
    Undefined(Ty<A>),
    Struct(A, Vec<(A, Exp<A>)>),
    Kind(A, Box<Exp<A>>),
    Unwrap(A, Box<Exp<A>>),
    Field(Box<Exp<A>>, A),
    Call(Op, Vec<Exp<A>>),
}

impl<A: Hash + Eq + Clone> Exp<A> {
    fn collect_ids(&self, ids: &mut HashSet<A>) {
        use Exp::*;
        match self {
            Id(id) => {
                ids.insert(id.clone());
            }
            Ref(_) | Bool(_) | Bits(_) | String(_) | Unit | I64(_) | I128(_) | Undefined(_) => (),
            Kind(_, exp) | Unwrap(_, exp) | Field(exp, _) => exp.collect_ids(ids),
            Call(_, exps) => exps.iter().for_each(|exp| exp.collect_ids(ids)),
            Struct(_, fields) => fields.iter().for_each(|(_, exp)| exp.collect_ids(ids)),
        }
    }

    pub(crate) fn collect_variables<'a, 'b>(&'a mut self, vars: &'b mut Vec<Variable<'a, A>>) {
        use Exp::*;
        match self {
            Id(id) => vars.push(Variable::Usage(id)),
            Ref(_) | Bool(_) | Bits(_) | String(_) | Unit | I64(_) | I128(_) | Undefined(_) => (),
            Kind(_, exp) | Unwrap(_, exp) | Field(exp, _) => exp.collect_variables(vars),
            Call(_, exps) => exps.iter_mut().for_each(|exp| exp.collect_variables(vars)),
            Struct(_, fields) => fields.iter_mut().for_each(|(_, exp)| exp.collect_variables(vars)),
        }
    }

    pub fn variables(&mut self) -> Variables<'_, A> {
        let mut vec = Vec::new();
        self.collect_variables(&mut vec);
        Variables::from_vec(vec)
    }

    pub fn bool_not(self) -> Self {
        match self {
            Exp::Bool(b) => Exp::Bool(!b),
            exp => Exp::Call(Op::Not, vec![exp]),
        }
    }

    /// This function returns a number abstractly representing how
    /// 'big' or 'complex' a certain expression is. The larger the
    /// number, the larger or more complex the expression.
    pub fn size_heuristic(&self) -> usize {
        match self {
            Exp::Call(_, exps) => 1 + exps.iter().map(Exp::size_heuristic).sum::<usize>(),
            Exp::Struct(_, fields) => 1 + fields.iter().map(|(_, exp)| exp.size_heuristic()).sum::<usize>(),
            Exp::Kind(_, exp) | Exp::Unwrap(_, exp) | Exp::Field(exp, _) => 1 + exp.size_heuristic(),
            _ => 1,
        }
    }
}

pub fn short_circuit_and<A>(lhs: Exp<A>, rhs: Exp<A>) -> Exp<A> {
    match (lhs, rhs) {
        (Exp::Bool(false), _) => Exp::Bool(false),
        (_, Exp::Bool(false)) => Exp::Bool(false),
        (Exp::Bool(true), rhs) => rhs,
        (lhs, Exp::Bool(true)) => lhs,
        (lhs, rhs) => Exp::Call(Op::And, vec![lhs, rhs]),
    }
}

pub fn short_circuit_or<A>(lhs: Exp<A>, rhs: Exp<A>) -> Exp<A> {
    match (lhs, rhs) {
        (Exp::Bool(true), _) => Exp::Bool(true),
        (_, Exp::Bool(true)) => Exp::Bool(true),
        (Exp::Bool(false), rhs) => rhs,
        (lhs, Exp::Bool(false)) => lhs,
        (lhs, rhs) => Exp::Call(Op::Or, vec![lhs, rhs]),
    }
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum ExitCause {
    /// A pattern match failure
    MatchFailure,
    /// Used if we rewrite assertions into explicit control flow
    AssertionFailure,
    /// An explicit call to the Sail exit() function
    Explicit,
}

#[derive(Clone)]
pub enum Instr<A, B> {
    Decl(A, Ty<A>, SourceLoc),
    Init(A, Ty<A>, Exp<A>, SourceLoc),
    Jump(Exp<A>, usize, SourceLoc),
    Goto(usize),
    Copy(Loc<A>, Exp<A>, SourceLoc),
    Monomorphize(A, SourceLoc),
    Call(Loc<A>, bool, A, Vec<Exp<A>>, SourceLoc),
    PrimopUnary(Loc<A>, Unary<B>, Exp<A>, SourceLoc),
    PrimopBinary(Loc<A>, Binary<B>, Exp<A>, Exp<A>, SourceLoc),
    PrimopVariadic(Loc<A>, Variadic<B>, Vec<Exp<A>>, SourceLoc),
    Exit(ExitCause, SourceLoc),
    Arbitrary,
    End,
}

impl<A: fmt::Debug, B: fmt::Debug> fmt::Debug for Instr<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Instr::*;
        match self {
            Decl(id, ty, info) => write!(f, "{:?} : {:?} ` {:?}", id, ty, info),
            Init(id, ty, exp, info) => write!(f, "{:?} : {:?} = {:?} ` {:?}", id, ty, exp, info),
            Jump(exp, target, info) => write!(f, "jump {:?} to {:?} ` {:?}", exp, target, info),
            Goto(target) => write!(f, "goto {:?}", target),
            Copy(loc, exp, info) => write!(f, "{:?} = {:?} ` {:?}", loc, exp, info),
            Monomorphize(id, info) => write!(f, "mono {:?} ` {:?}", id, info),
            Call(loc, ext, id, args, info) => write!(f, "{:?} = {:?}<{:?}>({:?}) ` {:?}", loc, id, ext, args, info),
            Exit(cause, info) => write!(f, "exit {:?} ` {:?}", cause, info),
            Arbitrary => write!(f, "arbitrary"),
            End => write!(f, "end"),
            PrimopUnary(loc, fptr, exp, info) => write!(f, "{:?} = {:p}({:?}) ` {:?}", loc, fptr, exp, info),
            PrimopBinary(loc, fptr, lhs, rhs, info) => {
                write!(f, "{:?} = {:p}({:?}, {:?}) ` {:?}", loc, fptr, lhs, rhs, info)
            }
            PrimopVariadic(loc, fptr, args, info) => write!(f, "{:?} = {:p}({:?}) ` {:?}", loc, fptr, args, info),
        }
    }
}

/// Append instructions from rhs into the lhs vector, leaving rhs
/// empty (the same behavior as `Vec::append`).
pub fn append_instrs<A, B>(lhs: &mut Vec<Instr<A, B>>, rhs: &mut Vec<Instr<A, B>>) {
    for instr in rhs.iter_mut() {
        match instr {
            Instr::Goto(label) => *label += lhs.len(),
            Instr::Jump(_, label, _) => *label += lhs.len(),
            _ => (),
        }
    }
    lhs.append(rhs)
}

#[derive(Clone)]
pub enum Def<A, B> {
    Register(A, Ty<A>),
    Let(Vec<(A, Ty<A>)>, Vec<Instr<A, B>>),
    Enum(A, Vec<A>),
    Struct(A, Vec<(A, Ty<A>)>),
    Union(A, Vec<(A, Ty<A>)>),
    Val(A, Vec<Ty<A>>, Ty<A>),
    Extern(A, bool, String, Vec<Ty<A>>, Ty<A>),
    Fn(A, Vec<A>, Vec<Instr<A, B>>),
    Files(Vec<String>),
    Pragma(String, String),
}

/// A [Symtab] is a symbol table that maps each `u32` identifier used
/// in the IR to it's `&str` name and vice-versa.
#[derive(Clone)]
pub struct Symtab<'ir> {
    symbols: Vec<&'ir str>,
    table: HashMap<&'ir str, u32, ahash::RandomState>,
    next: u32,
    files: Vec<&'ir str>,
    /// The Sail IR may monomorphize a tuple (A, B) into a tuple with
    /// two monomorphic fields. If it does so, it will leave a
    /// tuplestruct pragma informing us of this.
    pub tuple_structs: HashMap<Name, Vec<Name>>,
    /// If names went through name mangling during monomorphisation,
    /// Sail inserts a #mangled pragma that tells us the original name
    /// of the symbol.
    pub mangled_names: HashMap<Name, &'ir str>,
}

/// When a function returns via the [Instr::End] instruction, the
/// value returned is contained in the special [RETURN] variable.
pub const RETURN: Name = Name { id: 0 };

/// Function id for the primop implementing the `assert` construct in
/// Sail.
pub const SAIL_ASSERT: Name = Name { id: 1 };

/// Function id for the `assume` primop, which is like a Sail assert
/// but always corresponds to an raw SMT assert.
pub const SAIL_ASSUME: Name = Name { id: 2 };

/// [CURRENT_EXCEPTION] is a global variable containing an exception
/// with the sail type `exception`. It is only defined when
/// [HAVE_EXCEPTION] is true.
pub const CURRENT_EXCEPTION: Name = Name { id: 3 };

/// [HAVE_EXCEPTION] is a global boolean variable which is true if an
/// exception is being thrown.
pub const HAVE_EXCEPTION: Name = Name { id: 4 };

/// [THROW_LOCATION] is a global variable which contains a string
/// describing the location of the last thrown exeception.
pub const THROW_LOCATION: Name = Name { id: 5 };

/// Special primitive that initializes a generic vector
pub const INTERNAL_VECTOR_INIT: Name = Name { id: 6 };

/// Special primitive used while initializing a generic vector
pub const INTERNAL_VECTOR_UPDATE: Name = Name { id: 7 };

/// Special primitive for `update_fbits`
pub const BITVECTOR_UPDATE: Name = Name { id: 8 };

/// [NULL] is a global letbinding which contains the empty list
pub const NULL: Name = Name { id: 9 };

/// The function id for the `elf_entry` function.
pub const ELF_ENTRY: Name = Name { id: 10 };

/// Is the function id of the `reg_deref` primop, that implements
/// register dereferencing `*R` in Sail.
pub const REG_DEREF: Name = Name { id: 11 };

/// [SAIL_EXCEPTION] is the Sail `exception` type
pub const SAIL_EXCEPTION: Name = Name { id: 12 };

/// [TOP_LEVEL_LET] is a name used in backtraces when evaluating a top-level let definition
pub const TOP_LEVEL_LET: Name = Name { id: 13 };

/// [BV_BIT_LEFT] is the field name for the left element of a bitvector,bit pair
pub const BV_BIT_LEFT: Name = Name { id: 14 };

/// [BV_BIT_RIGHT] is the field name for the right element of a bitvector,bit pair
pub const BV_BIT_RIGHT: Name = Name { id: 15 };

/// [RESET_REGISTERS] is a special function that resets register
/// values according to the ISA config
pub const RESET_REGISTERS: Name = Name { id: 16 };

/// When we linearize function definitions, the phi functions from the
/// SSA representation become explicit if-then-else functions in the
/// IR, and are representing using this builtin
pub const ITE_PHI: Name = Name { id: 17 };

/// When we make function calls abstract we replace them by calls to this primitive
pub const ABSTRACT_CALL: Name = Name { id: 18 };

/// Primitives we treat as abstract are replaced by calls to this primitive
pub const ABSTRACT_PRIMOP: Name = Name { id: 19 };

/// Primitive to read a register from a vector of register references
pub const READ_REGISTER_FROM_VECTOR: Name = Name { id: 20 };

/// Primitive to write a register from a vector of register references
pub const WRITE_REGISTER_FROM_VECTOR: Name = Name { id: 21 };

static GENSYM: &str = "zzUGENSYMzU";

impl<'ir> Symtab<'ir> {
    pub fn intern(&mut self, sym: &'ir str) -> Name {
        match self.table.get(sym) {
            None => {
                let n = self.next;
                self.symbols.push(sym);
                self.table.insert(sym, n);
                self.next += 1;
                Name::from_u32(n)
            }
            Some(n) => Name::from_u32(*n),
        }
    }

    pub fn gensym(&mut self) -> Name {
        let n = self.next;
        self.symbols.push(GENSYM);
        self.table.insert(GENSYM, n);
        self.next += 1;
        Name::from_u32(n)
    }

    // Used for the really verbose tracing options
    pub fn all_names(&self) -> HashSet<Name> {
        let mut set = HashSet::with_capacity(self.next as usize);
        for i in 0..self.next {
            set.insert(Name::from_u32(i));
        };
        set
    }

    pub fn to_raw_table(&self) -> (Vec<String>, Vec<String>) {
        (
            self.symbols.iter().map(|sym| sym.to_string()).collect(),
            self.files.iter().map(|file| file.to_string()).collect(),
        )
    }

    pub fn from_raw_table(raw: &'ir [String], files: &'ir [String]) -> Self {
        let s = ahash::RandomState::new();
        let mut symtab = Symtab {
            symbols: Vec::with_capacity(raw.len()),
            table: HashMap::with_capacity_and_hasher(raw.len(), s),
            next: 0,
            files: files.iter().map(|f| &**f).collect(),
            tuple_structs: HashMap::new(),
            mangled_names: HashMap::new(),
        };
        for sym in raw {
            symtab.intern(sym);
        }
        symtab
    }

    pub fn to_str(&self, n: Name) -> &'ir str {
        match self.symbols.get(n.id as usize) {
            Some(s) => s,
            None => "zUNKNOWN",
        }
    }

    pub fn to_str_demangled(&self, n: Name) -> &'ir str {
        if let Some(s) = self.mangled_names.get(&n) {
            s
        } else {
            self.to_str(n)
        }
    }

    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        let mut symtab = Symtab {
            symbols: Vec::new(),
            table: HashMap::default(),
            next: 0,
            files: Vec::new(),
            tuple_structs: HashMap::new(),
            mangled_names: HashMap::new(),
        };
        symtab.intern("return");
        symtab.intern("zsail_assert");
        symtab.intern("zsail_assume");
        symtab.intern("current_exception");
        symtab.intern("have_exception");
        symtab.intern("throw_location");
        symtab.intern("zinternal_vector_init");
        symtab.intern("zinternal_vector_update");
        symtab.intern("zupdate_fbits");
        symtab.intern("NULL");
        symtab.intern("elf_entry");
        symtab.intern("reg_deref");
        symtab.intern("zexception");
        symtab.intern("zzUletzU");
        symtab.intern("ztuplez3z5bv_z5bit0");
        symtab.intern("ztuplez3z5bv_z5bit1");
        symtab.intern("reset_registers");
        symtab.intern("zzUite_phizU");
        symtab.intern("zzUabstractzU");
        symtab.intern("zzUprimitivezU");
        symtab.intern("zread_register_from_vector");
        symtab.intern("zwrite_register_from_vector");
        symtab
    }

    pub fn lookup(&self, sym: &str) -> Name {
        Name::from_u32(*self.table.get(sym).unwrap_or_else(|| {
            eprintln!("Could not find symbol: {}", sym);
            &std::u32::MAX
        }))
    }

    pub fn get(&self, sym: &str) -> Option<Name> {
        self.table.get(sym).copied().map(Name::from_u32)
    }

    pub fn set_files(&mut self, files: Vec<&'ir str>) {
        self.files = files;
    }

    pub fn files<'a>(&'a self) -> &'a [&'ir str] {
        &self.files
    }

    pub fn get_loc(&self, loc: &Loc<String>) -> Option<Loc<Name>> {
        use Loc::*;
        Some(match loc {
            Id(v) => Id(self.get(v)?),
            Field(loc, field) => Field(Box::new(self.get_loc(loc)?), self.get(field)?),
            Addr(loc) => Addr(Box::new(self.get_loc(loc)?)),
        })
    }

    pub fn tuple_struct_field_number(&self, field1: Name) -> Option<usize> {
        for fields in self.tuple_structs.values() {
            for (n, field2) in fields.iter().enumerate() {
                if field1 == *field2 {
                    return Some(n);
                }
            }
        }
        None
    }
}

/// A function declaration is a tripe of name * type pairs of
/// parameters, the return type, and a list of instructions for the
/// function body.
type FnDecl<'ir, B> = (Vec<(Name, &'ir Ty<Name>)>, &'ir Ty<Name>, &'ir [Instr<Name, B>]);

/// An extern declaration is like a function declaration, but it
/// points at a primop name rather than a list of instructions.
type ExternDecl<'ir> = (&'ir [Ty<Name>], &'ir Ty<Name>, &'ir str);

/// The idea behind the `Reset` type is we dynamically create what is
/// essentially a Sail function consisting of:
///
/// ```text
/// reg1 = f();
/// reg2 = g();
/// ...
/// ```
///
/// where `f` and `g` are Rust closures of type `Reset`. This is used
/// to define custom architectural reset values of these registers, in
/// a possibly symbolic way or based on some memory value. As an
/// example, for ARMv8 system concurrency litmus tests we can set up
/// something like `X1 = pte(virtual_address)`, where `pte` is the
/// address of the third level page table entry for a virtual address.
pub type Reset<B> =
    Arc<dyn 'static + Send + Sync + Fn(&Memory<B>, Typedefs, &mut Solver<B>) -> Result<Val<B>, ExecError>>;

/// All symbolic evaluation happens over some (immutable) IR. The
/// [SharedState] provides each worker that is performing symbolic
/// evaluation with a convenient view into that IR.
pub struct SharedState<'ir, B> {
    /// A map from function identifers to function bodies and parameter lists
    pub functions: HashMap<Name, FnDecl<'ir, B>>,
    /// A map of external definitions
    pub externs: HashMap<Name, ExternDecl<'ir>>,
    /// The symbol table for the IR
    pub symtab: Symtab<'ir>,
    /// A map from struct identifers to a map from field identifiers
    /// to their types
    pub structs: HashMap<Name, BTreeMap<Name, Ty<Name>>>,
    /// A map from enum identifiers to sets of their member
    /// identifiers
    pub enums: HashMap<Name, HashSet<Name>>,
    /// `enum_members` maps each enum member for every enum to it's
    /// position (as a (pos, size) pair, i.e. 1 of 3) within its
    /// respective enum
    pub enum_members: HashMap<Name, (usize, usize)>,
    /// `unions` is a map from union names to constructor (name, type) pairs
    pub unions: HashMap<Name, Vec<(Name, Ty<Name>)>>,
    /// `union_ctors` is a set of all union constructor identifiers
    pub union_ctors: HashSet<Name>,
    /// `registers` is a set of all registers and their types
    pub registers: HashMap<Name, Ty<Name>>,
    /// `probes` is a set of function/location identifers to print debug information for when called
    pub probes: HashSet<Name>,
    /// `trace_functions` defines a set of functions which we include
    /// in the traces as function call and return events
    pub trace_functions: HashSet<Name>,
    /// `reset_registers` are reset values for each register
    /// derived from the ISA config
    pub reset_registers: Vec<(Loc<Name>, Reset<B>)>,
    /// `reset_constraints` are added as assertions at the reset_registers builtin
    /// derived from the ISA config
    pub reset_constraints: Vec<smtlib::Exp<Loc<String>>>,
    /// `function_assumptions` are used to assume that a function applied to the
    /// given arguments has the given result, skipping execution
    /// derived from the ISA config
    pub function_assumptions: Vec<(String, Vec<Option<smtlib::Exp<Loc<String>>>>, smtlib::Exp<Loc<String>>)>,
}

#[derive(Copy, Clone)]
pub struct Typedefs<'a> {
    pub structs: &'a HashMap<Name, BTreeMap<Name, Ty<Name>>>,
    pub enums: &'a HashMap<Name, HashSet<Name>>,
    pub unions: &'a HashMap<Name, Vec<(Name, Ty<Name>)>>,
}

impl<'ir, B: BV> SharedState<'ir, B> {
    pub fn new(
        symtab: Symtab<'ir>,
        defs: &'ir [Def<Name, B>],
        probes: HashSet<Name>,
        trace_functions: HashSet<Name>,
        reset_registers: Vec<(Loc<Name>, Reset<B>)>,
        reset_constraints: Vec<smtlib::Exp<Loc<String>>>,
        function_assumptions: Vec<(String, Vec<Option<smtlib::Exp<Loc<String>>>>, smtlib::Exp<Loc<String>>)>,
    ) -> Self {
        let mut vals = HashMap::new();
        let mut functions: HashMap<Name, FnDecl<'ir, B>> = HashMap::new();
        let mut externs: HashMap<Name, ExternDecl<'ir>> = HashMap::new();
        let mut structs: HashMap<Name, BTreeMap<Name, Ty<Name>>> = HashMap::new();
        let mut enums: HashMap<Name, HashSet<Name>> = HashMap::new();
        let mut enum_members: HashMap<Name, (usize, usize)> = HashMap::new();
        let mut unions: HashMap<Name, Vec<(Name, Ty<Name>)>> = HashMap::new();
        let mut union_ctors: HashSet<Name> = HashSet::new();
        let mut registers: HashMap<Name, Ty<Name>> = HashMap::new();

        for def in defs {
            match def {
                Def::Val(f, arg_tys, ret_ty) => {
                    vals.insert(f, (arg_tys, ret_ty));
                }

                Def::Fn(f, args, body) => match vals.get(f) {
                    None => panic!("Found fn without a val when creating the global state!"),
                    Some((arg_tys, ret_ty)) => {
                        assert!(arg_tys.len() == args.len());
                        let args = args.iter().zip(arg_tys.iter()).map(|(id, ty)| (*id, ty)).collect();
                        functions.insert(*f, (args, ret_ty, body));
                    }
                },

                Def::Extern(f, _, primop, arg_tys, ret_ty) => {
                    externs.insert(*f, (arg_tys, ret_ty, primop));
                }

                Def::Struct(name, fields) => {
                    let fields: BTreeMap<_, _> = fields.clone().into_iter().collect();
                    structs.insert(*name, fields);
                }

                Def::Enum(name, members) => {
                    for (i, member) in members.iter().enumerate() {
                        enum_members.insert(*member, (i, members.len()));
                    }
                    let members: HashSet<_> = members.clone().into_iter().collect();
                    enums.insert(*name, members);
                }

                Def::Union(name, ctors) => {
                    for (ctor, _) in ctors {
                        union_ctors.insert(*ctor);
                    }
                    unions.insert(*name, ctors.to_vec());
                }

                Def::Register(name, ty) => {
                    registers.insert(*name, ty.clone());
                }

                _ => (),
            }
        }

        SharedState {
            functions,
            externs,
            symtab,
            structs,
            enums,
            enum_members,
            unions,
            union_ctors,
            registers,
            probes,
            trace_functions,
            reset_registers,
            reset_constraints,
            function_assumptions,
        }
    }

    pub fn typedefs(&self) -> Typedefs {
        Typedefs { structs: &self.structs, enums: &self.enums, unions: &self.unions }
    }

    pub fn enum_member_from_str(&self, member: &str) -> Option<usize> {
        let member = self.symtab.get(&zencode::encode(member))?;
        self.enum_members.get(&member).map(|(pos, _)| *pos)
    }

    pub fn enum_member(&self, member: Name) -> Option<usize> {
        self.enum_members.get(&member).map(|(pos, _)| *pos)
    }
}

fn insert_instr_primops<B: BV>(
    instr: Instr<Name, B>,
    externs: &HashMap<Name, (String, bool)>,
    primops: &Primops<B>,
) -> Instr<Name, B> {
    match &instr {
        Instr::Call(loc, _, f, args, info) => match externs.get(f) {
            Some((name, is_abstract)) => {
                if *is_abstract {
                    let mut args = args.clone();
                    args.push(Exp::Ref(*f));
                    Instr::Call(loc.clone(), false, ABSTRACT_PRIMOP, args, *info)
                } else if let Some(unop) = primops.unary.get(name) {
                    assert!(args.len() == 1);
                    Instr::PrimopUnary(loc.clone(), *unop, args[0].clone(), *info)
                } else if let Some(binop) = primops.binary.get(name) {
                    assert!(args.len() == 2);
                    Instr::PrimopBinary(loc.clone(), *binop, args[0].clone(), args[1].clone(), *info)
                } else if let Some(varop) = primops.variadic.get(name) {
                    Instr::PrimopVariadic(loc.clone(), *varop, args.clone(), *info)
                } else if name == "reg_deref" {
                    Instr::Call(loc.clone(), false, REG_DEREF, args.clone(), *info)
                } else if name == "reset_registers" {
                    Instr::Call(loc.clone(), false, RESET_REGISTERS, args.clone(), *info)
                } else if name == "read_register_from_vector" {
                    Instr::Call(loc.clone(), false, READ_REGISTER_FROM_VECTOR, args.clone(), *info)
                } else if name == "write_register_from_vector" {
                    Instr::Call(loc.clone(), false, WRITE_REGISTER_FROM_VECTOR, args.clone(), *info)
                } else {
                    // Currently we just warn when we don't have a
                    // primop. As long as we never actually try to
                    // call it things will be fine. This happens for
                    // softfloat based floating point in RISC-V right
                    // now.
                    eprintln!("No primop {} ({:?})", name, f);
                    Instr::Call(loc.clone(), false, *f, args.clone(), *info)
                }
            }
            None => instr,
        },
        _ => instr,
    }
}

/// There are two ways to handle assertions in the Sail code, the
/// first being to assume that they succeed (essentially treating them
/// like assumptions in the SMT) - this is the optimistic mode. The
/// other way is to assume that they might fail, and check each
/// assertion to ensure that it can never fail - this is the
/// pessimistic mode.
pub enum AssertionMode {
    Pessimistic,
    Optimistic,
}

/// Change Calls without implementations into Primops
pub(crate) fn insert_primops<B: BV>(defs: &mut [Def<Name, B>], mode: AssertionMode) {
    let mut externs: HashMap<Name, (String, bool)> = HashMap::new();
    for def in defs.iter() {
        if let Def::Extern(f, is_abstract, ext, _, _) = def {
            externs.insert(*f, (ext.to_string(), *is_abstract));
        }
    }

    match mode {
        AssertionMode::Optimistic => {
            externs.insert(SAIL_ASSERT, ("optimistic_assert".to_string(), false));
        }
        AssertionMode::Pessimistic => {
            externs.insert(SAIL_ASSERT, ("pessimistic_assert".to_string(), false));
        }
    };
    externs.insert(SAIL_ASSUME, ("assume".to_string(), false));
    externs.insert(BITVECTOR_UPDATE, ("bitvector_update".to_string(), false));

    let primops = Primops::default();

    for def in defs.iter_mut() {
        match def {
            Def::Fn(f, args, body) => {
                *def = Def::Fn(
                    *f,
                    args.to_vec(),
                    body.iter().cloned().map(|instr| insert_instr_primops(instr, &externs, &primops)).collect(),
                )
            }
            Def::Let(bindings, setup) => {
                *def = Def::Let(
                    bindings.clone(),
                    setup.iter().cloned().map(|instr| insert_instr_primops(instr, &externs, &primops)).collect(),
                )
            }
            _ => (),
        }
    }
}

pub fn assertions_to_jumps<B: BV>(defs: &mut [Def<Name, B>]) {
    for def in defs.iter_mut() {
        if let Def::Fn(_, _, body) = def {
            instrs_assertions_to_jumps(body)
        }
    }
}

fn instrs_assertions_to_jumps<B: BV>(instrs: &mut Vec<Instr<Name, B>>) {
    let mut len = instrs.len();
    let mut handlers = Vec::new();

    for (label, instr) in instrs.iter_mut().enumerate() {
        match instr {
            Instr::Call(loc, _, f, args, info) if *f == SAIL_ASSERT => {
                handlers.push(Instr::Jump(args[0].clone(), len + 2, *info));
                handlers.push(Instr::Exit(ExitCause::AssertionFailure, *info));
                handlers.push(Instr::Copy(loc.clone(), Exp::Unit, *info));
                handlers.push(Instr::Goto(label + 1));

                // Replace the call by a jump to a handler routine
                // placed at the end of the function body
                *instr = Instr::Goto(len);

                len += 4
            }
            _ => (),
        }
    }

    instrs.append(&mut handlers)
}

/// By default each jump or goto just contains a `usize` offset into
/// the instruction vector. This representation is efficient but hard
/// to work with, so we support mapping this representation into one
/// where any instruction can have an explicit label, and jumps point
/// to those explicit labels, and then going back to the offset based
/// representation for execution.
#[derive(Debug)]
pub enum LabeledInstr<B> {
    Labeled(usize, Instr<Name, B>),
    Unlabeled(Instr<Name, B>),
}

pub(crate) fn apply_label<B: BV>(label: &mut Option<usize>, instr: Instr<Name, B>) -> LabeledInstr<B> {
    if let Some(label) = label.take() {
        LabeledInstr::Labeled(label, instr)
    } else {
        LabeledInstr::Unlabeled(instr)
    }
}

impl<B: BV> LabeledInstr<B> {
    fn strip(self) -> Instr<Name, B> {
        use LabeledInstr::*;
        match self {
            Labeled(_, instr) => instr,
            Unlabeled(instr) => instr,
        }
    }

    fn strip_ref(&self) -> &Instr<Name, B> {
        use LabeledInstr::*;
        match self {
            Labeled(_, instr) => instr,
            Unlabeled(instr) => instr,
        }
    }

    fn label(&self) -> Option<usize> {
        match self {
            LabeledInstr::Labeled(l, _) => Some(*l),
            LabeledInstr::Unlabeled(_) => None,
        }
    }

    fn is_labeled(&self) -> bool {
        matches!(self, LabeledInstr::Labeled(_, _))
    }

    fn is_unlabeled(&self) -> bool {
        !self.is_labeled()
    }
}

/// Rewrites an instruction sequence with implicit offset based labels
/// into a vector where the labels are explicit. Note that this just
/// adds a label to every instruction which is equal to its
/// offset. Use [prune_labels] to remove any labels which are not the
/// target of any jump or goto instruction.
pub fn label_instrs<B: BV>(mut instrs: Vec<Instr<Name, B>>) -> Vec<LabeledInstr<B>> {
    use LabeledInstr::*;
    instrs.drain(..).enumerate().map(|(i, instr)| Labeled(i, instr)).collect()
}

/// Remove labels which are not the targets of any jump or goto.
pub fn prune_labels<B: BV>(mut instrs: Vec<LabeledInstr<B>>) -> Vec<LabeledInstr<B>> {
    use LabeledInstr::*;
    let mut targets = HashSet::new();

    for instr in &instrs {
        match instr.strip_ref() {
            Instr::Goto(target) | Instr::Jump(_, target, _) => {
                targets.insert(*target);
            }
            _ => (),
        }
    }

    instrs
        .drain(..)
        .map(|instr| match instr {
            Labeled(l, instr) if targets.contains(&l) => Labeled(l, instr),
            instr => Unlabeled(instr.strip()),
        })
        .collect()
}

/// Remove the explicit labels from instructions, and go back to using
/// offset based jumps and gotos.
pub fn unlabel_instrs<B: BV>(mut instrs: Vec<LabeledInstr<B>>) -> Vec<Instr<Name, B>> {
    use LabeledInstr::*;

    let mut jump_table: HashMap<usize, usize> = HashMap::new();

    for (i, instr) in instrs.iter().enumerate() {
        match instr {
            Labeled(label, _) => {
                jump_table.insert(*label, i);
            }
            Unlabeled(_) => (),
        }
    }

    instrs
        .drain(..)
        .map(|instr| match instr.strip() {
            Instr::Jump(cond, target, loc) => {
                let new_target = jump_table.get(&target).unwrap();
                Instr::Jump(cond, *new_target, loc)
            }

            Instr::Goto(target) => {
                let new_target = jump_table.get(&target).unwrap();
                Instr::Goto(*new_target)
            }

            instr => instr,
        })
        .collect()
}

fn insert_monomorphize_instrs<B: BV>(instrs: Vec<Instr<Name, B>>, mono_fns: &HashSet<Name>) -> Vec<Instr<Name, B>> {
    use LabeledInstr::*;
    let mut new_instrs = Vec::new();

    for instr in label_instrs(instrs) {
        match instr {
            Labeled(label, Instr::Call(loc, ext, f, args, info)) if mono_fns.contains(&f) => {
                let mut ids = HashSet::new();
                args.iter().for_each(|exp| exp.collect_ids(&mut ids));

                if ids.is_empty() {
                    new_instrs.push(Labeled(label, Instr::Call(loc, ext, f, args, info)))
                } else {
                    for (i, id) in ids.iter().enumerate() {
                        if i == 0 {
                            new_instrs.push(Labeled(label, Instr::Monomorphize(*id, info)))
                        } else {
                            new_instrs.push(Unlabeled(Instr::Monomorphize(*id, info)))
                        }
                    }
                    new_instrs.push(Unlabeled(Instr::Call(loc, ext, f, args, info)))
                }
            }

            _ => new_instrs.push(instr),
        }
    }

    unlabel_instrs(new_instrs)
}

fn has_mono_fn<B: BV>(instrs: &[Instr<Name, B>], mono_fns: &HashSet<Name>) -> bool {
    for instr in instrs {
        match instr {
            Instr::Call(_, _, f, _, _) if mono_fns.contains(f) => return true,
            _ => (),
        }
    }
    false
}

pub(crate) fn insert_monomorphize<B: BV>(defs: &mut [Def<Name, B>]) {
    let mut mono_fns = HashSet::new();
    for def in defs.iter() {
        match def {
            Def::Extern(f, _, ext, _, _) if ext == "monomorphize" => {
                mono_fns.insert(*f);
            }
            _ => (),
        }
    }

    for def in defs.iter_mut() {
        match def {
            Def::Fn(f, args, body) if has_mono_fn(body, &mono_fns) => {
                *def = Def::Fn(*f, args.to_vec(), insert_monomorphize_instrs(body.to_vec(), &mono_fns))
            }
            _ => (),
        }
    }
}

/// This function replaces a function with an _abstract_ function in
/// the trace. This means that rather than calling the function in
/// question, we simply add an event in the trace saying we called the
/// function, recording it's inputs and output, which is an arbitrary
/// value of the correct type.
pub fn abstract_function<B: BV>(defs: &mut [Def<Name, B>], target_function: Name) {
    for def in defs.iter_mut() {
        if let Def::Let(_, instrs) | Def::Fn(_, _, instrs) = def {
            for instr in instrs.iter_mut() {
                match instr {
                    Instr::Call(_, _, f, args, _) if *f == target_function => {
                        args.push(Exp::Ref(*f));
                        *f = ABSTRACT_CALL
                    }
                    _ => (),
                }
            }
        }
    }
}

fn has_call<B: BV>(instrs: &[Instr<Name, B>], target_function: Name) -> bool {
    for instr in instrs {
        match instr {
            Instr::Call(_, _, f, _, _) if *f == target_function => return true,
            _ => (),
        }
    }
    false
}

pub fn function_return_type<B: BV>(defs: &[Def<Name, B>], target_function: Name) -> Option<&Ty<Name>> {
    for def in defs {
        match def {
            Def::Val(f, _, ret_ty) if *f == target_function => return Some(ret_ty),
            _ => (),
        }
    }
    None
}

/// Replace a function call with an abstract function call in the
/// trace (see `abstract_function` for details). The return value of
/// this function is assumed to satisfy a given property, i.e.
///
/// ```text
/// y = f(x)
/// ```
///
/// will be replaced by
///
/// ```text
/// y = abstract(x)
/// assume(P(x, y))
/// ```
///
/// For this transformation to be sound, P should be an actual
/// property satisfied by the function being abstracted.
pub fn abstract_function_with_property<B: BV>(
    defs: &mut [Def<Name, B>],
    symtab: &mut Symtab,
    target_function: Name,
    property: Name,
) -> Option<()> {
    use Instr::*;
    use LabeledInstr::*;

    let ret_ty = function_return_type(defs, target_function)?.clone();

    for def in defs.iter_mut() {
        if let Def::Let(_, instrs) | Def::Fn(_, _, instrs) = def {
            if !has_call(instrs, target_function) {
                continue;
            }

            let mut new_instrs = Vec::new();

            for instr in label_instrs(std::mem::take(instrs)) {
                match instr {
                    Labeled(label, Instr::Call(loc, ext, f, mut args, info)) if f == target_function => {
                        let ret_val = symtab.gensym();
                        let prop = symtab.gensym();
                        let unit_val = symtab.gensym();
                        let mut prop_args = args.clone();

                        new_instrs.push(Labeled(label, Decl(ret_val, ret_ty.clone(), info)));
                        new_instrs.push(Unlabeled(Decl(prop, Ty::Bool, info)));
                        new_instrs.push(Unlabeled(Decl(unit_val, Ty::Unit, info)));

                        // Abstract the function call
                        args.push(Exp::Ref(f));
                        new_instrs.push(Unlabeled(Call(Loc::Id(ret_val), ext, ABSTRACT_CALL, args, info)));

                        // Call the property function
                        prop_args.push(Exp::Id(ret_val));
                        new_instrs.push(Unlabeled(Call(Loc::Id(prop), ext, property, prop_args, info)));

                        // Assume the property is true
                        new_instrs.push(Unlabeled(PrimopUnary(Loc::Id(unit_val), primop::assume, Exp::Id(prop), info)));

                        new_instrs.push(Unlabeled(Copy(loc, Exp::Id(ret_val), info)));
                    }

                    _ => new_instrs.push(instr),
                }
            }

            *instrs = unlabel_instrs(new_instrs)
        }
    }

    Some(())
}
