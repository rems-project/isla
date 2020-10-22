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

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::sync::Arc;

use crate::concrete::{bitvector64::B64, BV};
use crate::primop::{Binary, Primops, Unary, Variadic};
use crate::smt::Sym;
use crate::zencode;

pub mod linearize;
pub mod serialize;
pub mod ssa;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Name {
    id: u32,
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
}

/// A [Loc] is a location that can be assigned to.
#[derive(Clone, Debug, Serialize, Deserialize)]
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EnumMember {
    pub enum_id: usize,
    pub member: usize,
}

/// A value is either a symbolic value, represented as `Symbolic(n)`
/// for where n is the identifier of the variable in the SMT solver,
/// or one of the concrete values in this enum.
#[derive(Clone, Debug)]
pub enum Val<B> {
    Symbolic(Sym),
    I64(i64),
    I128(i128),
    Bool(bool),
    Bits(B),
    String(String),
    Unit,
    Vector(Vec<Val<B>>),
    List(Vec<Val<B>>),
    Enum(EnumMember),
    Struct(HashMap<Name, Val<B>>),
    Ctor(Name, Box<Val<B>>),
    Ref(Name),
    Poison,
}

impl<B: BV> Val<B> {
    fn collect_symbolic_variables(&self, vars: &mut HashSet<Sym>) {
        use Val::*;
        match self {
            Symbolic(v) => {
                vars.insert(*v);
            }
            I64(_) | I128(_) | Bool(_) | Bits(_) | Enum(_) | String(_) | Unit | Ref(_) | Poison => (),
            Vector(vals) | List(vals) => vals.iter().for_each(|val| val.collect_symbolic_variables(vars)),
            Struct(vals) => vals.iter().for_each(|(_, val)| val.collect_symbolic_variables(vars)),
            Ctor(_, val) => val.collect_symbolic_variables(vars),
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

    pub fn to_string(&self, symtab: &Symtab) -> String {
        use Val::*;
        match self {
            Symbolic(v) => format!("v{}", v),
            I64(n) => format!("(_ bv{} 64)", n),
            I128(n) => format!("(_ bv{} 128)", n),
            Bool(b) => format!("{}", b),
            Bits(bv) => format!("{}", bv),
            String(s) => format!("\"{}\"", s),
            Enum(EnumMember { enum_id, member }) => format!("e{}_{}", enum_id, member),
            Unit => "(_ unit)".to_string(),
            List(vec) => {
                let vec =
                    vec.iter()
                        .map(|elem| elem.to_string(symtab))
                        .fold(None, |acc, elem| {
                            if let Some(prefix) = acc {
                                Some(format!("{} {}", prefix, elem))
                            } else {
                                Some(elem)
                            }
                        })
                        .unwrap_or_else(|| "nil".to_string());
                format!("(_ list {})", vec)
            }
            Vector(vec) => {
                let vec =
                    vec.iter()
                        .map(|elem| elem.to_string(symtab))
                        .fold(None, |acc, elem| {
                            if let Some(prefix) = acc {
                                Some(format!("{} {}", prefix, elem))
                            } else {
                                Some(elem)
                            }
                        })
                        .unwrap_or_else(|| "nil".to_string());
                format!("(_ vec {})", vec)
            }
            Struct(fields) => {
                let fields = fields
                    .iter()
                    .map(|(k, v)| format!("(|{}| {})", zencode::decode(&symtab.to_str(*k)), v.to_string(symtab)))
                    .fold(
                        None,
                        |acc, kv| {
                            if let Some(prefix) = acc {
                                Some(format!("{} {}", prefix, kv))
                            } else {
                                Some(kv)
                            }
                        },
                    )
                    .unwrap();
                format!("(_ struct {})", fields)
            }
            Ctor(ctor, v) => format!("(|{}| {})", zencode::decode(&symtab.to_str(*ctor)), v.to_string(symtab)),
            Ref(reg) => format!("(_ reg |{}|)", zencode::decode(&symtab.to_str(*reg))),
            Poison => "(_ poison)".to_string(),
        }
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
pub enum UVal<B> {
    Uninit(Arc<Ty<Name>>),
    Init(Val<B>),
}

/// A map from identifers to potentially uninitialized values.
pub type Bindings<B> = HashMap<Name, UVal<B>>;

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
}

#[derive(Clone)]
pub enum Instr<A, B> {
    Decl(A, Arc<Ty<A>>),
    Init(A, Arc<Ty<A>>, Exp<A>),
    Jump(Exp<A>, usize, String),
    Goto(usize),
    Copy(Loc<A>, Exp<A>),
    Monomorphize(A),
    Call(Loc<A>, bool, A, Vec<Exp<A>>),
    PrimopUnary(Loc<A>, Unary<B>, Exp<A>),
    PrimopBinary(Loc<A>, Binary<B>, Exp<A>, Exp<A>),
    PrimopVariadic(Loc<A>, Variadic<B>, Vec<Exp<A>>),
    Failure,
    Arbitrary,
    End,
}

impl<A: fmt::Debug, B: fmt::Debug> fmt::Debug for Instr<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Instr::*;
        match self {
            Decl(id, ty) => write!(f, "{:?} : {:?}", id, ty),
            Init(id, ty, exp) => write!(f, "{:?} : {:?} = {:?}", id, ty, exp),
            Jump(exp, target, info) => write!(f, "jump {:?} to {:?} ` {:?}", exp, target, info),
            Goto(target) => write!(f, "goto {:?}", target),
            Copy(loc, exp) => write!(f, "{:?} = {:?}", loc, exp),
            Monomorphize(id) => write!(f, "mono {:?}", id),
            Call(loc, ext, id, args) => write!(f, "{:?} = {:?}<{:?}>({:?})", loc, id, ext, args),
            Failure => write!(f, "failure"),
            Arbitrary => write!(f, "arbitrary"),
            End => write!(f, "end"),
            PrimopUnary(loc, fptr, exp) => write!(f, "{:?} = {:p}({:?})", loc, fptr, exp),
            PrimopBinary(loc, fptr, lhs, rhs) => write!(f, "{:?} = {:p}({:?}, {:?})", loc, fptr, lhs, rhs),
            PrimopVariadic(loc, fptr, args) => write!(f, "{:?} = {:p}({:?})", loc, fptr, args),
        }
    }
}

/// Append instructions from rhs into the lhs vector, leaving rhs
/// empty (the same behavior as Vec::append).
pub fn append_instrs<A, B>(lhs: &mut Vec<Instr<A, B>>, rhs: &mut Vec<Instr<A, B>>) {
    for instr in rhs.iter_mut() {
        match instr {
            Instr::Goto(label) => *label = *label + lhs.len(),
            Instr::Jump(_, label, _) => *label = *label + lhs.len(),
            _ => (),
        }
    }
    lhs.append(rhs)
}

#[derive(Clone)]
pub enum Def<A, B> {
    Register(A, Ty<A>),
    Let(Vec<(A, Ty<A>)>, Arc<Vec<Instr<A, B>>>),
    Enum(A, Vec<A>),
    Struct(A, Vec<(A, Ty<A>)>),
    Union(A, Vec<(A, Ty<A>)>),
    Val(A, Vec<Ty<A>>, Ty<A>),
    Extern(A, String, Vec<Ty<A>>, Ty<A>),
    Fn(A, Vec<A>, Arc<Vec<Instr<A, B>>>),
}

impl Name {
    fn from_u32(id: u32) -> Self {
        Name { id }
    }
}

/// A [Symtab] is a symbol table that maps each `u32` identifier used
/// in the IR to it's `&str` name and vice-versa.
#[derive(Clone)]
pub struct Symtab {
    symbols: Vec<Arc<str>>,
    table: HashMap<Arc<str>, u32>,
    next: u32,
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

/// Function id for the primop implementing the `exit` construct in
/// Sail.
pub const SAIL_EXIT: Name = Name { id: 3 };

/// [CURRENT_EXCEPTION] is a global variable containing an exception
/// with the sail type `exception`. It is only defined when
/// [HAVE_EXCEPTION] is true.
pub const CURRENT_EXCEPTION: Name = Name { id: 4 };

/// [HAVE_EXCEPTION] is a global boolean variable which is true if an
/// exception is being thrown.
pub const HAVE_EXCEPTION: Name = Name { id: 5 };

/// [THROW_LOCATION] is a global variable which contains a string
/// describing the location of the last thrown exeception.
pub const THROW_LOCATION: Name = Name { id: 6 };

/// Special primitive that initializes a generic vector
pub const INTERNAL_VECTOR_INIT: Name = Name { id: 7 };

/// Special primitive used while initializing a generic vector
pub const INTERNAL_VECTOR_UPDATE: Name = Name { id: 8 };

/// Special primitive for `update_fbits`
pub const BITVECTOR_UPDATE: Name = Name { id: 9 };

/// [NULL] is a global letbinding which contains the empty list
pub const NULL: Name = Name { id: 10 };

/// The function id for the `elf_entry` function.
pub const ELF_ENTRY: Name = Name { id: 11 };

/// Is the function id of the `reg_deref` primop, that implements
/// register dereferencing `*R` in Sail.
pub const REG_DEREF: Name = Name { id: 12 };

/// [SAIL_EXCEPTION] is the Sail `exception` type
pub const SAIL_EXCEPTION: Name = Name { id: 13 };

/// [TOP_LEVEL_LET] is a name used in backtraces when evaluating a top-level let definition
pub const TOP_LEVEL_LET: Name = Name { id: 14 };

/// [BV_BIT_LEFT] is the field name for the left element of a bitvector,bit pair
pub const BV_BIT_LEFT: Name = Name { id: 15 };

/// [BV_BIT_RIGHT] is the field name for the right element of a bitvector,bit pair
pub const BV_BIT_RIGHT: Name = Name { id: 16 };

static GENSYM: &str = "|GENSYM|";

impl Symtab {
    pub fn intern(&mut self, sym: Arc<str>) -> Name {
        match self.table.get(&sym) {
            None => {
                let n = self.next;
                self.symbols.push(sym.clone());
                self.table.insert(sym, n);
                self.next += 1;
                Name::from_u32(n)
            }
            Some(n) => Name::from_u32(*n),
        }
    }

    pub fn gensym(&mut self) -> Name {
        let n = self.next;
        self.symbols.push(Arc::from(GENSYM)); //TODO verify
        self.table.insert(Arc::from(GENSYM), n); //TODO verify
        self.next += 1;
        Name::from_u32(n)
    }

    pub fn to_raw_table(&self) -> Vec<String> {
        self.symbols.iter().map(|sym| (*sym).to_string()).collect()
    }

    pub fn from_raw_table(raw: &[String]) -> Self {
        let mut symtab =
            Symtab { symbols: Vec::with_capacity(raw.len()), table: HashMap::with_capacity(raw.len()), next: 0 };
        for sym in raw {
            symtab.intern(Arc::from(sym.clone()));
        }
        symtab
    }

    pub fn to_str(&self, n: Name) -> Arc<str> {
        match self.symbols.get(n.id as usize) {
            Some(s) => s.clone(),
            None => Arc::from("zUNKNOWN"),
        }
    }

    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        let mut symtab = Symtab { symbols: Vec::new(), table: HashMap::new(), next: 0 };
        symtab.intern(Arc::from("return"));
        symtab.intern(Arc::from("zsail_assert"));
        symtab.intern(Arc::from("zsail_assume"));
        symtab.intern(Arc::from("zsail_exit"));
        symtab.intern(Arc::from("current_exception"));
        symtab.intern(Arc::from("have_exception"));
        symtab.intern(Arc::from("throw_location"));
        symtab.intern(Arc::from("zinternal_vector_init"));
        symtab.intern(Arc::from("zinternal_vector_update"));
        symtab.intern(Arc::from("zupdate_fbits"));
        symtab.intern(Arc::from("NULL"));
        symtab.intern(Arc::from("elf_entry"));
        symtab.intern(Arc::from("reg_deref"));
        symtab.intern(Arc::from("zexception"));
        symtab.intern(Arc::from("|let|"));
        symtab.intern(Arc::from("ztuplez3z5bv_z5bit0"));
        symtab.intern(Arc::from("ztuplez3z5bv_z5bit1"));
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

    /* //TODO
    pub fn intern_ty(&mut self, ty: Arc<Ty<String>>) -> Ty<Name> {
        use Ty::*;
        match &*ty {
            I64 => I64,
            I128 => I128,
            AnyBits => AnyBits,
            Bits(sz) => Bits(*sz),
            Unit => Unit,
            Bool => Bool,
            Bit => Bit,
            String => String,
            Real => Real,
            Enum(e) => Enum(self.lookup(e)),
            Struct(s) => Struct(self.lookup(s)),
            Union(u) => Union(self.lookup(u)),
            Vector(ty) => Vector(Box::new(self.intern_ty(ty))),
            FixedVector(sz, ty) => FixedVector(*sz, Box::new(self.intern_ty(ty))),
            List(ty) => List(Box::new(self.intern_ty(ty))),
            Ref(ty) => Ref(Box::new(self.intern_ty(ty))),
        }
    }

    pub fn intern_loc(&mut self, loc: Arc<Loc<String>>) -> Loc<Name> {
        use Loc::*;
        match &*loc {
            Id(v) => Id(self.lookup(v)),
            Field(loc, field) => Field(Box::new(self.intern_loc(loc)), self.lookup(field)),
            Addr(loc) => Addr(Box::new(self.intern_loc(loc))),
        }
    }

    pub fn intern_exp(&mut self, exp: Arc<Exp<String>>) -> Exp<Name> {
        use Exp::*;
        match &*exp {
            Id(v) => Id(self.lookup(v)),
            Ref(reg) => Ref(self.lookup(reg)),
            Bool(b) => Bool(*b),
            Bits(bv) => Bits(*bv),
            String(s) => String(s.clone()),
            Unit => Unit,
            I64(i) => I64(*i),
            I128(i) => I128(*i),
            Undefined(ty) => Undefined(self.intern_ty(ty)),
            Struct(s, fields) => Struct(
                self.lookup(s),
                fields.iter().map(|(field, exp)| (self.lookup(field), self.intern_exp(exp))).collect(),
            ),
            Kind(ctor, exp) => Kind(self.lookup(ctor), Box::new(self.intern_exp(exp))),
            Unwrap(ctor, exp) => Unwrap(self.lookup(ctor), Box::new(self.intern_exp(exp))),
            Field(exp, field) => Field(Box::new(self.intern_exp(exp)), self.lookup(field)),
            Call(op, args) => Call(*op, args.iter().map(|exp| self.intern_exp(exp)).collect()),
        }
    }
    */

    /* //TODO
    pub fn intern_instr<B: BV>(&mut self, instr: Arc<Instr<String, B>>) -> Instr<Name, B> {
        use Instr::*;
        match &*instr {
            Decl(v, ty) => Decl(self.intern(v), self.intern_ty(ty)),
            Init(v, ty, exp) => {
                let exp = self.intern_exp(exp);
                Init(self.intern(v), self.intern_ty(ty), exp)
            }
            Jump(exp, target, loc) => Jump(self.intern_exp(exp), *target, loc.clone()),
            Goto(target) => Goto(*target),
            Copy(loc, exp) => Copy(self.intern_loc(loc), self.intern_exp(exp)),
            Monomorphize(id) => Monomorphize(self.lookup(id)),
            Call(loc, ext, f, args) => {
                let loc = self.intern_loc(loc);
                let args = args.iter().map(|exp| self.intern_exp(exp)).collect();
                Call(loc, *ext, self.lookup(f), args)
            }
            Failure => Failure,
            Arbitrary => Arbitrary,
            End => End,
            // We split calls into primops/regular calls later, so
            // this shouldn't exist yet.
            PrimopUnary(_, _, _) => unreachable!("PrimopUnary in intern_instr"),
            PrimopBinary(_, _, _, _) => unreachable!("PrimopBinary in intern_instr"),
            PrimopVariadic(_, _, _) => unreachable!("PrimopVariadic in intern_instr"),
        }
    }
    */

    /* //TODO
    pub fn intern_def<B: BV>(&mut self, def: Arc<Def<String, B>>) -> Def<Name, B> {
        use Def::*;
        match &*def {
            Register(reg, ty) => Register(self.intern(reg), self.intern_ty(ty)),
            Let(bindings, setup) => {
                let bindings = bindings.iter().map(|(v, ty)| (self.intern(v), self.intern_ty(ty))).collect();
                let setup = setup.iter().map(|instr| self.intern_instr(instr)).collect();
                Let(bindings, setup)
            }
            Enum(e, ctors) => Enum(self.intern(e), ctors.iter().map(|ctor| self.intern(ctor)).collect()),
            Struct(s, fields) => {
                let fields = fields.iter().map(|(field, ty)| (self.intern(field), self.intern_ty(ty))).collect();
                Struct(self.intern(s), fields)
            }
            Union(u, ctors) => {
                let ctors = ctors.iter().map(|(ctor, ty)| (self.intern(ctor), self.intern_ty(ty))).collect();
                Union(self.intern(u), ctors)
            }
            Val(f, args, ret) => {
                Val(self.intern(f), args.iter().map(|ty| self.intern_ty(ty)).collect(), self.intern_ty(ret))
            }
            Extern(f, ext, args, ret) => Extern(
                self.intern(f),
                ext.clone(),
                args.iter().map(|ty| self.intern_ty(ty)).collect(),
                self.intern_ty(ret),
            ),
            Fn(f, args, body) => {
                let args = args.iter().map(|arg| self.intern(arg)).collect();
                let body = body.iter().map(|instr| self.intern_instr(instr)).collect();
                Fn(self.lookup(f), args, body)
            }
        }
    }
    */

    /* //TODO
    pub fn intern_defs<B: BV>(&mut self, defs: Arc<[Def<String, B>]>) -> Vec<Def<Name, B>> {
        defs.iter().map(|def| self.intern_def(def)).collect()
    }
    */
}

type Fn<B> = (Vec<(Name, Arc<Ty<Name>>)>, Ty<Name>, Arc<Vec<Instr<Name, B>>>);

/// All symbolic evaluation happens over some (immutable) IR. The
/// [SharedState] provides each worker that is performing symbolic
/// evaluation with a convenient view into that IR.
pub struct SharedState<B> {
    /// A map from function identifers to function bodies and parameter lists
    pub functions: HashMap<Name, Fn<B>>,
    /// The symbol table for the IR
    pub symtab: Symtab,
    /// A map from struct identifers to a map from field identifiers
    /// to their types
    pub structs: HashMap<Name, HashMap<Name, Ty<Name>>>,
    /// A map from enum identifiers to sets of their member
    /// identifiers
    pub enums: HashMap<Name, HashSet<Name>>,
    /// `enum_members` maps each enum member for every enum to it's
    /// position (as a (pos, size) pair, i.e. 1 of 3) within its
    /// respective enum
    pub enum_members: HashMap<Name, (usize, usize)>,
    /// `union_ctors` is a set of all union constructor identifiers
    pub union_ctors: HashSet<Name>,
    /// `probes` is a set of function/location identifers to trace
    pub probes: HashSet<Name>,
}

impl<B: BV> SharedState<B> {
    pub fn new(symtab: Symtab, defs: &Vec<Def<Name, B>>, probes: HashSet<Name>) -> Self {
        let mut vals = HashMap::new();
        let mut functions: HashMap<Name, Fn<B>> = HashMap::new();
        let mut structs: HashMap<Name, HashMap<Name, Ty<Name>>> = HashMap::new();
        let mut enums: HashMap<Name, HashSet<Name>> = HashMap::new();
        let mut enum_members: HashMap<Name, (usize, usize)> = HashMap::new();
        let mut union_ctors: HashSet<Name> = HashSet::new();

        for def in &*defs {
            match def {
                Def::Val(f, arg_tys, ret_ty) => {
                    vals.insert(f, (arg_tys, ret_ty));
                }

                Def::Fn(f, args, body) => match vals.get(f) {
                    None => panic!("Found fn without a val when creating the global state!"),
                    Some((arg_tys, ret_ty)) => {
                        assert!(arg_tys.len() == args.len());
                        let args = args.iter().zip(arg_tys.iter()).map(|(id, ty)| (*id, Arc::new(ty.clone()))).collect();
                        functions.insert(*f, (args, (*ret_ty).clone(), (*body).clone()));
                    }
                },

                Def::Struct(name, fields) => {
                    let fields: HashMap<_, Ty<Name>> = fields.clone().into_iter().collect();
                    structs.insert(*name, fields);
                }

                Def::Enum(name, members) => {
                    for (i, member) in members.iter().enumerate() {
                        enum_members.insert(*member, (i, members.len()));
                    }
                    let members: HashSet<_> = members.clone().into_iter().collect();
                    enums.insert(*name, members);
                }

                Def::Union(_, ctors) => {
                    for (ctor, _) in ctors {
                        union_ctors.insert(*ctor);
                    }
                }

                _ => (),
            }
        }

        SharedState { functions, symtab, structs, enums, enum_members, union_ctors, probes }
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
    externs: &HashMap<Name, String>,
    primops: &Primops<B>,
) -> Instr<Name, B> {
    match &instr {
        Instr::Call(loc, _, f, args) => match externs.get(&f) {
            Some(name) => {
                if let Some(unop) = primops.unary.get(name) {
                    assert!(args.len() == 1);
                    Instr::PrimopUnary(loc.clone(), *unop, args[0].clone())
                } else if let Some(binop) = primops.binary.get(name) {
                    assert!(args.len() == 2);
                    Instr::PrimopBinary(loc.clone(), *binop, args[0].clone(), args[1].clone())
                } else if let Some(varop) = primops.variadic.get(name) {
                    Instr::PrimopVariadic(loc.clone(), *varop, args.clone())
                } else if name == "reg_deref" {
                    Instr::Call(loc.clone(), false, REG_DEREF, args.clone())
                } else {
                    eprintln!("No primop {} ({:?})", name, f);
                    Instr::Call(loc.clone(), false, *f, args.clone())
                    // panic!("Cannot find implementation for primop {}", name)
                }
            }
            None => instr,
        },
        _ => instr,
    }
}

pub enum AssertionMode {
    Pessimistic,
    Optimistic,
}

/// Change Calls without implementations into Primops
pub(crate) fn insert_primops<B: BV>(defs: &mut [Def<Name, B>], mode: AssertionMode) {
    let mut externs: HashMap<Name, String> = HashMap::new();
    for def in defs.iter() {
        if let Def::Extern(f, ext, _, _) = def {
            externs.insert(*f, ext.to_string());
        }
    }
    match mode {
        AssertionMode::Optimistic => externs.insert(SAIL_ASSERT, "optimistic_assert".to_string()),
        AssertionMode::Pessimistic => externs.insert(SAIL_ASSERT, "pessimistic_assert".to_string()),
    };
    externs.insert(SAIL_ASSUME, "assume".to_string());
    externs.insert(BITVECTOR_UPDATE, "bitvector_update".to_string());

    let primops = Primops::default();

    for def in defs.iter_mut() {
        match def {
            Def::Fn(f, args, body) => {
                *def = Def::Fn(
                    *f,
                    args.to_vec(),
                    Arc::new(body.to_vec().into_iter().map(|instr| insert_instr_primops(instr, &externs, &primops)).collect()),
                )
            }
            Def::Let(bindings, setup) => {
                *def = Def::Let(
                    bindings.clone(),
                    Arc::new(setup.to_vec().into_iter().map(|instr| insert_instr_primops(instr, &externs, &primops)).collect()),
                )
            }
            _ => (),
        }
    }
}

/// By default each jump or goto just contains a `usize` offset into
/// the instruction vector. This representation is hard to work with,
/// so we support mapping this representation into one where any
/// instruction can have an explicit label, and jumps point to those
/// explicit labels, and then going back to the offset based
/// representation for execution.
#[derive(Debug)]
pub enum LabeledInstr<B> {
    Labeled(usize, Instr<Name, B>),
    Unlabeled(Instr<Name, B>),
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
        if let LabeledInstr::Labeled(_, _) = self {
            true
        } else {
            false
        }
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
            Labeled(label, Instr::Call(loc, ext, f, args)) if mono_fns.contains(&f) => {
                let mut ids = HashSet::new();
                args.iter().for_each(|exp| exp.collect_ids(&mut ids));

                if ids.is_empty() {
                    new_instrs.push(Labeled(label, Instr::Call(loc, ext, f, args)))
                } else {
                    for (i, id) in ids.iter().enumerate() {
                        if i == 0 {
                            new_instrs.push(Labeled(label, Instr::Monomorphize(*id)))
                        } else {
                            new_instrs.push(Unlabeled(Instr::Monomorphize(*id)))
                        }
                    }
                    new_instrs.push(Unlabeled(Instr::Call(loc, ext, f, args)))
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
            Instr::Call(_, _, f, _) if mono_fns.contains(&f) => return true,
            _ => (),
        }
    }
    false
}

pub(crate) fn insert_monomorphize<B: BV>(defs: &mut [Def<Name, B>]) {
    let mut mono_fns = HashSet::new();
    for def in defs.iter() {
        match def {
            Def::Extern(f, ext, _, _) if ext == "monomorphize" => {
                mono_fns.insert(*f);
            }
            _ => (),
        }
    }

    for def in defs.iter_mut() {
        match def {
            Def::Fn(f, args, body) if has_mono_fn(body, &mono_fns) => {
                *def = Def::Fn(*f, args.to_vec(), Arc::new(insert_monomorphize_instrs(body.to_vec(), &mono_fns)))
            }
            _ => (),
        }
    }
}
