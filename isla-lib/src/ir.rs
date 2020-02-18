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

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::concrete::{B64, BV};
use crate::primop::{Binary, Primops, Unary, Variadic};
use crate::zencode;

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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Loc<A> {
    Id(A),
    Field(Box<Loc<A>>, A),
    Addr(Box<Loc<A>>),
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
    Symbolic(u32),
    I64(i64),
    I128(i128),
    Bool(bool),
    Bits(B),
    String(String),
    Unit,
    Vector(Vec<Val<B>>),
    List(Vec<Val<B>>),
    Enum(EnumMember),
    Struct(HashMap<u32, Val<B>>),
    Ctor(u32, Box<Val<B>>),
    Ref(u32),
    Poison,
}

impl<B: BV> Val<B> {
    fn collect_symbolic_variables(&self, vars: &mut HashSet<u32>) {
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

    pub fn symbolic_variables(&self) -> HashSet<u32> {
        let mut vars = HashSet::new();
        self.collect_symbolic_variables(&mut vars);
        vars
    }

    pub fn is_symbolic(&self) -> bool {
        !self.symbolic_variables().is_empty()
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
                    .map(|(k, v)| format!("(|{}| {})", zencode::decode(symtab.to_str(*k)), v.to_string(symtab)))
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
            Ctor(ctor, v) => format!("(|{}| {})", zencode::decode(symtab.to_str(*ctor)), v.to_string(symtab)),
            Ref(reg) => format!("(_ reg |{}|)", zencode::decode(symtab.to_str(*reg))),
            Poison => "(_ poison)".to_string(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum UVal<'ir, B> {
    Uninit(&'ir Ty<u32>),
    Init(Val<B>),
}

pub type Bindings<'ir, B> = HashMap<u32, UVal<'ir, B>>;

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

#[derive(Clone)]
pub enum Instr<A, B> {
    Decl(A, Ty<A>),
    Init(A, Ty<A>, Exp<A>),
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

#[derive(Clone)]
pub enum Def<A, B> {
    Register(A, Ty<A>),
    Let(Vec<(A, Ty<A>)>, Vec<Instr<A, B>>),
    Enum(A, Vec<A>),
    Struct(A, Vec<(A, Ty<A>)>),
    Union(A, Vec<(A, Ty<A>)>),
    Val(A, Vec<Ty<A>>, Ty<A>),
    Extern(A, String, Vec<Ty<A>>, Ty<A>),
    Fn(A, Vec<A>, Vec<Instr<A, B>>),
}

pub mod serialize;

#[derive(Clone)]
pub struct Symtab<'ir> {
    symbols: Vec<&'ir str>,
    table: HashMap<&'ir str, u32>,
    next: u32,
}

pub const RETURN: u32 = 0;
pub const SAIL_ASSERT: u32 = 1;
pub const SAIL_ASSUME: u32 = 2;
pub const SAIL_EXIT: u32 = 3;
pub const CURRENT_EXCEPTION: u32 = 4;
pub const HAVE_EXCEPTION: u32 = 5;
pub const THROW_LOCATION: u32 = 6;
pub const INTERNAL_VECTOR_INIT: u32 = 7;
pub const INTERNAL_VECTOR_UPDATE: u32 = 8;
pub const BITVECTOR_UPDATE: u32 = 9;
pub const NULL: u32 = 10;
pub const ELF_ENTRY: u32 = 11;
pub const REG_DEREF: u32 = 12;

impl<'ir> Symtab<'ir> {
    pub fn intern(&mut self, sym: &'ir str) -> u32 {
        match self.table.get(sym) {
            None => {
                let n = self.next;
                self.symbols.push(sym);
                self.table.insert(sym, n);
                self.next += 1;
                n
            }
            Some(n) => *n,
        }
    }

    pub fn to_raw_table(&self) -> Vec<String> {
        self.symbols.iter().map(|sym| (*sym).to_string()).collect()
    }

    pub fn from_raw_table(raw: &'ir [String]) -> Self {
        let mut symtab =
            Symtab { symbols: Vec::with_capacity(raw.len()), table: HashMap::with_capacity(raw.len()), next: 0 };
        for sym in raw {
            symtab.intern(sym);
        }
        symtab
    }

    pub fn to_str(&self, n: u32) -> &'ir str {
        match self.symbols.get(n as usize) {
            Some(s) => s,
            None => "zUNKNOWN",
        }
    }

    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        let mut symtab = Symtab { symbols: Vec::new(), table: HashMap::new(), next: 0 };
        symtab.intern("return");
        symtab.intern("zsail_assert");
        symtab.intern("zsail_assume");
        symtab.intern("zsail_exit");
        symtab.intern("current_exception");
        symtab.intern("have_exception");
        symtab.intern("throw_location");
        symtab.intern("zinternal_vector_init");
        symtab.intern("zinternal_vector_update");
        symtab.intern("zupdate_fbits");
        symtab.intern("NULL");
        symtab.intern("elf_entry");
        symtab.intern("reg_deref");
        symtab
    }

    pub fn lookup(&self, sym: &str) -> u32 {
        *self.table.get(sym).unwrap_or_else(|| {
            eprintln!("Could not find symbol: {}", sym);
            &std::u32::MAX
        })
    }

    pub fn get(&self, sym: &str) -> Option<u32> {
        self.table.get(sym).copied()
    }

    pub fn intern_ty(&mut self, ty: &'ir Ty<String>) -> Ty<u32> {
        use Ty::*;
        match ty {
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

    pub fn intern_loc(&mut self, loc: &'ir Loc<String>) -> Loc<u32> {
        use Loc::*;
        match loc {
            Id(v) => Id(self.lookup(v)),
            Field(loc, field) => Field(Box::new(self.intern_loc(loc)), self.lookup(field)),
            Addr(loc) => Addr(Box::new(self.intern_loc(loc))),
        }
    }

    pub fn intern_exp(&mut self, exp: &'ir Exp<String>) -> Exp<u32> {
        use Exp::*;
        match exp {
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

    pub fn intern_instr<B>(&mut self, instr: &'ir Instr<String, B>) -> Instr<u32, B> {
        use Instr::*;
        match instr {
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

    pub fn intern_def<B>(&mut self, def: &'ir Def<String, B>) -> Def<u32, B> {
        use Def::*;
        match def {
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

    pub fn intern_defs<B>(&mut self, defs: &'ir [Def<String, B>]) -> Vec<Def<u32, B>> {
        defs.iter().map(|def| self.intern_def(def)).collect()
    }
}

type Fn<'ir, B> = (Vec<(u32, &'ir Ty<u32>)>, Ty<u32>, &'ir [Instr<u32, B>]);

pub struct SharedState<'ir, B> {
    pub functions: HashMap<u32, Fn<'ir, B>>,
    pub symtab: Symtab<'ir>,
    pub structs: HashMap<u32, HashMap<u32, Ty<u32>>>,
    /// `enums` is a map from enum identifiers to sets of their member identifiers
    pub enums: HashMap<u32, HashSet<u32>>,
    /// `enum_members` maps each enum member for every enum to it's
    /// position (as a (pos, size) pair, i.e. 1 of 3) within its
    /// respective enum
    pub enum_members: HashMap<u32, (usize, usize)>,
    /// `union_ctors` is a set of all union constructor identifiers
    pub union_ctors: HashSet<u32>,
    /// `probes` is a set of function identifers to trace
    pub probes: HashSet<u32>,
}

impl<'ir, B: BV> SharedState<'ir, B> {
    pub fn new(symtab: Symtab<'ir>, defs: &'ir [Def<u32, B>], probes: HashSet<u32>) -> Self {
        let mut vals = HashMap::new();
        let mut functions: HashMap<u32, Fn<'ir, B>> = HashMap::new();
        let mut structs: HashMap<u32, HashMap<u32, Ty<u32>>> = HashMap::new();
        let mut enums: HashMap<u32, HashSet<u32>> = HashMap::new();
        let mut enum_members: HashMap<u32, (usize, usize)> = HashMap::new();
        let mut union_ctors: HashSet<u32> = HashSet::new();

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
                        functions.insert(*f, (args, (*ret_ty).clone(), body));
                    }
                },

                Def::Struct(name, fields) => {
                    let fields: HashMap<_, _> = fields.clone().into_iter().collect();
                    structs.insert(*name, fields);
                }

                Def::Enum(name, members) => {
                    assert!(members.len() < 256);
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

    pub fn enum_member(&self, member: &str) -> Option<usize> {
        let member = self.symtab.get(&zencode::encode(member))?;
        self.enum_members.get(&member).map(|(pos, _)| *pos)
    }
}

fn insert_instr_primops<B: BV>(
    instr: Instr<u32, B>,
    externs: &HashMap<u32, String>,
    primops: &Primops<B>,
) -> Instr<u32, B> {
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
                    eprintln!("No primop {} ({})", name, f);
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
pub fn insert_primops<B: BV>(defs: &mut [Def<u32, B>], mode: AssertionMode) {
    let mut externs: HashMap<u32, String> = HashMap::new();
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
                    body.to_vec().into_iter().map(|instr| insert_instr_primops(instr, &externs, &primops)).collect(),
                )
            }
            Def::Let(bindings, setup) => {
                *def = Def::Let(
                    bindings.clone(),
                    setup.to_vec().into_iter().map(|instr| insert_instr_primops(instr, &externs, &primops)).collect(),
                )
            }
            _ => (),
        }
    }
}
