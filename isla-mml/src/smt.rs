// BSD 2-Clause License
//
// Copyright (c) 2022 Alasdair Armstrong
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

use id_arena::{Arena, Id};
use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap};
use std::io;
use std::io::Write;
use std::ops::Index;
use std::sync::atomic::{AtomicU32, Ordering};

use isla_lib::ir::Typedefs;
use isla_lib::simplify::write_bits;
use isla_lib::smt::{EnumId, EnumMember, Sym};
use isla_lib::zencode;

use crate::memory_model::constants::*;
use crate::memory_model::{
    Binary, Check, Def, Error, Exp, ExpArena, ExpId, MemoryModel, Name, Spanned, Symtab, TyAnnot, Unary,
};

/// Event ids are `u32` variables denoted in the generated SMTLIB as
/// `evX` where X is a number greater than 0. The arguments to
/// toplevel relations and sets are always `ev1` and `ev2`.
pub type EventId = u32;

static FRESH_COUNTER: AtomicU32 = AtomicU32::new(3);

fn fresh() -> EventId {
    FRESH_COUNTER.fetch_add(1, Ordering::SeqCst)
}

pub type SexpId = Id<Sexp>;

#[derive(Clone, Debug)]
pub enum BitWidth {
    Fixed(u32),
    Index(Name),
}

#[derive(Clone, Debug)]
pub enum Sexp {
    Atom(Name),
    Bits(Vec<bool>),
    Int(u32),
    List(Vec<SexpId>),
    /// An event identifier in the event graph
    Event(EventId),
    /// A symbolic variable from an Isla trace
    Symbolic(Sym),
    /// The bitvector type of length `N`: `(_ BitVec N)`
    BitVec(BitWidth),
    /// A member of an enumeration
    Enum(EnumMember),
    /// An enumeration type name
    EnumTy(EnumId),
}

/// An arena where we can allocate S-expressions, freeing all at
/// once. The advantages of using an arena allocator here is that we
/// can alias and copy SexpIds freely without worring about their
/// lifetimes. Various common S-expression components are
/// pre-allocated as public fields.
#[derive(Clone)]
pub struct SexpArena {
    arena: Arena<Sexp>,
    pub and: SexpId,
    pub array: SexpId,
    pub assert: SexpId,
    pub atom_as: SexpId,
    pub atom_const: SexpId,
    pub bool_false: SexpId,
    pub bool_true: SexpId,
    pub bool_ty: SexpId,
    pub declare_const: SexpId,
    pub declare_fun: SexpId,
    pub define_const: SexpId,
    pub define_fun: SexpId,
    pub eq: SexpId,
    pub event: SexpId,
    pub exclamation: SexpId,
    pub exists: SexpId,
    pub extract: SexpId,
    pub forall: SexpId,
    pub implies: SexpId,
    pub ite: SexpId,
    pub letbind: SexpId,
    pub named: SexpId,
    pub not: SexpId,
    pub or: SexpId,
    pub sign_extend: SexpId,
    pub underscore: SexpId,
    pub zero_extend: SexpId,
    pub index: SexpId,
    pub ev1: SexpId,
    pub ev2: SexpId,
}

impl Index<SexpId> for SexpArena {
    type Output = Sexp;

    fn index(&self, i: SexpId) -> &Self::Output {
        &self.arena[i]
    }
}

impl SexpArena {
    pub fn new() -> Self {
        let mut arena = Arena::new();

        let and = arena.alloc(Sexp::Atom(AND.name()));
        let array = arena.alloc(Sexp::Atom(ARRAY.name()));
        let assert = arena.alloc(Sexp::Atom(ASSERT.name()));
        let atom_as = arena.alloc(Sexp::Atom(AS.name()));
        let atom_const = arena.alloc(Sexp::Atom(CONST.name()));
        let bool_false = arena.alloc(Sexp::Atom(FALSE.name()));
        let bool_true = arena.alloc(Sexp::Atom(TRUE.name()));
        let bool_ty = arena.alloc(Sexp::Atom(BOOL.name()));
        let declare_const = arena.alloc(Sexp::Atom(DECLARE_CONST.name()));
        let declare_fun = arena.alloc(Sexp::Atom(DECLARE_FUN.name()));
        let define_const = arena.alloc(Sexp::Atom(DEFINE_CONST.name()));
        let define_fun = arena.alloc(Sexp::Atom(DEFINE_FUN.name()));
        let eq = arena.alloc(Sexp::Atom(EQ.name()));
        let event = arena.alloc(Sexp::Atom(EVENT.name()));
        let exclamation = arena.alloc(Sexp::Atom(EXCLAMATION.name()));
        let exists = arena.alloc(Sexp::Atom(EXISTS.name()));
        let extract = arena.alloc(Sexp::Atom(EXTRACT.name()));
        let forall = arena.alloc(Sexp::Atom(FORALL.name()));
        let implies = arena.alloc(Sexp::Atom(IMPLIES.name()));
        let ite = arena.alloc(Sexp::Atom(ITE.name()));
        let letbind = arena.alloc(Sexp::Atom(LET.name()));
        let named = arena.alloc(Sexp::Atom(NAMED.name()));
        let not = arena.alloc(Sexp::Atom(NOT.name()));
        let or = arena.alloc(Sexp::Atom(OR.name()));
        let sign_extend = arena.alloc(Sexp::Atom(SIGN_EXTEND.name()));
        let underscore = arena.alloc(Sexp::Atom(UNDERSCORE.name()));
        let zero_extend = arena.alloc(Sexp::Atom(ZERO_EXTEND.name()));
        let index = arena.alloc(Sexp::Atom(INDEX.name()));
        let ev1 = arena.alloc(Sexp::Event(1));
        let ev2 = arena.alloc(Sexp::Event(2));

        SexpArena {
            and,
            arena,
            array,
            assert,
            atom_as,
            atom_const,
            bool_false,
            bool_true,
            bool_ty,
            declare_const,
            declare_fun,
            define_const,
            define_fun,
            eq,
            event,
            exclamation,
            exists,
            extract,
            forall,
            implies,
            ite,
            letbind,
            named,
            not,
            or,
            sign_extend,
            underscore,
            zero_extend,
            index,
            ev1,
            ev2,
        }
    }

    pub fn alloc(&mut self, sexp: Sexp) -> SexpId {
        self.arena.alloc(sexp)
    }

    pub fn alloc_bitvec(&mut self, width: u32) -> SexpId {
        self.arena.alloc(Sexp::BitVec(BitWidth::Fixed(width)))
    }

    pub fn alloc_default_value(&mut self, ty: SexpId) -> SexpId {
        match self[ty] {
            Sexp::Atom(id) if id == BOOL.name() => self.bool_false,
            // FIXME
            Sexp::BitVec(BitWidth::Fixed(n)) => self.alloc(Sexp::Bits(vec![false; n as usize])),
            Sexp::EnumTy(e) => self.alloc(Sexp::Enum(e.first_member())),
            _ => unreachable!(),
        }
    }

    fn alloc_exists(&mut self, e: SexpId, sexp: Sexp) -> SexpId {
        let sexp = self.alloc(sexp);
        let var = self.alloc(Sexp::List(vec![e, self.event]));
        let vars = self.alloc(Sexp::List(vec![var]));
        self.alloc(Sexp::List(vec![self.exists, vars, sexp]))
    }

    fn alloc_exists_id(&mut self, e: SexpId, sexp: SexpId) -> SexpId {
        let var = self.alloc(Sexp::List(vec![e, self.event]));
        let vars = self.alloc(Sexp::List(vec![var]));
        self.alloc(Sexp::List(vec![self.exists, vars, sexp]))
    }

    fn alloc_multi_exists(&mut self, vs: &[(Name, SexpId)], body: SexpId) -> SexpId {
        let mut vars = Vec::new();
        for (v, x) in vs {
            let v = self.alloc(Sexp::Atom(*v));
            vars.push(self.alloc(Sexp::List(vec![v, *x])))
        }
        let vars = self.alloc(Sexp::List(vars));
        self.alloc(Sexp::List(vec![self.exists, vars, body]))
    }

    fn alloc_multi_forall(&mut self, vs: &[(Name, SexpId)], body: SexpId) -> SexpId {
        let mut vars = Vec::new();
        for (v, x) in vs {
            let v = self.alloc(Sexp::Atom(*v));
            vars.push(self.alloc(Sexp::List(vec![v, *x])))
        }
        let vars = self.alloc(Sexp::List(vars));
        self.alloc(Sexp::List(vec![self.forall, vars, body]))
    }

    fn alloc_multi_forall_sexp(&mut self, vs: &[(SexpId, SexpId)], body: SexpId) -> SexpId {
        let mut vars = Vec::new();
        for (v, x) in vs {
            vars.push(self.alloc(Sexp::List(vec![*v, *x])))
        }
        let vars = self.alloc(Sexp::List(vars));
        self.alloc(Sexp::List(vec![self.forall, vars, body]))
    }

    fn alloc_letbind(&mut self, vs: &[(Name, SexpId)], body: SexpId) -> SexpId {
        let mut vars = Vec::new();
        for (v, x) in vs {
            let v = self.alloc(Sexp::Atom(*v));
            vars.push(self.alloc(Sexp::List(vec![v, *x])))
        }
        let vars = self.alloc(Sexp::List(vars));
        self.alloc(Sexp::List(vec![self.letbind, vars, body]))
    }

    /// Gets all the enum type sexprs currently allocated in the arena
    pub fn enum_ids(&self) -> Vec<EnumId> {
        self.arena.iter().filter_map(|(_, sexp)| if let Sexp::EnumTy(id) = sexp { Some(*id) } else { None }).collect()
    }

    pub fn alloc_define_fun(
        &mut self,
        name: Name,
        params: &[(SexpId, SexpId)],
        ret_ty: SexpId,
        body: SexpId,
    ) -> SexpId {
        let name = self.alloc(Sexp::Atom(name));

        let params = params.iter().copied().map(|(name, ty)| self.alloc(Sexp::List(vec![name, ty]))).collect();
        let params = self.alloc(Sexp::List(params));

        self.alloc(Sexp::List(vec![self.define_fun, name, params, ret_ty, body]))
    }

    pub fn alloc_or(&mut self, disj: Vec<SexpId>) -> SexpId {
        if disj.is_empty() {
            self.bool_false
        } else {
            self.alloc(Sexp::List(disj))
        }
    }
}

impl Sexp {
    fn write(
        &self,
        buf: &mut dyn Write,
        sexps: &SexpArena,
        symtab: &Symtab,
        typedefs: Typedefs,
        bitwidths: &HashMap<Name, u32>,
    ) -> std::io::Result<()> {
        match self {
            Sexp::Atom(n) => write!(buf, "{}", &symtab[*n]),
            Sexp::Int(i) => write!(buf, "{}", i),
            Sexp::Event(id) => write!(buf, "ev{}", id),
            Sexp::Symbolic(v) => write!(buf, "v{}", v),
            Sexp::BitVec(width) => match width {
                BitWidth::Fixed(n) => write!(buf, "(_ BitVec {})", n),
                BitWidth::Index(i) => {
                    if let Some(n) = bitwidths.get(i) {
                        write!(buf, "(_ BitVec {})", n)
                    } else {
                        write!(buf, "Enum1")
                    }
                }
            },
            Sexp::Enum(e) => {
                let members = typedefs.enums.get(&e.enum_id.to_name()).ok_or_else(|| {
                    io::Error::new(io::ErrorKind::Other, format!("Failed to get enumeration '{}'", e.enum_id.to_name()))
                })?;
                let name = zencode::decode(typedefs.symtab.to_str(members[e.member]));
                write!(buf, "{}", name)
            }
            Sexp::EnumTy(enum_id) => {
                let name = zencode::decode(typedefs.symtab.to_str(enum_id.to_name()));
                write!(buf, "{}", name)
            }
            Sexp::Bits(bv) => write_bits(buf, bv),
            Sexp::List(xs) => {
                if let Some((last, rest)) = xs.split_last() {
                    write!(buf, "(")?;
                    for x in rest {
                        sexps[*x].write(buf, sexps, symtab, typedefs, bitwidths)?;
                        write!(buf, " ")?
                    }
                    sexps[*last].write(buf, sexps, symtab, typedefs, bitwidths)?;
                    write!(buf, ")")
                } else {
                    write!(buf, "nil")
                }
            }
        }
    }
}

pub fn write_sexps(
    buf: &mut dyn Write,
    xs: &[SexpId],
    sexps: &SexpArena,
    symtab: &Symtab,
    typedefs: Typedefs,
    bitwidths: &HashMap<Name, u32>,
) -> std::io::Result<()> {
    for x in xs {
        sexps[*x].write(buf, sexps, symtab, typedefs, bitwidths)?;
        write!(buf, "\n\n")?
    }
    Ok(())
}

fn relation_arity_name(n: usize) -> Cow<'static, str> {
    match n {
        0 => Cow::Borrowed("value"),
        1 => Cow::Borrowed("set"),
        2 => Cow::Borrowed("binary relation"),
        n => Cow::Owned(format!("{}-ary relation", n)),
    }
}

fn count_wildcards(args: &[Option<ExpId>]) -> usize {
    let mut wildcards = 0;
    for arg in args {
        if arg.is_none() {
            wildcards += 1
        }
    }
    wildcards
}

pub fn compile_type(
    ty: &Spanned<Exp>,
    typedefs: Typedefs,
    exps: &ExpArena,
    sexps: &mut SexpArena,
    symtab: &Symtab,
) -> Result<SexpId, Error> {
    let result = match &ty.node {
        Exp::Id(id) if *id == EVENT.name() => Ok(sexps.event),
        Exp::Id(id) if *id == BOOL.name() => Ok(sexps.bool_ty),
        Exp::Id(id) => {
            // Translate id into a Sail IR name
            if let Some(id_str) = symtab.get(*id) {
                let id = typedefs.symtab.lookup(&zencode::encode(id_str));
                Ok(sexps.alloc(Sexp::EnumTy(EnumId::from_name(id))))
            } else {
                Err("No enum with this name")
            }
        }
        Exp::App(f, args) if *f == BITS.name() => match args.as_slice() {
            &[Some(arg)] => {
                let arg = &exps[arg];
                match &arg.node {
                    Exp::Int(n) => {
                        if let Ok(n) = (*n).try_into() {
                            Ok(sexps.alloc(Sexp::BitVec(BitWidth::Fixed(n))))
                        } else {
                            Err("bits type argument out of bounds")
                        }
                    }
                    Exp::Id(id) => Ok(sexps.alloc(Sexp::BitVec(BitWidth::Index(*id)))),
                    _ => Err("bits type argument must be a natural number"),
                }
            }
            _ => Err("bits type expects a single numeric argument"),
        },
        _ => Err("Could not generate SMT compatible type"),
    };
    result.map_err(|msg| Error { message: msg.to_string(), file: ty.file, span: ty.span })
}

pub fn compile_tyannot(
    tyannot: &TyAnnot,
    typedefs: Typedefs,
    exps: &ExpArena,
    sexps: &mut SexpArena,
    symtab: &Symtab,
) -> Result<SexpId, Error> {
    if let Some(ty) = tyannot {
        compile_type(&exps[*ty], typedefs, exps, sexps, symtab)
    } else {
        Ok(sexps.event)
    }
}

pub fn compile_exp(
    exp: &Spanned<Exp>,
    evs: &[SexpId],
    typedefs: Typedefs,
    exps: &ExpArena,
    sexps: &mut SexpArena,
    symtab: &mut Symtab,
    compiled: &mut Vec<SexpId>,
) -> Result<SexpId, Error> {
    match &exp.node {
        Exp::Empty => Ok(sexps.bool_false),

        Exp::Int(_) => Err(Error { message: "unexpected integer".to_string(), file: exp.file, span: exp.span }),

        Exp::App(f, args) if *f == DOMAIN.name() => match args.as_slice() {
            [Some(arg)] => {
                let range_ev = sexps.alloc(Sexp::Event(fresh()));
                let mut evs_with_range = evs.to_owned();
                evs_with_range.push(range_ev);
                let rel = compile_exp(&exps[*arg], &evs_with_range, typedefs, exps, sexps, symtab, compiled)?;
                Ok(sexps.alloc_exists_id(range_ev, rel))
            }
            _ => Err(Error { message: "range expects a single argument".to_string(), file: exp.file, span: exp.span }),
        },

        Exp::App(f, args) if *f == RANGE.name() => match args.as_slice() {
            [Some(arg)] => {
                let domain_ev = sexps.alloc(Sexp::Event(fresh()));
                let mut evs_with_domain = vec![domain_ev];
                evs_with_domain.extend_from_slice(evs);
                let rel = compile_exp(&exps[*arg], &evs_with_domain, typedefs, exps, sexps, symtab, compiled)?;
                Ok(sexps.alloc_exists_id(domain_ev, rel))
            }
            _ => Err(Error { message: "range expects a single argument".to_string(), file: exp.file, span: exp.span }),
        },

        Exp::App(f, args) if *f == EXTRACT.name() => match args.as_slice() {
            [Some(hi), Some(lo), Some(arg)] => match (&exps[*hi].node, &exps[*lo].node) {
                (Exp::Int(hi), Exp::Int(lo)) => {
                    let hi = sexps.alloc(Sexp::Int(*hi as u32));
                    let lo = sexps.alloc(Sexp::Int(*lo as u32));
                    let extract = sexps.alloc(Sexp::List(vec![sexps.underscore, sexps.extract, hi, lo]));
                    let arg = compile_exp(&exps[*arg], &[], typedefs, exps, sexps, symtab, compiled)?;
                    Ok(sexps.alloc(Sexp::List(vec![extract, arg])))
                }
                _ => Err(Error {
                    message: "extract must have integer literals as the first two arguments".to_string(),
                    file: exp.file,
                    span: exp.span,
                }),
            },
            _ => {
                Err(Error { message: "extract expects a three arguments".to_string(), file: exp.file, span: exp.span })
            }
        },

        Exp::App(f, args) => {
            let wildcards = count_wildcards(args);
            if !(wildcards == evs.len() || wildcards == 0) {
                return Err(Error {
                    message: format!(
                        "Incorrect number of wildcards in function call. Either {} or 0 allowed, {} found",
                        evs.len(),
                        wildcards
                    ),
                    file: exp.file,
                    span: exp.span,
                });
            }

            let mut wildcard: usize = 0;
            let mut sexp_args = Vec::new();
            for arg in args {
                if let Some(arg) = arg {
                    let sexp = compile_exp(&exps[*arg], &[], typedefs, exps, sexps, symtab, compiled)?;
                    sexp_args.push(sexp)
                } else {
                    sexp_args.push(evs[wildcard]);
                    wildcard += 1
                }
            }

            let f = sexps.alloc(Sexp::Atom(*f));
            let mut xs = vec![f];
            xs.append(&mut sexp_args);
            xs.extend_from_slice(&evs[wildcard..]);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Bits(bv) => Ok(sexps.alloc(Sexp::Bits(bv.clone()))),

        Exp::IfThen(v, lhs, rhs) => {
            // generate (and (=> v lhs) (=> (not v) rhs)
            let vid = sexps.alloc(Sexp::Atom(*v));

            let xs = vec![sexps.implies, vid, compile_exp(&exps[*lhs], evs, typedefs, exps, sexps, symtab, compiled)?];

            let lhs_impl = sexps.alloc(Sexp::List(xs));

            let rhs_impl = match rhs {
                // for just `if V then R` generate (and ... (=> (not v) true))
                None => sexps.bool_true,
                Some(exp) => {
                    let negvid = sexps.alloc(Sexp::List(vec![sexps.not, vid]));
                    let ys = vec![
                        sexps.implies,
                        negvid,
                        compile_exp(&exps[*exp], evs, typedefs, exps, sexps, symtab, compiled)?,
                    ];
                    sexps.alloc(Sexp::List(ys))
                }
            };

            Ok(sexps.alloc(Sexp::List(vec![sexps.and, lhs_impl, rhs_impl])))
        }

        Exp::Id(f) => {
            if evs.is_empty() {
                Ok(sexps.alloc(Sexp::Atom(*f)))
            } else {
                let f = sexps.alloc(Sexp::Atom(*f));
                let mut xs = vec![f];
                xs.extend_from_slice(evs);
                Ok(sexps.alloc(Sexp::List(xs)))
            }
        }

        Exp::Cartesian(x, y) => match evs {
            &[ev1, ev2] => match (x, y) {
                (Some(x), Some(y)) => {
                    let mut xs = vec![sexps.and];
                    xs.push(compile_exp(&exps[*x], &[ev1], typedefs, exps, sexps, symtab, compiled)?);
                    xs.push(compile_exp(&exps[*y], &[ev2], typedefs, exps, sexps, symtab, compiled)?);
                    Ok(sexps.alloc(Sexp::List(xs)))
                }
                (Some(x), None) => compile_exp(&exps[*x], &[ev1], typedefs, exps, sexps, symtab, compiled),
                (None, Some(y)) => compile_exp(&exps[*y], &[ev2], typedefs, exps, sexps, symtab, compiled),
                (None, None) => Ok(sexps.bool_true),
            },
            _ => Err(Error {
                message: format!(
                    "Cartesian product in a context where a {} was expected, rather than a binary relation",
                    relation_arity_name(evs.len()),
                ),
                file: exp.file,
                span: exp.span,
            }),
        },

        Exp::Binary(Binary::Diff, x, y) => {
            let mut xs = vec![sexps.and];
            xs.push(compile_exp(&exps[*x], evs, typedefs, exps, sexps, symtab, compiled)?);
            let y = compile_exp(&exps[*y], evs, typedefs, exps, sexps, symtab, compiled)?;
            xs.push(sexps.alloc(Sexp::List(vec![sexps.not, y])));
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Binary(Binary::Union, x, y) => {
            let mut xs = vec![sexps.or];
            xs.push(compile_exp(&exps[*x], evs, typedefs, exps, sexps, symtab, compiled)?);
            xs.push(compile_exp(&exps[*y], evs, typedefs, exps, sexps, symtab, compiled)?);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Binary(Binary::Inter, x, y) => {
            let mut xs = vec![sexps.and];
            xs.push(compile_exp(&exps[*x], evs, typedefs, exps, sexps, symtab, compiled)?);
            xs.push(compile_exp(&exps[*y], evs, typedefs, exps, sexps, symtab, compiled)?);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Binary(Binary::Implies, x, y) => {
            let mut xs = vec![sexps.implies];
            xs.push(compile_exp(&exps[*x], evs, typedefs, exps, sexps, symtab, compiled)?);
            xs.push(compile_exp(&exps[*y], evs, typedefs, exps, sexps, symtab, compiled)?);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Binary(Binary::In, x, set) => {
            if evs.is_empty() {
                let mut args = Vec::new();
                match &exps[*x].node {
                    Exp::Tuple(xs) => {
                        for x in xs {
                            args.push(compile_exp(&exps[*x], &[], typedefs, exps, sexps, symtab, compiled)?)
                        }
                    }
                    _ => args.push(compile_exp(&exps[*x], &[], typedefs, exps, sexps, symtab, compiled)?),
                }
                compile_exp(&exps[*set], &args, typedefs, exps, sexps, symtab, compiled)
            } else {
                Err(Error {
                    message: format!(
                        "Boolean set membership in a context where a {} was expected",
                        relation_arity_name(evs.len())
                    ),
                    file: exp.file,
                    span: exp.span,
                })
            }
        }

        Exp::Binary(Binary::Seq, x, y) => match evs {
            &[ev1, ev2] => {
                let ev3 = sexps.alloc(Sexp::Event(fresh()));
                let mut xs = vec![sexps.and];
                xs.push(compile_exp(&exps[*x], &[ev1, ev3], typedefs, exps, sexps, symtab, compiled)?);
                xs.push(compile_exp(&exps[*y], &[ev3, ev2], typedefs, exps, sexps, symtab, compiled)?);
                Ok(sexps.alloc_exists(ev3, Sexp::List(xs)))
            }
            _ => Err(Error {
                message: format!(
                    "Sequential composition in a context where a {} was expected, rather than a binary relation",
                    relation_arity_name(evs.len())
                ),
                file: exp.file,
                span: exp.span,
            }),
        },

        Exp::Binary(Binary::Eq, x, y) => {
            let mut xs = vec![sexps.eq];
            xs.push(compile_exp(&exps[*x], evs, typedefs, exps, sexps, symtab, compiled)?);
            xs.push(compile_exp(&exps[*y], evs, typedefs, exps, sexps, symtab, compiled)?);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Binary(Binary::Neq, x, y) => {
            let mut xs = vec![sexps.eq];
            xs.push(compile_exp(&exps[*x], evs, typedefs, exps, sexps, symtab, compiled)?);
            xs.push(compile_exp(&exps[*y], evs, typedefs, exps, sexps, symtab, compiled)?);
            let eq = sexps.alloc(Sexp::List(xs));
            Ok(sexps.alloc(Sexp::List(vec![sexps.not, eq])))
        }

        Exp::Unary(Unary::Compl, x) => {
            let mut xs = vec![sexps.not];
            xs.push(compile_exp(&exps[*x], evs, typedefs, exps, sexps, symtab, compiled)?);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Unary(Unary::Identity, x) => match evs {
            &[ev1, ev2] => {
                let mut xs = vec![sexps.and];
                xs.push(compile_exp(&exps[*x], &[ev1], typedefs, exps, sexps, symtab, compiled)?);
                xs.push(compile_exp(&exps[*x], &[ev2], typedefs, exps, sexps, symtab, compiled)?);
                xs.push(sexps.alloc(Sexp::List(vec![sexps.eq, ev1, ev2])));
                Ok(sexps.alloc(Sexp::List(xs)))
            }
            _ => Err(Error {
                message: format!(
                    "Identity in a context where a {} was expected, rather than a binary relation",
                    relation_arity_name(evs.len())
                ),
                file: exp.file,
                span: exp.span,
            }),
        },

        Exp::Unary(Unary::IdentityUnion, x) => match evs {
            &[ev1, ev2] => {
                let mut xs = vec![sexps.or];
                xs.push(compile_exp(&exps[*x], &[ev1, ev2], typedefs, exps, sexps, symtab, compiled)?);
                xs.push(sexps.alloc(Sexp::List(vec![sexps.eq, ev1, ev2])));
                Ok(sexps.alloc(Sexp::List(xs)))
            }
            _ => Err(Error {
                message: format!(
                    "Union with identity in a context where a {} was expected, rather than a binary relation",
                    relation_arity_name(evs.len())
                ),
                file: exp.file,
                span: exp.span,
            }),
        },

        Exp::Unary(Unary::Inverse, x) => match evs {
            &[ev1, ev2] => compile_exp(&exps[*x], &[ev2, ev1], typedefs, exps, sexps, symtab, compiled),
            _ => Err(Error {
                message: format!(
                    "Inverse in a context where a {} was expected, rather than a binary relation",
                    relation_arity_name(evs.len())
                ),
                file: exp.file,
                span: exp.span,
            }),
        },

        Exp::Unary(closure_op @ (Unary::TClosure | Unary::RTClosure), x) => match evs {
            &[_, _] => {
                if let Unary::TClosure = closure_op {
                    compile_closure(false, &exps[*x], evs, typedefs, exps, sexps, symtab, compiled)
                } else {
                    compile_closure(true, &exps[*x], evs, typedefs, exps, sexps, symtab, compiled)
                }
            }
            _ => Err(Error {
                message: format!(
                    "Closure operator in a context where a {} was expected, rather than a binary relation",
                    relation_arity_name(evs.len())
                ),
                file: exp.file,
                span: exp.span,
            }),
        },

        Exp::Set(v, _, body) => match evs {
            &[ev1] => {
                let body = compile_exp(&exps[*body], &[], typedefs, exps, sexps, symtab, compiled)?;
                Ok(sexps.alloc_letbind(&[(*v, ev1)], body))
            }
            _ => Err(Error {
                message: format!("Explicit set in a context where a {} was expected", relation_arity_name(evs.len())),
                file: exp.file,
                span: exp.span,
            }),
        },

        Exp::Relation(v1, _, v2, _, body) => match evs {
            &[ev1, ev2] => {
                let body = compile_exp(&exps[*body], &[], typedefs, exps, sexps, symtab, compiled)?;
                Ok(sexps.alloc_letbind(&[(*v1, ev1), (*v2, ev2)], body))
            }
            _ => Err(Error {
                message: format!(
                    "Explicit relation in a context where a {} was expected",
                    relation_arity_name(evs.len())
                ),
                file: exp.file,
                span: exp.span,
            }),
        },

        Exp::Forall(args, body) => {
            if evs.is_empty() {
                let body = compile_exp(&exps[*body], &[], typedefs, exps, sexps, symtab, compiled)?;
                let mut compiled_args = Vec::new();
                for (n, tyannot) in args {
                    compiled_args.push((*n, compile_tyannot(tyannot, typedefs, exps, sexps, symtab)?))
                }
                Ok(sexps.alloc_multi_forall(&compiled_args, body))
            } else {
                Err(Error {
                    message: format!(
                        "Universal quantifier in a context where a {} was expected",
                        relation_arity_name(evs.len())
                    ),
                    file: exp.file,
                    span: exp.span,
                })
            }
        }

        Exp::Exists(args, body) => {
            if evs.is_empty() {
                let body = compile_exp(&exps[*body], &[], typedefs, exps, sexps, symtab, compiled)?;
                let mut compiled_args = Vec::new();
                for (n, tyannot) in args {
                    compiled_args.push((*n, compile_tyannot(tyannot, typedefs, exps, sexps, symtab)?))
                }
                Ok(sexps.alloc_multi_exists(&compiled_args, body))
            } else {
                Err(Error {
                    message: format!(
                        "Existential quantifier in a context where a {} was expected",
                        relation_arity_name(evs.len())
                    ),
                    file: exp.file,
                    span: exp.span,
                })
            }
        }

        Exp::WhereForall(rel, args, cond) => {
            let cond = compile_exp(&exps[*cond], &[], typedefs, exps, sexps, symtab, compiled)?;
            let mut compiled_args = Vec::new();
            for (n, tyannot) in args {
                compiled_args.push((*n, compile_tyannot(tyannot, typedefs, exps, sexps, symtab)?))
            }
            let rel = compile_exp(&exps[*rel], evs, typedefs, exps, sexps, symtab, compiled)?;
            let body = sexps.alloc(Sexp::List(vec![sexps.and, cond, rel]));
            Ok(sexps.alloc_multi_forall(&compiled_args, body))
        }

        Exp::WhereExists(rel, args, cond) => {
            let cond = compile_exp(&exps[*cond], &[], typedefs, exps, sexps, symtab, compiled)?;
            let mut compiled_args = Vec::new();
            for (n, tyannot) in args {
                compiled_args.push((*n, compile_tyannot(tyannot, typedefs, exps, sexps, symtab)?))
            }
            let rel = compile_exp(&exps[*rel], evs, typedefs, exps, sexps, symtab, compiled)?;
            let body = sexps.alloc(Sexp::List(vec![sexps.and, cond, rel]));
            Ok(sexps.alloc_multi_exists(&compiled_args, body))
        }

        Exp::SetLiteral(elements) => {
            let mut disj = vec![sexps.or];
            for element in elements.iter() {
                let element = &exps[*element];
                match &element.node {
                    Exp::Tuple(xs) if xs.len() == evs.len() => {
                        let mut conj = vec![sexps.and];
                        for (x, ev) in xs.iter().zip(evs.iter().copied()) {
                            let x = compile_exp(&exps[*x], &[], typedefs, exps, sexps, symtab, compiled)?;
                            conj.push(sexps.alloc(Sexp::List(vec![sexps.eq, ev, x])))
                        }
                        disj.push(sexps.alloc(Sexp::List(conj)))
                    }
                    _ if evs.len() == 1 => {
                        let x = compile_exp(element, &[], typedefs, exps, sexps, symtab, compiled)?;
                        disj.push(sexps.alloc(Sexp::List(vec![sexps.eq, evs[0], x])))
                    }
                    _ => {
                        return Err(Error {
                            message: format!(
                            "Set literal must contain only tuples with length {} in a context where a {} was expected",
                            evs.len(),
                            relation_arity_name(evs.len())
                        ),
                            file: element.file,
                            span: element.span,
                        })
                    }
                }
            }
            Ok(sexps.alloc(Sexp::List(disj)))
        }

        Exp::Accessor(exp, accs) => {
            let exp = compile_exp(&exps[*exp], &[], typedefs, exps, sexps, symtab, compiled)?;
            let accessor_function = sexps.alloc(Sexp::Atom(symtab.encode_accessors(accs)));
            Ok(sexps.alloc(Sexp::List(vec![accessor_function, exp])))
        }

        Exp::IndexedAccessor(exp, index, accs) => {
            let exp = compile_exp(&exps[*exp], &[], typedefs, exps, sexps, symtab, compiled)?;
            let index = compile_exp(&exps[*index], &[], typedefs, exps, sexps, symtab, compiled)?;
            let accessor_function = sexps.alloc(Sexp::Atom(symtab.encode_accessors(accs)));
            Ok(sexps.alloc(Sexp::List(vec![accessor_function, exp, index])))
        }

        Exp::Tuple(_) => Err(Error { message: "Unexpected tuple".to_string(), file: exp.file, span: exp.span }),
    }
}

// Compiles either the reflexive transitive closure, or the transitive closure of an expression X.
//
// Will create a new top-level definition to define the closure, so
// it is important that X^+ does not reference any local variables.
fn compile_closure(
    reflexive: bool,
    exp: &Spanned<Exp>,
    evs: &[SexpId],
    typedefs: Typedefs,
    exps: &ExpArena,
    sexps: &mut SexpArena,
    symtab: &mut Symtab,
    compiled: &mut Vec<SexpId>,
) -> Result<SexpId, Error> {
    let closure_id = sexps.alloc(Sexp::Atom(symtab.intern_owned(format!("__closure{}", fresh()))));

    let declaration_type = sexps.alloc(Sexp::List(vec![sexps.event, sexps.event]));
    let declaration = sexps.alloc(Sexp::List(vec![sexps.declare_fun, closure_id, declaration_type, sexps.bool_ty]));
    compiled.push(declaration);

    let ev1 = sexps.alloc(Sexp::Event(fresh()));
    let ev2 = sexps.alloc(Sexp::Event(fresh()));
    let ev3 = sexps.alloc(Sexp::Event(fresh()));

    let closure_1_1 = sexps.alloc(Sexp::List(vec![closure_id, ev1, ev1]));
    let closure_1_2 = sexps.alloc(Sexp::List(vec![closure_id, ev1, ev2]));
    let closure_2_3 = sexps.alloc(Sexp::List(vec![closure_id, ev2, ev3]));
    let closure_1_3 = sexps.alloc(Sexp::List(vec![closure_id, ev1, ev3]));

    let exp = compile_exp(exp, &[ev1, ev2], typedefs, exps, sexps, symtab, compiled)?;
    let subset = sexps.alloc(Sexp::List(vec![sexps.implies, exp, closure_1_2]));
    let subset = sexps.alloc_multi_forall_sexp(&[(ev1, sexps.event), (ev2, sexps.event)], subset);
    compiled.push(sexps.alloc(Sexp::List(vec![sexps.assert, subset])));

    let transitive = sexps.alloc(Sexp::List(vec![sexps.and, closure_1_2, closure_2_3]));
    let transitive = sexps.alloc(Sexp::List(vec![sexps.implies, transitive, closure_1_3]));
    let transitive =
        sexps.alloc_multi_forall_sexp(&[(ev1, sexps.event), (ev2, sexps.event), (ev3, sexps.event)], transitive);
    compiled.push(sexps.alloc(Sexp::List(vec![sexps.assert, transitive])));

    let mut app = vec![closure_id];
    app.extend_from_slice(evs);
    let app = sexps.alloc(Sexp::List(app));

    if reflexive {
        let reflexive = sexps.alloc_multi_forall_sexp(&[(ev1, sexps.event)], closure_1_1);
        compiled.push(sexps.alloc(Sexp::List(vec![sexps.assert, reflexive])));
        Ok(app)
    } else {
        Ok(app)
    }
}

pub fn compile_let_annot(
    ret_ty: &TyAnnot,
    sexps: &mut SexpArena,
    forall_args: &mut Vec<SexpId>,
    compiled_params: &mut Vec<SexpId>,
) -> Result<SexpId, Error> {
    match ret_ty {
        // Assume unannoted top-level letbindings are for relations
        None => {
            compiled_params.push(sexps.event);
            compiled_params.push(sexps.event);
            forall_args.push(sexps.ev1);
            forall_args.push(sexps.ev2);
            Ok(sexps.bool_ty)
        }

        _ => Ok(sexps.bool_ty),
    }
}

pub fn compile_check(
    check: Check,
    exp: ExpId,
    typedefs: Typedefs,
    exps: &ExpArena,
    sexps: &mut SexpArena,
    symtab: &mut Symtab,
    compiled: &mut Vec<SexpId>,
) -> Result<SexpId, Error> {
    Ok(match check {
        Check::Empty => {
            let exp = compile_exp(&exps[exp], &[sexps.ev1, sexps.ev2], typedefs, exps, sexps, symtab, compiled)?;
            let not_exp = sexps.alloc(Sexp::List(vec![sexps.not, exp]));
            sexps.alloc_multi_forall_sexp(&[(sexps.ev1, sexps.event), (sexps.ev2, sexps.event)], not_exp)
        }

        Check::NonEmpty => {
            let ev1 = sexps.alloc(Sexp::Event(fresh()));
            let ev2 = sexps.alloc(Sexp::Event(fresh()));
            compiled.push(sexps.alloc(Sexp::List(vec![sexps.declare_const, ev1, sexps.event])));
            compiled.push(sexps.alloc(Sexp::List(vec![sexps.declare_const, ev2, sexps.event])));

            compile_exp(&exps[exp], &[ev1, ev2], typedefs, exps, sexps, symtab, compiled)?
        }

        Check::Irreflexive => {
            let exp = compile_exp(&exps[exp], &[sexps.ev1, sexps.ev1], typedefs, exps, sexps, symtab, compiled)?;
            let not_exp = sexps.alloc(Sexp::List(vec![sexps.not, exp]));
            sexps.alloc_multi_forall_sexp(&[(sexps.ev1, sexps.event)], not_exp)
        }

        Check::NonIrreflexive => {
            let ev = sexps.alloc(Sexp::Event(fresh()));
            compiled.push(sexps.alloc(Sexp::List(vec![sexps.declare_const, ev, sexps.event])));

            compile_exp(&exps[exp], &[ev, ev], typedefs, exps, sexps, symtab, compiled)?
        }

        Check::Acyclic => {
            let trancl =
                compile_closure(false, &exps[exp], &[sexps.ev1, sexps.ev1], typedefs, exps, sexps, symtab, compiled)?;
            let not_trancl = sexps.alloc(Sexp::List(vec![sexps.not, trancl]));
            sexps.alloc_multi_forall_sexp(&[(sexps.ev1, sexps.event)], not_trancl)
        }

        Check::NonAcyclic => {
            let ev = sexps.alloc(Sexp::Event(fresh()));
            compiled.push(sexps.alloc(Sexp::List(vec![sexps.declare_const, ev, sexps.event])));

            compile_closure(false, &exps[exp], &[ev, ev], typedefs, exps, sexps, symtab, compiled)?
        }
    })
}

pub fn compile_def(
    def: &Spanned<Def>,
    typedefs: Typedefs,
    exps: &ExpArena,
    sexps: &mut SexpArena,
    symtab: &mut Symtab,
    compiled: &mut Vec<SexpId>,
) -> Result<(), Error> {
    match &def.node {
        Def::Let(f, extra_params, annot, body) => {
            let f = sexps.alloc(Sexp::Atom(*f));

            let mut param_types = Vec::new();
            let mut params = Vec::new();

            for (n, tyannot) in extra_params {
                params.push(sexps.alloc(Sexp::Atom(*n)));
                param_types.push(compile_tyannot(tyannot, typedefs, exps, sexps, symtab)?)
            }
            let return_type = compile_let_annot(annot, sexps, &mut params, &mut param_types)?;

            let declaration = if param_types.is_empty() {
                sexps.alloc(Sexp::List(vec![sexps.declare_const, f, return_type]))
            } else {
                let arg_types = sexps.alloc(Sexp::List(param_types.clone()));
                sexps.alloc(Sexp::List(vec![sexps.declare_fun, f, arg_types, return_type]))
            };
            compiled.push(declaration);

            let exp = compile_exp(&exps[*body], &params, typedefs, exps, sexps, symtab, compiled)?;

            let constraint = if params.is_empty() {
                sexps.alloc(Sexp::List(vec![sexps.eq, f, exp]))
            } else {
                let mut args = Vec::new();
                for (x, ty) in params.iter().zip(param_types.iter()) {
                    args.push(sexps.alloc(Sexp::List(vec![*x, *ty])))
                }
                let args = sexps.alloc(Sexp::List(args));

                let mut funcall = vec![f];
                funcall.extend_from_slice(&params);
                let funcall = sexps.alloc(Sexp::List(funcall));

                let constraint = sexps.alloc(Sexp::List(vec![sexps.eq, funcall, exp]));

                sexps.alloc(Sexp::List(vec![sexps.forall, args, constraint]))
            };

            let assert = sexps.alloc(Sexp::List(vec![sexps.assert, constraint]));
            compiled.push(assert);
            Ok(())
        }

        Def::Assert(constraint) => {
            let constraint = compile_exp(&exps[*constraint], &[], typedefs, exps, sexps, symtab, compiled)?;
            let assert = sexps.alloc(Sexp::List(vec![sexps.assert, constraint]));
            compiled.push(assert);
            Ok(())
        }

        Def::Flag(check, exp, as_name) => {
            let constraint = compile_check(*check, *exp, typedefs, exps, sexps, symtab, compiled)?;

            let as_name = sexps.alloc(Sexp::Atom(*as_name));
            compiled.push(sexps.alloc(Sexp::List(vec![sexps.define_const, as_name, sexps.bool_ty, constraint])));
            Ok(())
        }

        Def::Check(check, exp, as_name) => {
            let constraint = compile_check(*check, *exp, typedefs, exps, sexps, symtab, compiled)?;

            let as_name = sexps.alloc(Sexp::Atom(*as_name));
            let named_constraint = sexps.alloc(Sexp::List(vec![sexps.exclamation, constraint, sexps.named, as_name]));
            let assert = sexps.alloc(Sexp::List(vec![sexps.assert, named_constraint]));
            compiled.push(assert);
            Ok(())
        }

        Def::Declare(f, tys, ret_ty) => {
            let f = sexps.alloc(Sexp::Atom(*f));

            let mut compiled_tys = Vec::new();
            for ty in tys {
                compiled_tys.push(compile_type(&exps[*ty], typedefs, exps, sexps, symtab)?)
            }
            let ret_ty = compile_type(&exps[*ret_ty], typedefs, exps, sexps, symtab)?;

            if tys.is_empty() {
                compiled.push(sexps.alloc(Sexp::List(vec![sexps.declare_const, f, ret_ty])))
            } else {
                let tys = sexps.alloc(Sexp::List(compiled_tys));
                compiled.push(sexps.alloc(Sexp::List(vec![sexps.declare_fun, f, tys, ret_ty])))
            }
            Ok(())
        }

        Def::Define(f, params, ret_ty, body) => {
            let f = sexps.alloc(Sexp::Atom(*f));

            let mut compiled_params = Vec::new();
            for (name, ty) in params {
                let ty = compile_type(&exps[*ty], typedefs, exps, sexps, symtab)?;
                let name = sexps.alloc(Sexp::Atom(*name));
                compiled_params.push(sexps.alloc(Sexp::List(vec![name, ty])))
            }
            let ret_ty = compile_type(&exps[*ret_ty], typedefs, exps, sexps, symtab)?;

            let exp = compile_exp(&exps[*body], &[], typedefs, exps, sexps, symtab, compiled)?;

            if params.is_empty() {
                compiled.push(sexps.alloc(Sexp::List(vec![sexps.define_const, f, ret_ty, exp])))
            } else {
                let params = sexps.alloc(Sexp::List(compiled_params));
                compiled.push(sexps.alloc(Sexp::List(vec![sexps.define_fun, f, params, ret_ty, exp])))
            }
            Ok(())
        }

        // `variant x y z` gets compiled to a set of Bool consts elsewhere
        Def::Variants(_) => Ok(()),

        Def::Relation(_, _) | Def::Show(_) => Ok(()),

        Def::Accessor(..) => Ok(()),

        Def::IndexedAccessor(..) => Ok(()),

        Def::Enum(..) => Ok(()),

        Def::Index(_) => Ok(()),

        Def::Include(_) => panic!("include statement should be removed before compilation to SMT"),
    }
}

pub fn compile_variants(
    mm: &MemoryModel,
    model_variants: &Vec<String>,
    sexps: &mut SexpArena,
    symtab: &mut Symtab,
    compiled: &mut Vec<SexpId>,
) -> Result<(), Error> {
    let variants = mm.variants();

    let mut seen: BTreeSet<Name> = BTreeSet::new();

    for v in model_variants {
        let vname = symtab.intern(v);
        let vid = sexps.alloc(Sexp::Atom(vname));
        compiled.push(sexps.alloc(Sexp::List(vec![sexps.define_const, vid, sexps.bool_ty, sexps.bool_true])));
        seen.insert(vname);
    }

    for v in variants {
        if !seen.contains(v) {
            let vid = sexps.alloc(Sexp::Atom(*v));
            compiled.push(sexps.alloc(Sexp::List(vec![sexps.define_const, vid, sexps.bool_ty, sexps.bool_false])))
        }
    }

    Ok(())
}

pub fn compile_memory_model(
    mm: &MemoryModel,
    typedefs: Typedefs,
    exps: &ExpArena,
    model_variants: &Vec<String>,
    sexps: &mut SexpArena,
    symtab: &mut Symtab,
    compiled: &mut Vec<SexpId>,
) -> Result<(), Error> {
    compile_variants(mm, model_variants, sexps, symtab, compiled)?;

    for def in mm.defs.iter() {
        compile_def(def, typedefs, exps, sexps, symtab, compiled)?
    }
    Ok(())
}
