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
use std::io::Write;
use std::ops::Index;
use std::sync::atomic::{AtomicU32, Ordering};

use isla_lib::simplify::write_bits;

use crate::ast::{Binary, Def, Error, Exp, ExpArena, ExpId, MemoryModel, Name, Spanned, Symtab, TyAnnot, Unary};

/// Event ids are `u32` variables denoted in the generated SMTLIB as
/// `evX` where X is a number greater than 0. The arguments to
/// toplevel relations and sets are always `ev1` and `ev2`.
pub type EventId = u32;

static FRESH_COUNTER: AtomicU32 = AtomicU32::new(3);

fn fresh() -> EventId {
    FRESH_COUNTER.fetch_add(1, Ordering::SeqCst)
}

pub type SexpId = Id<Sexp>;

pub enum Sexp {
    Atom(Name),
    Event(EventId),
    Bits(Vec<bool>),
    List(Vec<SexpId>),
}

pub struct SexpArena {
    arena: Arena<Sexp>,
    pub declare_const: SexpId,
    pub declare_fun: SexpId,
    pub assert: SexpId,
    pub bool_true: SexpId,
    pub bool_false: SexpId,
    pub and: SexpId,
    pub or: SexpId,
    pub not: SexpId,
    pub forall: SexpId,
    pub exists: SexpId,
    pub event: SexpId,
    pub eq: SexpId,
    pub letbind: SexpId,
    pub bool_ty: SexpId,
    pub implies: SexpId,
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
        use crate::ast::constants::*;

        let mut arena = Arena::new();

        let declare_const = arena.alloc(Sexp::Atom(DECLARE_CONST.name()));
        let declare_fun = arena.alloc(Sexp::Atom(DECLARE_FUN.name()));
        let assert = arena.alloc(Sexp::Atom(ASSERT.name()));
        let bool_true = arena.alloc(Sexp::Atom(TRUE.name()));
        let bool_false = arena.alloc(Sexp::Atom(FALSE.name()));
        let and = arena.alloc(Sexp::Atom(AND.name()));
        let or = arena.alloc(Sexp::Atom(OR.name()));
        let not = arena.alloc(Sexp::Atom(NOT.name()));
        let forall = arena.alloc(Sexp::Atom(FORALL.name()));
        let exists = arena.alloc(Sexp::Atom(EXISTS.name()));
        let event = arena.alloc(Sexp::Atom(EVENT.name()));
        let eq = arena.alloc(Sexp::Atom(EQ.name()));
        let letbind = arena.alloc(Sexp::Atom(LET.name()));
        let bool_ty = arena.alloc(Sexp::Atom(BOOL.name()));
        let implies = arena.alloc(Sexp::Atom(IMPLIES.name()));
        let ev1 = arena.alloc(Sexp::Event(1));
        let ev2 = arena.alloc(Sexp::Event(2));

        SexpArena {
            arena,
            declare_const,
            declare_fun,
            assert,
            bool_true,
            bool_false,
            and,
            or,
            not,
            forall,
            exists,
            event,
            eq,
            letbind,
            bool_ty,
            implies,
            ev1,
            ev2,
        }
    }

    fn alloc(&mut self, sexp: Sexp) -> SexpId {
        self.arena.alloc(sexp)
    }

    fn alloc_exists(&mut self, e: SexpId, sexp: Sexp) -> SexpId {
        let sexp = self.alloc(sexp);
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
}

impl Sexp {
    fn write(&self, buf: &mut dyn Write, sexps: &SexpArena, symtab: &Symtab) -> std::io::Result<()> {
        match self {
            Sexp::Atom(n) => write!(buf, "{}", symtab[*n]),
            Sexp::Event(id) => write!(buf, "ev{}", id),
            Sexp::Bits(bv) => write_bits(buf, bv),
            Sexp::List(xs) => {
                if let Some((last, rest)) = xs.split_last() {
                    write!(buf, "(")?;
                    for x in rest {
                        sexps[*x].write(buf, sexps, symtab)?;
                        write!(buf, " ")?
                    }
                    sexps[*last].write(buf, sexps, symtab)?;
                    write!(buf, ")")
                } else {
                    write!(buf, "nil")
                }
            }
        }
    }
}

pub fn write_sexps(buf: &mut dyn Write, xs: &[SexpId], sexps: &SexpArena, symtab: &Symtab) -> std::io::Result<()> {
    for x in xs {
        sexps[*x].write(buf, sexps, symtab)?;
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
        if matches!(arg, None) {
            wildcards += 1
        }
    }
    wildcards
}

pub fn compile_type(ty: &Spanned<Exp>, exps: &ExpArena, sexps: &mut SexpArena) -> Result<SexpId, Error> {
    match &ty.node {
        _ => Ok(sexps.event),
    }
}

pub fn compile_tyannot(tyannot: &TyAnnot, exps: &ExpArena, sexps: &mut SexpArena) -> Result<SexpId, Error> {
    if let Some(ty) = tyannot {
        compile_type(&exps[*ty], exps, sexps)
    } else {
        Ok(sexps.event)
    }
}

pub fn compile_exp(
    exp: &Spanned<Exp>,
    evs: &[SexpId],
    exps: &ExpArena,
    sexps: &mut SexpArena,
    symtab: &mut Symtab,
    compiled: &mut Vec<SexpId>,
) -> Result<SexpId, Error> {
    match &exp.node {
        Exp::Empty => Ok(sexps.bool_false),

        Exp::App(f, args) => {
            let wildcards = count_wildcards(args);
            if evs.len() != wildcards {
                return Err(Error {
                    message: format!(
                        "{} expected, but {} found",
                        relation_arity_name(evs.len()),
                        relation_arity_name(wildcards)
                    ),
                    span: exp.span,
                });
            }

            let mut wildcard: usize = 0;
            let mut sexp_args = Vec::new();
            for arg in args {
                if let Some(arg) = arg {
                    let sexp = compile_exp(&exps[*arg], &[], exps, sexps, symtab, compiled)?;
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

        Exp::Binary(Binary::Cartesian, x, y) => match evs {
            &[ev1, ev2] => {
                let mut xs = vec![sexps.and];
                xs.push(compile_exp(&exps[*x], &[ev1], exps, sexps, symtab, compiled)?);
                xs.push(compile_exp(&exps[*y], &[ev2], exps, sexps, symtab, compiled)?);
                Ok(sexps.alloc(Sexp::List(xs)))
            }
            _ => {
                return Err(Error {
                    message: format!(
                        "Cartesian product in a context where a {} was expected, rather than a binary relation",
                        relation_arity_name(evs.len()),
                    ),
                    span: exp.span,
                })
            }
        },

        Exp::Binary(Binary::Diff, x, y) => {
            let mut xs = vec![sexps.and];
            xs.push(compile_exp(&exps[*x], evs, exps, sexps, symtab, compiled)?);
            let y = compile_exp(&exps[*y], evs, exps, sexps, symtab, compiled)?;
            xs.push(sexps.alloc(Sexp::List(vec![sexps.not, y])));
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Binary(Binary::Union, x, y) => {
            let mut xs = vec![sexps.or];
            xs.push(compile_exp(&exps[*x], evs, exps, sexps, symtab, compiled)?);
            xs.push(compile_exp(&exps[*y], evs, exps, sexps, symtab, compiled)?);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Binary(Binary::Inter, x, y) => {
            let mut xs = vec![sexps.and];
            xs.push(compile_exp(&exps[*x], evs, exps, sexps, symtab, compiled)?);
            xs.push(compile_exp(&exps[*y], evs, exps, sexps, symtab, compiled)?);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Binary(Binary::In, x, set) => {
            if evs.is_empty() {
                let mut args = Vec::new();
                match &exps[*x].node {
                    Exp::Tuple(xs) => {
                        for x in xs {
                            args.push(compile_exp(&exps[*x], &[], exps, sexps, symtab, compiled)?)
                        }
                    }
                    _ => args.push(compile_exp(&exps[*x], &[], exps, sexps, symtab, compiled)?),
                }
                compile_exp(&exps[*set], &args, exps, sexps, symtab, compiled)
            } else {
                return Err(Error {
                    message: format!(
                        "Boolean set membership in a context where a {} was expected",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                });
            }
        }

        Exp::Binary(Binary::Seq, x, y) => match evs {
            &[ev1, ev2] => {
                let ev3 = sexps.alloc(Sexp::Event(fresh()));
                let mut xs = vec![sexps.and];
                xs.push(compile_exp(&exps[*x], &[ev1, ev3], exps, sexps, symtab, compiled)?);
                xs.push(compile_exp(&exps[*y], &[ev3, ev2], exps, sexps, symtab, compiled)?);
                Ok(sexps.alloc_exists(ev3, Sexp::List(xs)))
            }
            _ => {
                return Err(Error {
                    message: format!(
                        "Sequential composition in a context where a {} was expected, rather than a binary relation",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                })
            }
        },

        Exp::Binary(Binary::Eq, x, y) => {
            let mut xs = vec![sexps.eq];
            xs.push(compile_exp(&exps[*x], evs, exps, sexps, symtab, compiled)?);
            xs.push(compile_exp(&exps[*y], evs, exps, sexps, symtab, compiled)?);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Binary(Binary::Neq, x, y) => {
            let mut xs = vec![sexps.eq];
            xs.push(compile_exp(&exps[*x], evs, exps, sexps, symtab, compiled)?);
            xs.push(compile_exp(&exps[*y], evs, exps, sexps, symtab, compiled)?);
            let eq = sexps.alloc(Sexp::List(xs));
            Ok(sexps.alloc(Sexp::List(vec![sexps.not, eq])))
        }

        Exp::Unary(Unary::Compl, x) => {
            let mut xs = vec![sexps.not];
            xs.push(compile_exp(&exps[*x], evs, exps, sexps, symtab, compiled)?);
            Ok(sexps.alloc(Sexp::List(xs)))
        }

        Exp::Unary(Unary::Identity, x) => match evs {
            &[ev1, ev2] => {
                let mut xs = vec![sexps.and];
                xs.push(compile_exp(&exps[*x], &[ev1], exps, sexps, symtab, compiled)?);
                xs.push(compile_exp(&exps[*x], &[ev2], exps, sexps, symtab, compiled)?);
                xs.push(sexps.alloc(Sexp::List(vec![sexps.eq, ev1, ev2])));
                Ok(sexps.alloc(Sexp::List(xs)))
            }
            _ => {
                return Err(Error {
                    message: format!(
                        "Identity in a context where a {} was expected, rather than a binary relation",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                })
            }
        },

        Exp::Unary(Unary::IdentityUnion, x) => match evs {
            &[ev1, ev2] => {
                let mut xs = vec![sexps.or];
                xs.push(compile_exp(&exps[*x], &[ev1, ev2], exps, sexps, symtab, compiled)?);
                xs.push(sexps.alloc(Sexp::List(vec![sexps.eq, ev1, ev2])));
                Ok(sexps.alloc(Sexp::List(xs)))
            }
            _ => {
                return Err(Error {
                    message: format!(
                        "Union with identity in a context where a {} was expected, rather than a binary relation",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                })
            }
        },

        Exp::Unary(Unary::Inverse, x) => match evs {
            &[ev1, ev2] => compile_exp(&exps[*x], &[ev2, ev1], exps, sexps, symtab, compiled),
            _ => {
                return Err(Error {
                    message: format!(
                        "Inverse in a context where a {} was expected, rather than a binary relation",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                })
            }
        },

        Exp::Unary(closure_op @ (Unary::TClosure | Unary::RTClosure), x) => match evs {
            &[ev1, ev2] => {
                if let Unary::TClosure = closure_op {
                    compile_closure(false, &exps[*x], evs, exps, sexps, symtab, compiled)
                } else {
                    compile_closure(true, &exps[*x], evs, exps, sexps, symtab, compiled)
                }
            }
            _ => {
                return Err(Error {
                    message: format!(
                        "Closure operator in a context where a {} was expected, rather than a binary relation",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                })
            }
        },

        Exp::Set(v, _, body) => match evs {
            &[ev1] => {
                let body = compile_exp(&exps[*body], &[], exps, sexps, symtab, compiled)?;
                Ok(sexps.alloc_letbind(&[(*v, ev1)], body))
            }
            _ => {
                return Err(Error {
                    message: format!(
                        "Explicit set in a context where a {} was expected",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                })
            }
        },

        Exp::Relation(v1, _, v2, _, body) => match evs {
            &[ev1, ev2] => {
                let body = compile_exp(&exps[*body], &[], exps, sexps, symtab, compiled)?;
                Ok(sexps.alloc_letbind(&[(*v1, ev1), (*v2, ev2)], body))
            }
            _ => {
                return Err(Error {
                    message: format!(
                        "Explicit relation in a context where a {} was expected",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                })
            }
        },

        Exp::Forall(args, body) => {
            if evs.is_empty() {
                let body = compile_exp(&exps[*body], &[], exps, sexps, symtab, compiled)?;
                let mut compiled_args = Vec::new();
                for (n, tyannot) in args {
                    compiled_args.push((*n, compile_tyannot(tyannot, exps, sexps)?))
                }
                Ok(sexps.alloc_multi_forall(&compiled_args, body))
            } else {
                return Err(Error {
                    message: format!(
                        "Universal quantifier in a context where a {} was expected",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                });
            }
        }

        Exp::Exists(args, body) => {
            if evs.is_empty() {
                let body = compile_exp(&exps[*body], &[], exps, sexps, symtab, compiled)?;
                let mut compiled_args = Vec::new();
                for (n, tyannot) in args {
                    compiled_args.push((*n, compile_tyannot(tyannot, exps, sexps)?))
                }
                Ok(sexps.alloc_multi_exists(&compiled_args, body))
            } else {
                return Err(Error {
                    message: format!(
                        "Existential quantifier in a context where a {} was expected",
                        relation_arity_name(evs.len())
                    ),
                    span: exp.span,
                });
            }
        }

        Exp::Accessor(exp, accs) => {
            let exp = compile_exp(&exps[*exp], &[], exps, sexps, symtab, compiled)?;
            let accessor_function = sexps.alloc(Sexp::Atom(symtab.encode_accessors(accs)));
            Ok(sexps.alloc(Sexp::List(vec![accessor_function, exp])))
        }

        Exp::Tuple(_) => Err(Error { message: "Unexpected tuple".to_string(), span: exp.span }),
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

    let exp = compile_exp(exp, &[ev1, ev2], exps, sexps, symtab, compiled)?;
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

pub fn compile_def(
    def: &Spanned<Def>,
    exps: &ExpArena,
    sexps: &mut SexpArena,
    symtab: &mut Symtab,
    compiled: &mut Vec<SexpId>,
) -> Result<(), Error> {
    match &def.node {
        Def::Let(f, params, annot, body) => {
            let f = sexps.alloc(Sexp::Atom(*f));

            let mut param_types = Vec::new();
            let mut params = Vec::new();
            let return_type = compile_let_annot(annot, sexps, &mut params, &mut param_types)?;
            let declaration = if param_types.is_empty() {
                sexps.alloc(Sexp::List(vec![sexps.declare_const, f, return_type]))
            } else {
                let arg_types = sexps.alloc(Sexp::List(param_types.clone()));
                sexps.alloc(Sexp::List(vec![sexps.declare_fun, f, arg_types, return_type]))
            };
            compiled.push(declaration);

            let exp = compile_exp(&exps[*body], &params, exps, sexps, symtab, compiled)?;

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
            let constraint = compile_exp(&exps[*constraint], &[], exps, sexps, symtab, compiled)?;
            let assert = sexps.alloc(Sexp::List(vec![sexps.assert, constraint]));
            compiled.push(assert);
            Ok(())
        }

        Def::Check(check, exp, as_name) => Ok(()),
    }
}

pub fn compile_memory_model(
    mm: &MemoryModel,
    exps: &ExpArena,
    sexps: &mut SexpArena,
    symtab: &mut Symtab,
    compiled: &mut Vec<SexpId>,
) -> Result<(), Error> {
    for def in mm.defs.iter() {
        compile_def(def, exps, sexps, symtab, compiled)?
    }
    Ok(())
}
