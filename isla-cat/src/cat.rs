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

//! Provides the top-level interface for interacting with cats. 🐱

use std::collections::{HashMap, HashSet};
use std::env;
use std::error;
use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::path::{Path, PathBuf};

use crate::cat_lexer;
use crate::cat_parser;

#[derive(Debug)]
pub enum Exp<T> {
    Empty(T),
    Id(String, T),
    Let(String, Box<Exp<T>>, Box<Exp<T>>, T),
    TryWith(Box<Exp<T>>, Box<Exp<T>>, T),
    /// Set or relation union R | S
    Union(Box<Exp<T>>, Box<Exp<T>>, T),
    /// Set or relation intersection R & S
    Inter(Box<Exp<T>>, Box<Exp<T>>, T),
    /// Set or relation difference R \ S
    Diff(Box<Exp<T>>, Box<Exp<T>>, T),
    /// Relation composition R; S
    Seq(Box<Exp<T>>, Box<Exp<T>>),
    /// Cartesian product of sets R * S
    Cartesian(Box<Exp<T>>, Box<Exp<T>>),
    /// Set or relation complement ~R
    Compl(Box<Exp<T>>, T),
    /// \[R\] Lift a set to the identity relation over its elements
    Identity(Box<Exp<T>>),
    /// R? intersect a relation R with the identity relation
    IdentityUnion(Box<Exp<T>>),
    /// Inverse of a relation R^-1
    Inverse(Box<Exp<T>>),
    /// Function application f(x)
    App(String, Box<Exp<T>>, T),
}

/// Cat allows arbitrary variable shadowing, so we have to deal with
/// it sadly.
#[derive(Debug, Default)]
pub struct Shadows {
    map: HashMap<String, usize>,
}

impl Shadows {
    pub fn new() -> Self {
        Default::default()
    }
}

impl<T> Exp<T> {
    fn unshadow(&mut self, shadows: &mut Shadows, locals: &mut HashMap<String, usize>) {
        use Exp::*;

        match self {
            Id(id, _) => {
                if let Some(count) = locals.get(id) {
                    *id = format!("{}/l{}", id, count)
                } else if let Some(count) = shadows.map.get(id) {
                    *id = format!("{}/{}", id, count)
                }
            }

            Let(id, exp1, exp2, _) => {
                exp1.unshadow(shadows, locals);
                if let Some(count) = locals.get_mut(id) {
                    *count += 1;
                    *id = format!("{}/l{}", id, count)
                } else {
                    locals.insert(id.clone(), 0);
                    *id = format!("{}/l0", id)
                }
                exp2.unshadow(shadows, locals)
            }

            Empty(_) => (),
            Inverse(exp) | IdentityUnion(exp) | Identity(exp) | Compl(exp, _) | App(_, exp, _) => {
                exp.unshadow(shadows, locals)
            }
            TryWith(exp1, exp2, _)
            | Union(exp1, exp2, _)
            | Inter(exp1, exp2, _)
            | Diff(exp1, exp2, _)
            | Seq(exp1, exp2)
            | Cartesian(exp1, exp2) => {
                exp1.unshadow(shadows, locals);
                exp2.unshadow(shadows, locals)
            }
        }
    }
}

#[derive(Debug)]
pub enum Check {
    Acyclic,
    Irreflexive,
    Empty,
    NonAcyclic,
    NonIrreflexive,
    NonEmpty,
}

#[derive(Debug)]
pub enum Def<T> {
    Let(Vec<(String, Exp<T>)>),
    Fn(String, Vec<(String, T)>, Exp<T>),
    TClosure(String, Exp<T>),
    RTClosure(String, Exp<T>),
    Flag(Check, Exp<T>, String),
    Check(Check, Exp<T>, Option<String>),
    Show(Vec<String>),
    ShowAs(Exp<T>, String),
    Unshow(Vec<String>),
    Set(String),
    Relation(String),
}

#[derive(Debug)]
pub enum ParseDef {
    Def(Def<()>),
    Include(String),
}

/// A `ParseCat` represents a single parsed cat file.
#[derive(Debug)]
pub struct ParseCat {
    pub tag: String,
    pub defs: Vec<ParseDef>,
}

impl ParseCat {
    pub fn from_string(contents: &str) -> Result<Self, String> {
        let lexer = cat_lexer::Lexer::new(contents);
        match cat_parser::CatParser::new().parse(lexer) {
            Ok(cat) => Ok(cat),
            Err(e) => Err(format!("Failed to parse cat file: {}", e)),
        }
    }

    pub fn from_file<P>(path: P) -> Result<Self, String>
    where
        P: AsRef<Path>,
    {
        let file_name = path.as_ref().display();
        let mut contents = String::new();

        match File::open(&path) {
            Ok(mut handle) => match handle.read_to_string(&mut contents) {
                Ok(_) => (),
                Err(e) => return Err(format!("Error when reading cat file '{}': {}", file_name, e)),
            },
            Err(e) => return Err(format!("Error when opening cat file '{}': {}", file_name, e)),
        }

        Self::from_string(&contents)
    }
}

/// A `Cat` is a full cat memory-model definition, with all its
/// includes resolved.
#[derive(Debug)]
pub struct Cat<T> {
    pub tag: String,
    pub defs: Vec<Def<T>>,
}

impl<T> Cat<T> {
    /// Remove all variable shadowing
    pub fn unshadow(&mut self, shadows: &mut Shadows) {
        use Def::*;

        for def in self.defs.iter_mut().rev() {
            match def {
                Let(bindings) => {
                    for (id, exp) in bindings.iter_mut() {
                        exp.unshadow(shadows, &mut HashMap::new());
                        if let Some(count) = shadows.map.get_mut(id) {
                            *id = format!("{}/{}", id, count);
                            *count += 1
                        } else {
                            shadows.map.insert(id.clone(), 0);
                        }
                    }
                }

                TClosure(id, exp) | RTClosure(id, exp) => {
                    exp.unshadow(shadows, &mut HashMap::new());
                    if let Some(count) = shadows.map.get_mut(id) {
                        *id = format!("{}/{}", id, count);
                        *count += 1
                    } else {
                        shadows.map.insert(id.clone(), 0);
                    }
                }

                Fn(_, _, exp) | Flag(_, exp, _) | Check(_, exp, _) | ShowAs(exp, _) => {
                    exp.unshadow(shadows, &mut HashMap::new())
                }

                _ => (),
            }
        }
    }

    pub fn shows(&self) -> Vec<String> {
        let mut shows = Vec::new();
        for def in self.defs.iter() {
            match def {
                Def::Show(ids) => shows.append(&mut ids.clone()),
                Def::ShowAs(_, id) => shows.push(id.clone()),
                _ => (),
            }
        }
        shows
    }
}

impl Cat<Ty> {
    /// Returns the names of all the relations defined by a cat file
    pub fn relations<'a>(&'a self) -> Vec<&'a str> {
        let mut rels: Vec<&'a str> = Vec::new();
        for def in self.defs.iter() {
            match def {
                Def::Let(bindings) => bindings.iter().for_each(|(id, exp)| {
                    if ty_of(exp) == Ty::Rel {
                        rels.push(id)
                    }
                }),
                Def::TClosure(id, _) | Def::RTClosure(id, _) | Def::Relation(id) => rels.push(id),
                _ => (),
            }
        }
        rels
    }
}

/// Turn a `ParseCat` into an full untyped Cat by resolving any
/// include statements. Note that some included cats are very special,
/// like `cos.cat` and `stdlib.cat` which are defined internally.
pub fn resolve_includes(cat_dirs: &[PathBuf], mut parse_cat: ParseCat) -> Result<Cat<()>, String> {
    Ok(Cat {
        tag: parse_cat.tag,
        defs: parse_cat
            .defs
            .drain(..)
            .map(|parse_def| match parse_def {
                ParseDef::Def(def) => Ok(vec![def]),
                ParseDef::Include(name) => find_cat(cat_dirs, &name).map(|cat| cat.defs),
            })
            .collect::<Result<Vec<_>, _>>()?
            .drain(..)
            .flatten()
            .collect(),
    })
}

static COS_CAT: &str = include_str!("../catlib/cos.cat");
static STDLIB_CAT: &str = include_str!("../catlib/stdlib.cat");

fn find_cat(cat_dirs: &[PathBuf], name: &str) -> Result<Cat<()>, String> {
    if name == "cos.cat" {
        let parse_cat = ParseCat::from_string(COS_CAT)?;
        return resolve_includes(cat_dirs, parse_cat);
    }

    if name == "stdlib.cat" {
        let parse_cat = ParseCat::from_string(STDLIB_CAT)?;
        return resolve_includes(cat_dirs, parse_cat);
    }

    for dir in cat_dirs {
        let cat_file = dir.join(name);
        if cat_file.is_file() {
            let parse_cat = ParseCat::from_file(cat_file)?;
            return resolve_includes(cat_dirs, parse_cat);
        }
    }

    Err(format!("Could not find cat: {}", name))
}

/// Load a cat model. The input can either be a path to the cat model such as
/// `my/favourite/cats/russian_blue.cat`, or the name of a cat like `british_shorthair.cat`. In the
/// first case any cats included by `russian_blue.cat` will be searched for first in
/// `my/favourite/cats/` followed by the HERDLIB environment variable (if set). In the second case
/// they will just be searched for in HERDLIB.
pub fn load_cat(name: &str) -> Result<Cat<()>, String> {
    let path = Path::new(name);

    let mut cat_dirs: Vec<PathBuf> = Vec::new();

    if let Ok(directory) = env::var("HERDLIB") {
        cat_dirs.push(directory.into())
    }

    let mut directory = path.to_path_buf();
    directory.pop();
    if directory.is_dir() {
        cat_dirs.push(directory)
    }

    if path.is_file() {
        let parse_cat = ParseCat::from_file(path)?;
        resolve_includes(&cat_dirs, parse_cat)
    } else {
        find_cat(&cat_dirs, name)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Rel,
    Set,
}

/// A type-checking context. For cats.
pub struct Tcx {
    bindings: HashMap<String, Vec<Ty>>,
    functions: HashMap<String, (Ty, Ty)>,
    unknowns: HashSet<String>,
    found: HashMap<String, Ty>,
}

impl Tcx {
    fn push<S: Into<String>>(&mut self, name: S, ty: Ty) {
        let name = name.into();
        match self.bindings.get_mut(&name) {
            None => {
                self.bindings.insert(name, vec![ty]);
            }
            Some(tys) => tys.push(ty),
        }
    }

    fn pop(&mut self, name: &str) {
        match self.bindings.get_mut(name) {
            None => (),
            Some(tys) => {
                tys.pop();
            }
        }
    }

    fn peek(&self, name: &str) -> Option<Ty> {
        match self.bindings.get(name) {
            None => None,
            Some(tys) => tys.last().copied(),
        }
    }
}

/// The initial typing context for cats. A iterator of architecture
/// specific sets can be provided to this function. This will usually
/// include the set of fences in the architecture.
pub fn initial_tcx<I>(sets: I) -> Tcx
where
    I: Iterator<Item = String>,
{
    let mut bindings = HashMap::new();
    let mut functions = HashMap::new();

    // Architecture specific sets
    for set in sets {
        bindings.insert(set, vec![Ty::Set]);
    }

    functions.insert("domain".to_string(), (Ty::Rel, Ty::Set));
    functions.insert("range".to_string(), (Ty::Rel, Ty::Set));
    functions.insert("fencerel".to_string(), (Ty::Set, Ty::Rel));
    functions.insert("ctrlcfence".to_string(), (Ty::Set, Ty::Rel));

    Tcx { bindings, functions, unknowns: HashSet::new(), found: HashMap::new() }
}

/// For badly-typed cats.
#[derive(Debug)]
pub struct TyError {
    message: String,
}

impl fmt::Display for TyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl error::Error for TyError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

fn ty_error<S: Into<String>, A>(message: S) -> Result<A, TyError> {
    Err(TyError { message: message.into() })
}

/// Returns the type of a cat expression.
pub fn ty_of(exp: &Exp<Ty>) -> Ty {
    use Exp::*;
    match exp {
        Empty(ty) => *ty,
        Id(_, ty) => *ty,
        Let(_, _, _, ty) => *ty,
        TryWith(_, _, ty) => *ty,
        Union(_, _, ty) => *ty,
        Inter(_, _, ty) => *ty,
        Diff(_, _, ty) => *ty,
        Seq(_, _) => Ty::Rel,
        Cartesian(_, _) => Ty::Rel,
        Compl(_, ty) => *ty,
        Identity(_) => Ty::Rel,
        IdentityUnion(_) => Ty::Rel,
        Inverse(_) => Ty::Rel,
        App(_, _, ty) => *ty,
    }
}

fn check_exp(tcx: &mut Tcx, exp: &Exp<()>, ty: Ty) -> Result<Exp<Ty>, TyError> {
    use Exp::*;
    match exp {
        Empty(()) => Ok(Empty(ty)),

        Id(id, ()) if tcx.unknowns.contains(id) => {
            match tcx.found.insert(id.clone(), ty) {
                Some(prev_ty) if ty != prev_ty => return ty_error(format!("Inconsistent type for {}", id)),
                _ => (),
            }
            Ok(Id(id.clone(), ty))
        }

        _ => {
            let exp = infer_exp(tcx, exp)?;
            if ty == ty_of(&exp) {
                Ok(exp)
            } else {
                ty_error("Types do not match")
            }
        }
    }
}

macro_rules! unary_infer {
    ($tcx: ident, $ctor: path, $x: ident) => {{
        let x = infer_exp($tcx, $x)?;
        let ty = ty_of(&x);
        Ok($ctor(Box::new(x), ty))
    }};
}

macro_rules! binary_infer {
    ($tcx: ident, $ctor: path, $x: ident, $y: ident) => {{
        match infer_exp($tcx, $x) {
            Ok(x) => {
                let y = check_exp($tcx, $y, ty_of(&x))?;
                if ty_of(&x) == ty_of(&y) {
                    let ty = ty_of(&x);
                    Ok($ctor(Box::new(x), Box::new(y), ty))
                } else {
                    ty_error("Types do not match")
                }
            }
            Err(_) => {
                let y = infer_exp($tcx, $y)?;
                let x = check_exp($tcx, $x, ty_of(&y))?;
                if ty_of(&x) == ty_of(&y) {
                    let ty = ty_of(&x);
                    Ok($ctor(Box::new(x), Box::new(y), ty))
                } else {
                    ty_error("Types do not match")
                }
            }
        }
    }};
}

fn infer_exp(tcx: &mut Tcx, exp: &Exp<()>) -> Result<Exp<Ty>, TyError> {
    use Exp::*;
    match exp {
        Empty(()) => ty_error("Cannot infer the type of an empty relation or set"),

        Id(id, ()) => match tcx.peek(id) {
            Some(ty) => Ok(Id(id.clone(), ty)),
            None => ty_error(format!("Identifier {} not defined", id)),
        },

        Let(v, x, y, ()) => {
            let x = infer_exp(tcx, x)?;
            tcx.push(v, ty_of(&x));
            let y = infer_exp(tcx, y)?;
            tcx.pop(v);
            let ty = ty_of(&y);
            Ok(Let(v.clone(), Box::new(x), Box::new(y), ty))
        }

        TryWith(x, y, ()) => match infer_exp(tcx, x) {
            Ok(x) => {
                let y = check_exp(tcx, y, ty_of(&x))?;
                if ty_of(&x) == ty_of(&y) {
                    let ty = ty_of(&x);
                    Ok(TryWith(Box::new(x), Box::new(y), ty))
                } else {
                    ty_error("Types do not mach in try with")
                }
            }
            Err(_) => {
                let y = infer_exp(tcx, y)?;
                match check_exp(tcx, x, ty_of(&y)) {
                    Ok(x) => {
                        if ty_of(&x) == ty_of(&y) {
                            let ty = ty_of(&x);
                            Ok(TryWith(Box::new(x), Box::new(y), ty))
                        } else {
                            ty_error("Types do not match in try with")
                        }
                    }
                    Err(_) => Ok(y),
                }
            }
        },

        Union(x, y, ()) => binary_infer!(tcx, Union, x, y),
        Inter(x, y, ()) => binary_infer!(tcx, Inter, x, y),
        Diff(x, y, ()) => binary_infer!(tcx, Diff, x, y),

        Seq(x, y) => {
            let x = check_exp(tcx, x, Ty::Rel)?;
            let y = check_exp(tcx, y, Ty::Rel)?;
            Ok(Seq(Box::new(x), Box::new(y)))
        }

        Cartesian(x, y) => {
            let x = check_exp(tcx, x, Ty::Set)?;
            let y = check_exp(tcx, y, Ty::Set)?;
            Ok(Cartesian(Box::new(x), Box::new(y)))
        }

        Compl(x, ()) => unary_infer!(tcx, Compl, x),

        Identity(x) => {
            let x = check_exp(tcx, x, Ty::Set)?;
            Ok(Identity(Box::new(x)))
        }

        IdentityUnion(x) => {
            let x = check_exp(tcx, x, Ty::Rel)?;
            Ok(IdentityUnion(Box::new(x)))
        }

        Inverse(x) => {
            let x = check_exp(tcx, x, Ty::Rel)?;
            Ok(Inverse(Box::new(x)))
        }

        App(f, x, ()) => {
            let (from_ty, to_ty) = match tcx.functions.get(f) {
                Some(f_ty) => *f_ty,
                None => return ty_error(format!("Function {} not defined", f)),
            };
            let x = check_exp(tcx, x, from_ty)?;
            Ok(App(f.clone(), Box::new(x), to_ty))
        }
    }
}

fn infer_def(tcx: &mut Tcx, def: Def<()>) -> Result<Def<Ty>, TyError> {
    use Def::*;
    Ok(match def {
        Set(name) => {
            tcx.push(name.clone(), Ty::Set);
            Set(name)
        }

        Relation(name) => {
            tcx.push(name.clone(), Ty::Rel);
            Relation(name)
        }

        Let(mut bindings) => {
            let bindings: Vec<(String, Exp<Ty>)> = bindings
                .drain(..)
                .map(|(name, exp)| match infer_exp(tcx, &exp) {
                    Ok(exp) => Ok((name, exp)),
                    Err(e) => Err(e),
                })
                .collect::<Result<_, _>>()?;

            tcx.unknowns.clear();
            tcx.found.clear();

            for (name, exp) in &bindings {
                tcx.push(name, ty_of(exp));
            }

            Let(bindings)
        }

        Fn(name, mut params, body) => {
            for (param, _) in &params {
                tcx.unknowns.insert(param.clone());
            }

            let body = infer_exp(tcx, &body)?;

            let params: Vec<(String, Ty)> = params
                .drain(..)
                .map(|(param, _)| {
                    if let Some(ty) = tcx.found.get(&param) {
                        Ok((param, *ty))
                    } else {
                        ty_error(format!("Could not infer type of function parameter {}", param))
                    }
                })
                .collect::<Result<_, _>>()?;

            tcx.unknowns.clear();
            tcx.found.clear();

            Fn(name, params, body)
        }

        TClosure(id, exp) => {
            let def = TClosure(id.clone(), check_exp(tcx, &exp, Ty::Rel)?);
            tcx.push(id, Ty::Rel);
            def
        }

        RTClosure(id, exp) => {
            let def = RTClosure(id.clone(), check_exp(tcx, &exp, Ty::Rel)?);
            tcx.push(id, Ty::Rel);
            def
        }

        Flag(check, exp, id) => Flag(check, infer_exp(tcx, &exp)?, id),

        Check(check, exp, opt_id) => Check(check, infer_exp(tcx, &exp)?, opt_id),

        Show(ids) => Show(ids),

        ShowAs(exp, id) => ShowAs(check_exp(tcx, &exp, Ty::Rel)?, id),

        Unshow(ids) => Unshow(ids),
    })
}

/// Infer all the types within a cat.
pub fn infer_cat(tcx: &mut Tcx, mut cat: Cat<()>) -> Result<Cat<Ty>, TyError> {
    Ok(Cat { tag: cat.tag, defs: cat.defs.drain(..).map(|def| infer_def(tcx, def)).collect::<Result<_, _>>()? })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_local_shadowing() {
        use Exp::*;
        let x = "x".to_string();
        let mut exp = Let(
            x.clone(),
            Box::new(Id(x.clone(), ())),
            Box::new(Let(x.clone(), Box::new(Id(x.clone(), ())), Box::new(Id(x.clone(), ())), ())),
            (),
        );
        exp.unshadow(&mut Shadows::new(), &mut HashMap::new());
        assert_eq!(
            "Let(\"x/l0\", Id(\"x\", ()), Let(\"x/l1\", Id(\"x/l0\", ()), Id(\"x/l1\", ()), ()), ())",
            &format!("{:?}", exp)
        )
    }
}
