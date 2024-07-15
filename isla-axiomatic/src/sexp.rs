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

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;

use isla_lib::bitvector::{b64::B64, BV};

#[derive(Debug, Clone)]
pub enum Sexp<'s> {
    Atom(&'s str),
    I128(i128),
    Bits(&'s str),
    List(Vec<Sexp<'s>>),
}

impl<'s> fmt::Display for Sexp<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Sexp::*;
        match self {
            Atom(s) => write!(f, "{}", s),
            I128(i) => write!(f, "{}", i),
            Bits(b) => write!(f, "{}", b),
            List(xs) => {
                write!(f, "(")?;
                let mut first = true;
                for x in xs {
                    if !first {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", x)?;
                    first = false;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SexpRelation<'ev> {
    EmptyRelation(/* flipped: */ bool),
    UnaryRelation(/* flipped: */ bool, HashSet<&'ev str>),
    BinaryRelation(/* flipped: */ bool, HashSet<(&'ev str, &'ev str)>),
}

impl<'ev> SexpRelation<'ev> {
    pub fn flipped(&self) -> bool {
        use SexpRelation::*;
        match self {
            EmptyRelation(b) => *b,
            UnaryRelation(b, _) => *b,
            BinaryRelation(b, _) => *b,
        }
    }

    pub fn contains<B: BV>(&self, args: &[SexpVal<'ev, B>]) -> Result<bool, InterpretError<'static>> {
        match (args.len(), self) {
            (i, SexpRelation::EmptyRelation(flipped)) if (1..=2).contains(&i) => Ok(*flipped),
            (1, SexpRelation::UnaryRelation(flipped, s)) => {
                let ev = args[0].expect_event()?;
                Ok(*flipped != s.contains(ev))
            }
            (2, SexpRelation::BinaryRelation(flipped, s)) => {
                let ev1 = args[0].expect_event()?;
                let ev2 = args[1].expect_event()?;
                Ok(*flipped != s.contains(&(ev1, ev2)))
            }
            _ => Err(InterpretError::bad_function_call()),
        }
    }

    pub fn expect_binary(self) -> Result<HashSet<(&'ev str, &'ev str)>, InterpretError<'static>> {
        match self {
            SexpRelation::EmptyRelation(_) => Ok(HashSet::new()),
            SexpRelation::BinaryRelation(_, r) => Ok(r.clone()),
            other => Err(InterpretError::unexpected_relation("binary relation", other)),
        }
    }

    pub fn expect_unary(self) -> Result<HashSet<&'ev str>, InterpretError<'static>> {
        match self {
            SexpRelation::EmptyRelation(_) => Ok(HashSet::new()),
            SexpRelation::UnaryRelation(_, r) => Ok(r.clone()),
            other => Err(InterpretError::unexpected_relation("unary relation", other)),
        }
    }
}

impl<'ev> fmt::Display for SexpRelation<'ev> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::EmptyRelation(false) => write!(f, "[]"),
            Self::EmptyRelation(true) => write!(f, "-[]"),
            Self::UnaryRelation(b, s) => write!(f, "{}[{:?}]", if *b { "-" } else { "" }, s),
            Self::BinaryRelation(b, s) => write!(f, "{}[{:?}]", if *b { "-" } else { "" }, s),
        }
    }
}

/// SexpVal contains just the atomic parts of an S-expression,
/// augmented with elements an additional set of events, which is
/// useful in the context of axiomatic memory models.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SexpVal<'ev, B> {
    Event(&'ev str),
    Bool(bool),
    I128(i128),
    Bits(B),
    // Relation : (Array Event^n Bool)
    Relation(SexpRelation<'ev>),
}

impl<'ev, B: BV> fmt::Display for SexpVal<'ev, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Event(ev) => write!(f, "{}", ev),
            Self::Bool(b) => write!(f, "{}", b),
            Self::I128(i) => write!(f, "{}", i),
            Self::Bits(b) => write!(f, "{}", b),
            Self::Relation(r) => write!(f, "{}", r),
        }
    }
}

#[derive(Clone, Debug)]
pub enum InterpretErrorKind {
    EmptyList,
    NotFound(String),
    BadParamList,
    BadFunctionCall,
    BadLet,
    UnknownFunction(String),
    Overflow,
    Type(String),
    BadRelation(String),
    UnexpectedType(String, String),
}

#[derive(Clone, Debug)]
pub struct InterpretError<'s> {
    kind: InterpretErrorKind,
    context: Vec<Sexp<'s>>,
}

impl<'s> InterpretError<'s> {
    pub fn from_kind(kind: InterpretErrorKind) -> Self {
        InterpretError { kind, context: vec![] }
    }

    pub fn push_context(self, ctx: Sexp<'s>) -> Self {
        let mut new_ctx = vec![];
        new_ctx.clone_from(&self.context);
        new_ctx.push(ctx);
        InterpretError { kind: self.kind, context: new_ctx }
    }

    pub fn empty_list() -> Self {
        Self::from_kind(InterpretErrorKind::EmptyList)
    }

    pub fn not_found(msg: String) -> Self {
        Self::from_kind(InterpretErrorKind::NotFound(msg))
    }

    pub fn bad_param_list() -> Self {
        Self::from_kind(InterpretErrorKind::BadParamList)
    }

    pub fn bad_function_call() -> Self {
        Self::from_kind(InterpretErrorKind::BadFunctionCall)
    }

    pub fn bad_let() -> Self {
        Self::from_kind(InterpretErrorKind::BadLet)
    }

    pub fn overflow() -> Self {
        Self::from_kind(InterpretErrorKind::Overflow)
    }

    pub fn bad_type(msg: String) -> Self {
        Self::from_kind(InterpretErrorKind::Type(msg))
    }

    pub fn unknown_function(f: String) -> Self {
        Self::from_kind(InterpretErrorKind::UnknownFunction(f))
    }

    pub fn bad_relation(msg: String) -> Self {
        Self::from_kind(InterpretErrorKind::BadRelation(msg))
    }

    pub fn unexpected_val<B: BV>(expected: &str, actual: &SexpVal<'_, B>) -> Self {
        Self::from_kind(InterpretErrorKind::UnexpectedType(expected.to_string(), format!("{}", actual)))
    }

    pub fn unexpected_relation(expected: &str, actual: SexpRelation<'_>) -> Self {
        Self::from_kind(InterpretErrorKind::UnexpectedType(expected.to_string(), format!("{}", actual)))
    }

    pub fn unexpected_sexp(expected: &str, actual: &Sexp<'s>) -> Self {
        Self::from_kind(InterpretErrorKind::UnexpectedType(expected.to_string(), format!("{}", actual)))
    }
}

pub type InterpretResult<'ev, 's, B> = Result<SexpVal<'ev, B>, InterpretError<'s>>;

/// Optional check for same-flipped-ness
fn same_flip(expected: Option<bool>, actual: &bool) -> bool {
    match (expected, actual) {
        (None, _) => true,
        (Some(b), a) => b == *a,
    }
}

impl<'ev, 's, B: BV> SexpVal<'ev, B> {
    pub fn into_bits(self) -> Option<B> {
        match self {
            SexpVal::Bits(bv) => Some(bv),
            _ => None,
        }
    }

    pub fn convert_into_bits(self) -> Option<B> {
        match self {
            SexpVal::Bits(bv) => Some(bv),
            SexpVal::Bool(b) => Some(B::from_u8(b as u8)),
            SexpVal::I128(i) => Some(B::zeros(8).add_i128(i)),
            _ => None,
        }
    }

    pub fn expect_binary_relation(
        &self,
        flipped: Option<bool>,
    ) -> Result<HashSet<(&'ev str, &'ev str)>, InterpretError<'s>> {
        match self {
            Self::Relation(SexpRelation::EmptyRelation(b)) if same_flip(flipped, b) => Ok(HashSet::new()),
            Self::Relation(SexpRelation::BinaryRelation(b, r)) if same_flip(flipped, b) => Ok(r.clone()),
            other if flipped == Some(true) => {
                Err(InterpretError::unexpected_val("complementary binary relation", other))
            }
            other => Err(InterpretError::unexpected_val("binary relation", other)),
        }
    }

    pub fn expect_set(&self, flipped: Option<bool>) -> Result<HashSet<&'ev str>, InterpretError<'s>> {
        match self {
            Self::Relation(SexpRelation::EmptyRelation(b)) if same_flip(flipped, b) => Ok(HashSet::new()),
            Self::Relation(SexpRelation::UnaryRelation(b, h)) if same_flip(flipped, b) => Ok(h.clone()),
            other if flipped == Some(true) => {
                Err(InterpretError::unexpected_val("complementary unary relation", other))
            }
            other => Err(InterpretError::unexpected_val("unary relation", other)),
        }
    }

    pub fn expect_relation(&self, flipped: Option<bool>) -> Result<SexpRelation<'ev>, InterpretError<'s>> {
        match self {
            Self::Relation(r) if same_flip(flipped, &r.flipped()) => Ok(r.clone()),
            other => Err(InterpretError::unexpected_val("relation", other)),
        }
    }

    pub fn into_event(self) -> Option<&'ev str> {
        match self {
            SexpVal::Event(ev) => Some(ev),
            _ => None,
        }
    }

    pub fn expect_event(&self) -> Result<&'ev str, InterpretError<'s>> {
        match self {
            Self::Event(ev) => Ok(*ev),
            other => Err(InterpretError::unexpected_val("event", other)),
        }
    }

    pub fn into_bool(self) -> Option<bool> {
        match self {
            SexpVal::Bool(b) => Some(b),
            _ => None,
        }
    }

    pub fn expect_bool(&self) -> Result<bool, InterpretError<'s>> {
        match self {
            Self::Bool(b) => Ok(*b),
            other => Err(InterpretError::unexpected_val("bool", other)),
        }
    }
}

impl fmt::Display for InterpretErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use InterpretErrorKind::*;
        match self {
            EmptyList => write!(f, "Tried to interpret the empty list"),
            NotFound(v) => write!(f, "The variable {} was not found", v),
            BadParamList => write!(f, "Bad function parameter list"),
            BadFunctionCall => write!(f, "Bad function call"),
            BadLet => write!(f, "Bad let binding in expression"),
            UnknownFunction(name) => write!(f, "Unknown function {}", name),
            Type(builtin) => write!(f, "Type error in call to builtin function or special form {}", builtin),
            Overflow => write!(f, "Bitvector did not fit in small bitvector type"),
            BadRelation(s) => write!(f, "Malformed array set: {}", s),
            UnexpectedType(expected, actual) => {
                write!(f, "Unexpected S-expr: expected {}, but got {}", expected, actual)
            }
        }
    }
}

impl<'s> fmt::Display for InterpretError<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "in ")?;

        for frame in self.context.iter().rev() {
            write!(f, "\'{}\', ", frame)?;
        }

        write!(f, "{}", self.kind)
    }
}

impl<'s> Error for InterpretError<'s> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

#[derive(Debug)]
pub struct SexpFn<'s> {
    pub params: Vec<&'s str>,
    pub body: Sexp<'s>,
}

#[derive(Default, Debug)]
pub struct InterpretEnv<'s, 'ev, B> {
    local_vars: HashMap<&'s str, Vec<SexpVal<'ev, B>>>,
    pub events: HashMap<&'ev str, SexpVal<'ev, B>>,
}

impl<'s, 'ev, B: BV> InterpretEnv<'s, 'ev, B> {
    pub fn new() -> Self {
        InterpretEnv { local_vars: HashMap::new(), events: HashMap::new() }
    }

    pub fn add_event(&mut self, ev: &'ev str) {
        self.events.insert(ev, SexpVal::Event(ev));
    }

    fn get(&self, id: &'s str) -> Option<&SexpVal<'ev, B>> {
        let local_value = match self.local_vars.get(id) {
            Some(values) => values.last(),
            None => None,
        };

        if local_value.is_none() {
            self.events.get(id)
        } else {
            local_value
        }
    }

    pub fn push(&mut self, id: &'s str, value: SexpVal<'ev, B>) {
        match self.local_vars.get_mut(id) {
            Some(values) => values.push(value),
            None => {
                self.local_vars.insert(id, vec![value]);
            }
        }
    }

    pub fn pop(&mut self, id: &'s str) {
        match self.local_vars.get_mut(id) {
            Some(values) => {
                values.pop();
            }
            None => panic!("Tried to remove variable binding that didn't exist when interpreting S-expression"),
        }
    }
}

impl<'ev, 's, B: BV> SexpVal<'ev, B> {
    fn negate(self) -> Result<Self, InterpretError<'s>> {
        match self {
            SexpVal::Bool(b) => Ok(SexpVal::Bool(!b)),
            _ => Err(InterpretError::bad_type("negate".to_string())),
        }
    }
}

fn and<'ev, 's, B: BV>(xs: &[SexpVal<'ev, B>]) -> InterpretResult<'ev, 's, B> {
    Ok(SexpVal::Bool(xs.iter().try_fold(true, |acc, x| match x {
        SexpVal::Bool(b) => Ok(*b && acc),
        _ => Err(InterpretError::bad_type("and".to_string())),
    })?))
}

fn or<'ev, 's, B: BV>(xs: &[SexpVal<'ev, B>]) -> InterpretResult<'ev, 's, B> {
    Ok(SexpVal::Bool(xs.iter().try_fold(false, |acc, x| match x {
        SexpVal::Bool(b) => Ok(*b || acc),
        _ => Err(InterpretError::bad_type("or".to_string())),
    })?))
}

fn concat<'ev, 's, B: BV>(xs: &[SexpVal<'ev, B>]) -> InterpretResult<'ev, 's, B> {
    Ok(SexpVal::Bits(xs.iter().try_fold(B::zeros(0), |acc, x| match x {
        SexpVal::Bits(bv) => acc.append(*bv).ok_or_else(|| InterpretError::bad_type("concat".to_string())),
        _ => Err(InterpretError::bad_type("concat".to_string())),
    })?))
}

fn store1<'ev, 's, B: BV>(
    arr: &SexpVal<'ev, B>,
    key: &SexpVal<'ev, B>,
    val: &SexpVal<'ev, B>,
) -> InterpretResult<'ev, 's, B> {
    let r = arr.expect_relation(None)?;
    let flipped = r.flipped();
    let mut arr_rel = r.expect_unary()?;
    let k = key.expect_event()?;
    let v = val.expect_bool()?;
    // for some reason, z3 also outputs stuff like (store ((as const Array) true) ev true)
    // this is superfluous, and we can detect when the inner array is flipped the same way and ignore it
    if v != flipped {
        arr_rel.insert(k);
    };
    Ok(SexpVal::Relation(SexpRelation::UnaryRelation(!v, arr_rel)))
}

fn store2<'ev, 's, B: BV>(
    arr: &SexpVal<'ev, B>,
    key1: &SexpVal<'ev, B>,
    key2: &SexpVal<'ev, B>,
    val: &SexpVal<'ev, B>,
) -> InterpretResult<'ev, 's, B> {
    let r = arr.expect_relation(None)?;
    let flipped = r.flipped();
    let mut arr_rel = r.expect_binary()?;
    let ev1 = key1.expect_event()?;
    let ev2 = key2.expect_event()?;
    let v = val.expect_bool()?;
    if v != flipped {
        arr_rel.insert((ev1, ev2));
    }
    Ok(SexpVal::Relation(SexpRelation::BinaryRelation(!v, arr_rel)))
}

pub struct DefineFun<'s> {
    pub name: &'s str,
    pub params: Vec<(&'s str, Sexp<'s>)>,
    pub ret_ty: Sexp<'s>,
    pub body: Sexp<'s>,
}

#[derive(Clone, Debug)]
pub struct LambdaFun<'s> {
    pub params: Vec<(&'s str, Sexp<'s>)>,
    pub body: Sexp<'s>,
}

impl<'s> Sexp<'s> {
    pub fn is_fn(&self, name: &str, args: usize) -> bool {
        match self {
            Sexp::List(sexps) if sexps.len() > args => {
                if let Sexp::Atom(f) = sexps[0] {
                    f == name
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    pub fn is_as_const(&self) -> bool {
        match self {
            Sexp::List(xs) if xs.len() == 2 => match &xs[0] {
                Sexp::List(ys) if ys.len() == 3 && ys[0].is_atom("as") && ys[1].is_atom("const") => true,
                _ => false,
            },
            _ => false,
        }
    }

    pub fn is_lambda(&self) -> bool {
        match self {
            Sexp::List(xs) if xs.len() == 3 && xs[0].is_atom("lambda") => true,
            _ => false,
        }
    }

    pub fn is_atom(&self, s: &str) -> bool {
        match self {
            Sexp::Atom(atom) => *atom == s,
            _ => false,
        }
    }

    pub fn as_str(&self) -> Option<&'s str> {
        match self {
            Sexp::Atom(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_usize(&self) -> Option<usize> {
        match self {
            Sexp::I128(n) => Some(*n as usize),
            _ => None,
        }
    }

    pub fn as_list(&self) -> Option<&[Self]> {
        match self {
            Sexp::List(xs) => Some(xs),
            _ => None,
        }
    }

    pub fn as_pair(&self) -> Option<(&Self, &Self)> {
        match self {
            Sexp::List(xs) if xs.len() == 2 => Some((&xs[0], &xs[1])),
            _ => None,
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Sexp::I128(n) => Some(*n as u64),
            Sexp::Bits(bv) => B64::from_str(bv).map(B64::lower_u64),
            _ => None,
        }
    }

    pub fn dest_list(self) -> Option<Vec<Self>> {
        match self {
            Sexp::List(xs) => Some(xs),
            _ => None,
        }
    }

    pub fn dest_cons(self) -> Option<(Self, Vec<Self>)> {
        match self {
            Sexp::List(mut list) if !list.is_empty() => {
                let tl = list.drain(1..).collect();
                let hd = list.remove(0);
                Some((hd, tl))
            }
            _ => None,
        }
    }

    pub fn is_pair(&self) -> bool {
        match self {
            Sexp::List(list) if list.len() == 2 => true,
            _ => false,
        }
    }

    pub fn dest_pair(self) -> Option<(Self, Self)> {
        match self {
            Sexp::List(mut list) if list.len() == 2 => {
                let snd = list.pop()?;
                let fst = list.pop()?;
                Some((fst, snd))
            }
            _ => None,
        }
    }

    pub fn dest_name_pair(self) -> Option<(&'s str, Self)> {
        match self {
            Sexp::List(mut list) if list.len() == 2 => {
                let snd = list.pop()?;
                match list.pop()? {
                    Sexp::Atom(fst) => Some((fst, snd)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub fn dest_fn(self, name: &str) -> Option<Vec<Self>> {
        match self.dest_cons() {
            Some((f, xs)) if f.is_atom(name) => Some(xs),
            _ => None,
        }
    }

    pub fn dest_fn_or_list(self, name: &str) -> Option<Vec<Self>> {
        match self {
            Sexp::List(mut list) => {
                if !list.is_empty() && list[0].is_atom(name) {
                    Some(list.drain(1..).collect())
                } else {
                    Some(list)
                }
            }
            _ => None,
        }
    }

    pub fn dest_define_fun(self) -> Option<DefineFun<'s>> {
        match self.dest_fn("define-fun") {
            Some(mut xs) if xs.len() == 4 => {
                let mut xs: Vec<Option<Self>> = xs.drain(..).map(Some).collect();

                let params = xs[1]
                    .take()?
                    .dest_list()?
                    .drain(..)
                    .map(|sexp| {
                        if let Some((name, ty)) = sexp.dest_pair() {
                            name.as_str().map(|name| (name, ty))
                        } else {
                            None
                        }
                    })
                    .collect::<Option<Vec<_>>>()?;

                Some(DefineFun { name: xs[0].take()?.as_str()?, params, ret_ty: xs[2].take()?, body: xs[3].take()? })
            }
            _ => None,
        }
    }

    pub fn dest_lambda(self) -> Result<LambdaFun<'s>, InterpretError<'s>> {
        match self.dest_list() {
            Some(mut xs) if xs.len() == 3 && xs[0].is_atom("lambda") => {
                let body = xs.pop().unwrap();
                let params = xs.pop().unwrap();
                let mut typed_bindings = vec![];
                match params {
                    Sexp::List(params) => {
                        for b in params {
                            match b.dest_pair() {
                                Some((Sexp::Atom(name), ty)) => {
                                    typed_bindings.push((name, ty));
                                }
                                _ => return Err(InterpretError::bad_param_list()),
                            }
                        }
                    }
                    _ => return Err(InterpretError::bad_param_list()),
                }
                Ok(LambdaFun { params: typed_bindings, body: body.clone() })
            }
            _ => return Err(InterpretError::bad_type("lambda".to_string())),
        }
    }

    pub fn interpret<'ev, B: BV>(&self, env: &mut InterpretEnv<'s, 'ev, B>) -> InterpretResult<'ev, 's, B> {
        let r = self._interpret(env);
        r.map_err(|e| e.push_context(self.clone()))
    }

    fn _interpret<'ev, B: BV>(&self, env: &mut InterpretEnv<'s, 'ev, B>) -> InterpretResult<'ev, 's, B> {
        match self {
            Sexp::Atom("true") => Ok(SexpVal::Bool(true)),
            Sexp::Atom("false") => Ok(SexpVal::Bool(false)),

            Sexp::Atom(a) => match env.get(a) {
                Some(v) => Ok(v.clone()),
                None => Err(InterpretError::not_found((*a).to_string())),
            },

            Sexp::I128(n) => Ok(SexpVal::I128(*n)),

            Sexp::Bits(b) => Ok(SexpVal::Bits(B::from_str(b).ok_or(InterpretError::overflow())?)),

            Sexp::List(xs) if xs.len() == 4 && xs[0].is_atom("ite") => {
                let cond = xs[1].interpret(env)?;
                match cond {
                    SexpVal::Bool(b) => {
                        if b {
                            xs[2].interpret(env)
                        } else {
                            xs[3].interpret(env)
                        }
                    }
                    _ => Err(InterpretError::bad_type("ite".to_string())),
                }
            }

            Sexp::List(xs) if xs.len() == 3 && xs[0].is_atom("let") => {
                if let Some(bindings) = xs[1].as_list() {
                    let mut vars = Vec::new();
                    for binding in bindings {
                        if let Some((var, sexp)) = binding.as_pair() {
                            let var = var.as_str().ok_or(InterpretError::bad_let())?;
                            let value = sexp.interpret(env)?;
                            vars.push(var);
                            env.push(var, value);
                        } else {
                            return Err(InterpretError::bad_let());
                        }
                    }
                    let value = xs[2].interpret(env)?;
                    vars.iter().for_each(|v| env.pop(v));
                    Ok(value)
                } else {
                    Err(InterpretError::bad_let())
                }
            }

            // ((as const Array) false)
            Sexp::List(xs)
                if xs.len() == 2
                    && (xs[1].is_atom("false") || xs[1].is_atom("true"))
                    && matches!(
                    &xs[0],
                    Sexp::List(ys) if ys.len() == 3 && ys[0].is_atom("as") && ys[1].is_atom("const")) =>
            {
                Ok(SexpVal::Relation(SexpRelation::EmptyRelation(xs[1].is_atom("true"))))
            }

            // (_ as-array ATOM)
            Sexp::List(xs)
                if xs.len() == 3
                    && xs[0].is_atom("_")
                    && xs[1].is_atom("as-array")
                    && matches!(&xs[2], Sexp::Atom(_)) =>
            {
                Ok(SexpVal::Relation(SexpRelation::EmptyRelation(false)))
            }

            Sexp::List(xs) if !xs.is_empty() => {
                let f = xs[0].as_str().ok_or(InterpretError::bad_function_call())?;
                let mut args: Vec<SexpVal<B>> =
                    xs[1..].iter().map(|sexp| sexp.interpret(env)).collect::<Result<_, _>>()?;

                if f == "=" && args.len() == 2 {
                    Ok(SexpVal::Bool(args[0] == args[1]))
                } else if f == "not" && args.len() == 1 {
                    args.pop().unwrap().negate()
                } else if f == "and" {
                    and(&args)
                } else if f == "or" {
                    or(&args)
                } else if f == "concat" {
                    concat(&args)
                } else if f == "store" && args.len() == 3 {
                    store1(&args[0], &args[1], &args[2])
                } else if f == "store" && args.len() == 4 {
                    store2(&args[0], &args[1], &args[2], &args[3])
                } else {
                    Err(InterpretError::unknown_function(f.to_string()))
                }
            }

            Sexp::List(_) => Err(InterpretError::empty_list()),
        }
    }
}
