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

use std::collections::HashMap;
use std::error::Error;
use std::fmt;

use isla_lib::concrete::{bitvector64::B64, BV};

#[derive(Debug)]
pub enum Sexp<'s> {
    Atom(&'s str),
    I128(i128),
    Bits(&'s str),
    List(Vec<Sexp<'s>>),
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
}

impl<'ev, B: BV> SexpVal<'ev, B> {
    pub fn into_bits(self) -> Option<B> {
        match self {
            SexpVal::Bits(bv) => Some(bv),
            _ => None,
        }
    }

    pub fn into_int_string(self) -> String {
        match self {
            SexpVal::Event(ev) => ev.to_string(),
            SexpVal::Bool(b) => b.to_string(),
            SexpVal::I128(i) => i.to_string(),
            SexpVal::Bits(bv) => format!("#x{:x} {}", bv, bv.len()),
        }
    }

    pub fn into_truncated_string(self) -> String {
        match self {
            SexpVal::Event(ev) => ev.to_string(),
            SexpVal::Bool(b) => b.to_string(),
            SexpVal::I128(i) => i.to_string(),
            SexpVal::Bits(bv) => format!("#x{:x}", bv),
        }
    }
}

#[derive(Debug)]
pub enum InterpretError {
    EmptyList,
    NotFound(String),
    BadParamList,
    BadFunctionCall,
    BadLet,
    UnknownFunction(String),
    Overflow,
    Type(String),
}

impl fmt::Display for InterpretError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use InterpretError::*;
        match self {
            EmptyList => write!(f, "Tried to interpret the empty list"),
            NotFound(v) => write!(f, "The variable {} was not found", v),
            BadParamList => write!(f, "Bad function parameter list"),
            BadFunctionCall => write!(f, "Bad function call"),
            BadLet => write!(f, "Bad let binding in expression"),
            UnknownFunction(name) => write!(f, "Unknown function {}", name),
            Type(builtin) => write!(f, "Type error in call to builtin function or special form {}", builtin),
            Overflow => write!(f, "Bitvector did not fit in small bitvector type"),
        }
    }
}

impl Error for InterpretError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

pub struct SexpFn<'s> {
    pub params: Vec<&'s str>,
    pub body: Sexp<'s>,
}

#[derive(Default)]
pub struct InterpretEnv<'s, 'ev, B> {
    local_vars: HashMap<&'s str, Vec<SexpVal<'ev, B>>>,
    event_vars: HashMap<&'ev str, SexpVal<'ev, B>>,
}

impl<'s, 'ev, B: BV> InterpretEnv<'s, 'ev, B> {
    pub fn new() -> Self {
        InterpretEnv { local_vars: HashMap::new(), event_vars: HashMap::new() }
    }

    pub fn add_event(&mut self, ev: &'ev str) {
        self.event_vars.insert(ev, SexpVal::Event(ev));
    }

    pub fn add_args(&mut self, params: &[&'s str], args: &[SexpVal<'ev, B>]) -> Result<(), InterpretError> {
        if params.len() != args.len() {
            Err(InterpretError::BadParamList)
        } else {
            for (param, arg) in params.iter().zip(args.iter()) {
                self.push(param, arg.clone())
            }
            Ok(())
        }
    }

    pub fn clear_args(&mut self, params: &[&'s str]) {
        for param in params {
            self.pop(param)
        }
    }

    fn get(&self, id: &'s str) -> Option<&SexpVal<'ev, B>> {
        let local_value = match self.local_vars.get(id) {
            Some(values) => values.last(),
            None => None,
        };

        if local_value.is_none() {
            self.event_vars.get(id)
        } else {
            local_value
        }
    }

    fn push(&mut self, id: &'s str, value: SexpVal<'ev, B>) {
        match self.local_vars.get_mut(id) {
            Some(values) => values.push(value),
            None => {
                self.local_vars.insert(id, vec![value]);
            }
        }
    }

    fn pop(&mut self, id: &'s str) {
        match self.local_vars.get_mut(id) {
            Some(values) => {
                values.pop();
            }
            None => panic!("Tried to remove variable binding that didn't exist when interpreting S-expression"),
        }
    }
}

impl<'ev, B: BV> SexpVal<'ev, B> {
    fn negate(self) -> Result<Self, InterpretError> {
        match self {
            SexpVal::Bool(b) => Ok(SexpVal::Bool(!b)),
            _ => Err(InterpretError::Type("negate".to_string())),
        }
    }
}

fn and<'ev, B: BV>(xs: &[SexpVal<'ev, B>]) -> Result<SexpVal<'ev, B>, InterpretError> {
    Ok(SexpVal::Bool(xs.iter().try_fold(true, |acc, x| match x {
        SexpVal::Bool(b) => Ok(*b && acc),
        _ => Err(InterpretError::Type("and".to_string())),
    })?))
}

fn or<'ev, B: BV>(xs: &[SexpVal<'ev, B>]) -> Result<SexpVal<'ev, B>, InterpretError> {
    Ok(SexpVal::Bool(xs.iter().try_fold(false, |acc, x| match x {
        SexpVal::Bool(b) => Ok(*b || acc),
        _ => Err(InterpretError::Type("or".to_string())),
    })?))
}

pub struct DefineFun<'s> {
    pub name: &'s str,
    pub params: Vec<(&'s str, Sexp<'s>)>,
    pub ret_ty: Sexp<'s>,
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

    pub fn dest_fn(self, name: &str) -> Option<Vec<Self>> {
        match self.dest_cons() {
            Some((f, xs)) if f.is_atom(name) => Some(xs),
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
                            if let Some(name) = name.as_str() {
                                Some((name, ty))
                            } else {
                                None
                            }
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

    pub fn interpret<'ev, B: BV>(
        &self,
        env: &mut InterpretEnv<'s, 'ev, B>,
        fns: &HashMap<&'s str, SexpFn<'s>>,
    ) -> Result<SexpVal<'ev, B>, InterpretError> {
        use InterpretError::*;
        match self {
            Sexp::Atom("true") => Ok(SexpVal::Bool(true)),
            Sexp::Atom("false") => Ok(SexpVal::Bool(false)),

            Sexp::Atom(a) => match env.get(a) {
                Some(v) => Ok(v.clone()),
                None => Err(NotFound((*a).to_string())),
            },

            Sexp::I128(n) => Ok(SexpVal::I128(*n)),

            Sexp::Bits(b) => Ok(SexpVal::Bits(B::from_str(*b).ok_or_else(|| Overflow)?)),

            Sexp::List(xs) if xs.len() == 4 && xs[0].is_atom("ite") => {
                let cond = xs[1].interpret(env, fns)?;
                match cond {
                    SexpVal::Bool(b) => {
                        if b {
                            xs[2].interpret(env, fns)
                        } else {
                            xs[3].interpret(env, fns)
                        }
                    }
                    _ => Err(Type("ite".to_string())),
                }
            }

            Sexp::List(xs) if xs.len() == 3 && xs[0].is_atom("let") => {
                if let Some(bindings) = xs[1].as_list() {
                    let mut vars = Vec::new();
                    for binding in bindings {
                        if let Some((var, sexp)) = binding.as_pair() {
                            let var = var.as_str().ok_or_else(|| BadLet)?;
                            let value = sexp.interpret(env, fns)?;
                            vars.push(var);
                            env.push(var, value);
                        } else {
                            return Err(BadLet);
                        }
                    }
                    let value = xs[2].interpret(env, fns)?;
                    vars.iter().for_each(|v| env.pop(v));
                    Ok(value)
                } else {
                    Err(BadLet)
                }
            }

            Sexp::List(xs) if !xs.is_empty() => {
                let f = xs[0].as_str().ok_or_else(|| BadFunctionCall)?;
                let mut args: Vec<SexpVal<B>> =
                    xs[1..].iter().map(|sexp| sexp.interpret(env, fns)).collect::<Result<_, _>>()?;

                if f == "=" && args.len() == 2 {
                    Ok(SexpVal::Bool(args[0] == args[1]))
                } else if f == "not" && args.len() == 1 {
                    args.pop().unwrap().negate()
                } else if f == "and" {
                    and(&args)
                } else if f == "or" {
                    or(&args)
                } else {
                    let function = fns.get(f).ok_or_else(|| InterpretError::UnknownFunction(f.to_string()))?;
                    env.add_args(&function.params, &args)?;
                    let result = function.body.interpret(env, fns)?;
                    env.clear_args(&function.params);
                    Ok(result)
                }
            }

            Sexp::List(_) => Err(EmptyList),
        }
    }
}
