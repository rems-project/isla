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

use std::fmt;

use crate::concrete::*;

pub type SVal = u32;

#[derive(Clone)]
pub enum Exp {
    Concrete(CVal),
    Symbolic(SVal),
    Var(usize),
    Eq(Box<Exp>, Box<Exp>),
    Not(Box<Exp>),
    Bvnot(Box<Exp>),
    Bvand(Box<Exp>, Box<Exp>),
    Bvor(Box<Exp>, Box<Exp>),
    Bvneg(Box<Exp>),
    Bvadd(Box<Exp>, Box<Exp>),
    Bvmul(Box<Exp>, Box<Exp>),
    Bvudiv(Box<Exp>, Box<Exp>),
    Bvurem(Box<Exp>, Box<Exp>),
    /*
        Bvshl(Box<Exp>, Box<Exp>),
        Bvlshr(Box<Exp>, Box<Exp>),
        Bvult(Box<Exp>, Box<Exp>),
    */
}

#[derive(Clone)]
pub enum Repr<C, S> {
    Concrete(C),
    Symbolic(S),
}

impl<C: fmt::Display, S: fmt::Display> fmt::Display for Repr<C, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Repr::Concrete(c) => C::fmt(c, f),
            Repr::Symbolic(s) => S::fmt(s, f),
        }
    }
}

pub fn evaluate_exp(exp: &Exp, vars: &Vec<Repr<CVal, SVal>>) -> Exp {
    match exp {
        Exp::Concrete(cv) => Exp::Concrete(cv.clone()),
        Exp::Symbolic(cv) => Exp::Symbolic(cv.clone()),
        Exp::Var(v) => match &vars[*v] {
            Repr::Concrete(cv) => Exp::Concrete(cv.clone()),
            Repr::Symbolic(sv) => Exp::Symbolic(*sv),
        },
        Exp::Eq(a, b) => {
            let a = evaluate_exp(a, vars);
            let b = evaluate_exp(b, vars);
            match (a, b) {
                (Exp::Concrete(CVal::Sbits(a)), Exp::Concrete(CVal::Sbits(b))) => {
                    Exp::Concrete(CVal::Bool(a == b))
                }
                (Exp::Concrete(CVal::Bool(a)), Exp::Concrete(CVal::Bool(b))) => {
                    Exp::Concrete(CVal::Bool(a == b))
                }
                (Exp::Concrete(CVal::Int(a)), Exp::Concrete(CVal::Int(b))) => {
                    Exp::Concrete(CVal::Bool(a == b))
                }
                (a, b) => Exp::Eq(Box::new(a), Box::new(b)),
            }
        }
        Exp::Not(a) => {
            let a = evaluate_exp(a, vars);
            match a {
                Exp::Concrete(CVal::Bool(a)) => Exp::Concrete(CVal::Bool(!a)),
                a => Exp::Not(Box::new(a)),
            }
        }
        Exp::Bvnot(a) => {
            let a = evaluate_exp(a, vars);
            match a {
                Exp::Concrete(CVal::Sbits(a)) => Exp::Concrete(CVal::Sbits(!a)),
                a => Exp::Bvnot(Box::new(a)),
            }
        }
        Exp::Bvand(a, b) => {
            let a = evaluate_exp(a, vars);
            let b = evaluate_exp(b, vars);
            match (a, b) {
                (Exp::Concrete(CVal::Sbits(a)), Exp::Concrete(CVal::Sbits(b))) => {
                    Exp::Concrete(CVal::Sbits(a & b))
                }
                (a, b) => Exp::Bvand(Box::new(a), Box::new(b)),
            }
        }
        Exp::Bvor(a, b) => {
            let a = evaluate_exp(a, vars);
            let b = evaluate_exp(b, vars);
            match (a, b) {
                (Exp::Concrete(CVal::Sbits(a)), Exp::Concrete(CVal::Sbits(b))) => {
                    Exp::Concrete(CVal::Sbits(a | b))
                }
                (a, b) => Exp::Bvor(Box::new(a), Box::new(b)),
            }
        }
        Exp::Bvneg(a) => {
            let a = evaluate_exp(a, vars);
            match a {
                Exp::Concrete(CVal::Sbits(a)) => Exp::Concrete(CVal::Sbits(-a)),
                a => Exp::Bvneg(Box::new(a)),
            }
        }
        Exp::Bvadd(a, b) => {
            let a = evaluate_exp(a, vars);
            let b = evaluate_exp(b, vars);
            match (a, b) {
                (Exp::Concrete(CVal::Sbits(a)), Exp::Concrete(CVal::Sbits(b))) => {
                    Exp::Concrete(CVal::Sbits(a + b))
                }
                (a, b) => Exp::Bvadd(Box::new(a), Box::new(b)),
            }
        }
        Exp::Bvmul(a, b) => {
            let a = evaluate_exp(a, vars);
            let b = evaluate_exp(b, vars);
            match (a, b) {
                (Exp::Concrete(CVal::Sbits(a)), Exp::Concrete(CVal::Sbits(b))) => {
                    Exp::Concrete(CVal::Sbits(a * b))
                }
                (a, b) => Exp::Bvmul(Box::new(a), Box::new(b)),
            }
        }
        Exp::Bvudiv(a, b) => {
            let a = evaluate_exp(a, vars);
            let b = evaluate_exp(b, vars);
            match (a, b) {
                (Exp::Concrete(CVal::Sbits(a)), Exp::Concrete(CVal::Sbits(b))) => {
                    Exp::Concrete(CVal::Sbits(a * b))
                }
                (a, b) => Exp::Bvudiv(Box::new(a), Box::new(b)),
            }
        }
        Exp::Bvurem(a, b) => {
            let a = evaluate_exp(a, vars);
            let b = evaluate_exp(b, vars);
            match (a, b) {
                (Exp::Concrete(CVal::Sbits(a)), Exp::Concrete(CVal::Sbits(b))) => {
                    Exp::Concrete(CVal::Sbits(a * b))
                }
                (a, b) => Exp::Bvurem(Box::new(a), Box::new(b)),
            }
        }
    }
}
