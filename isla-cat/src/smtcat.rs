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

use crate::cat::*;

pub enum Sexp {
    False,
    RelApp(String, u32, u32),
    SetApp(String, u32),
    Or(Vec<Sexp>),
    And(Vec<Sexp>),
    Not(Box<Sexp>),
    Eq(u32, u32),
    Exists(u32, Box<Sexp>),
    Implies(Box<Sexp>, Box<Sexp>),
}

fn fresh() -> u32 {
    0
}

pub fn compile_set(exp: &Exp<Ty>, ev: u32) -> Option<Sexp> {
    use Sexp::*;
    Some(match exp {
        Exp::Empty(_) => False,
        Exp::Id(name, _) => SetApp(name.clone(), ev),
        Exp::TryWith(x, y, _) => match compile_set(x, ev) {
            Some(x) => x,
            None => compile_set(y, ev)?,
        },
        Exp::Union(x, y, _) => Or(vec![compile_set(x, ev)?, compile_set(y, ev)?]),
        Exp::Inter(x, y, _) => And(vec![compile_set(x, ev)?, compile_set(y, ev)?]),
        Exp::Diff(x, y, _) => And(vec![compile_set(x, ev)?, Not(Box::new(compile_set(y, ev)?))]),
        Exp::Seq(_, _) => return None,
        Exp::Cartesian(_, _) => return None,
        Exp::Compl(x, _) => Not(Box::new(compile_set(x, ev)?)),
        Exp::Identity(_) => return None,
        Exp::IdentityInter(_) => return None,
        _ => panic!("unfinished"),
    })
}

pub fn compile_rel(exp: &Exp<Ty>, ev1: u32, ev2: u32) -> Option<Sexp> {
    use Sexp::*;
    Some(match exp {
        Exp::Empty(_) => False,
        Exp::Id(name, _) => RelApp(name.clone(), ev1, ev2),
        Exp::TryWith(x, y, _) => match compile_rel(x, ev1, ev2) {
            Some(x) => x,
            None => compile_rel(y, ev1, ev2)?,
        },
        Exp::Union(x, y, _) => Or(vec![compile_rel(x, ev1, ev2)?, compile_rel(y, ev1, ev2)?]),
        Exp::Inter(x, y, _) => And(vec![compile_rel(x, ev1, ev2)?, compile_rel(y, ev1, ev2)?]),
        Exp::Diff(x, y, _) => And(vec![compile_rel(x, ev1, ev2)?, Not(Box::new(compile_rel(y, ev1, ev2)?))]),
        Exp::Seq(x, y) => {
            let ev3 = fresh();
            Exists(ev3, Box::new(And(vec![compile_rel(x, ev1, ev3)?, compile_rel(y, ev3, ev2)?])))
        }
        Exp::Cartesian(x, y) => And(vec![compile_set(x, ev1)?, compile_set(y, ev2)?]),
        Exp::Compl(x, _) => Not(Box::new(compile_rel(x, ev1, ev2)?)),
        Exp::Identity(x) => And(vec![compile_set(x, ev1)?, compile_set(x, ev2)?, Eq(ev1, ev2)]),
        Exp::IdentityInter(x) => And(vec![compile_rel(x, ev1, ev2)?, Eq(ev1, ev2)]),
        Exp::Inverse(x) => compile_rel(x, ev2, ev1)?,
        _ => panic!("unfinished"),
    })
}
