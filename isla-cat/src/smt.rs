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

//! This module implements the compilation from the high-order
//! relation-algebra style expressions used by cat into first-order
//! SMT definitions, where relations are represented as functions from
//! Event × Event → Bool and sets are Event → Bool functions.

use std::collections::HashSet;
use std::error::Error;
use std::io::Write;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::cat::*;

/// Event ids are `u32` variables denoted in the generated SMTLIB as
/// `evX` where X is a number greater than 0. The arguments to
/// toplevel relations and sets are always `ev1` and `ev2`.
pub type EventId = u32;

static FRESH_COUNTER: AtomicU32 = AtomicU32::new(3);

fn fresh() -> EventId {
    FRESH_COUNTER.fetch_add(1, Ordering::SeqCst)
}

/// The SMTLIB2 format uses Lisp-style S-expressions. Here we
/// represent only the subset of S-expressions required to represent
/// the relational expressions used by the cat language.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexp {
    True,
    False,
    RelApp(String, EventId, EventId),
    SetApp(String, EventId),
    Or(Vec<Sexp>),
    And(Vec<Sexp>),
    Not(Box<Sexp>),
    Eq(EventId, EventId),
    Exists(EventId, Box<Sexp>),
    Implies(Box<Sexp>, Box<Sexp>),
}

impl Sexp {
    /// Traverse a S-expression bottom up, applying `f` to every sub-expression
    pub fn modify<F>(&mut self, f: &F)
    where
        F: Fn(&mut Self) -> (),
    {
        use Sexp::*;
        match self {
            True | False | RelApp(_, _, _) | SetApp(_, _) | Eq(_, _) => (),
            Not(sexp) | Exists(_, sexp) => sexp.modify(f),
            Implies(sexp1, sexp2) => {
                sexp1.modify(f);
                sexp2.modify(f)
            }
            And(sexps) | Or(sexps) => sexps.iter_mut().for_each(|sexp| sexp.modify(f)),
        }
        f(self)
    }

    fn is_true(&self) -> bool {
        if let Sexp::True = self {
            true
        } else {
            false
        }
    }

    fn is_false(&self) -> bool {
        if let Sexp::False = self {
            true
        } else {
            false
        }
    }

    fn is_and(&self) -> bool {
        if let Sexp::And(_) = self {
            true
        } else {
            false
        }
    }

    fn flatten_and(self) -> Vec<Self> {
        if let Sexp::And(sexps) = self {
            sexps
        } else {
            vec![self]
        }
    }

    fn is_or(&self) -> bool {
        if let Sexp::Or(_) = self {
            true
        } else {
            false
        }
    }

    fn flatten_or(self) -> Vec<Self> {
        if let Sexp::Or(sexps) = self {
            sexps
        } else {
            vec![self]
        }
    }

    fn simplification_step(&mut self, known_empty: &HashSet<String>) {
        use Sexp::*;
        match self {
            RelApp(r, _, _) if known_empty.contains(r) => *self = False,
            SetApp(r, _) if known_empty.contains(r) => *self = False,

            And(sexps) => {
                let sexps: Vec<Sexp> = sexps.drain(..).filter(|sexp| !sexp.is_true()).collect();
                if sexps.is_empty() {
                    *self = True
                } else if sexps.iter().any(|sexp| sexp.is_false()) {
                    *self = False
                } else if sexps.iter().any(|sexp| sexp.is_and()) {
                    *self = And(sexps.iter().map(|sexp| sexp.clone().flatten_and()).flatten().collect())
                } else {
                    *self = And(sexps);
                }
            }

            Or(sexps) => {
                let sexps: Vec<Sexp> = sexps.drain(..).filter(|sexp| !sexp.is_false()).collect();
                if sexps.is_empty() {
                    *self = False
                } else if sexps.iter().any(|sexp| sexp.is_true()) {
                    *self = True
                } else if sexps.iter().any(|sexp| sexp.is_or()) {
                    *self = Or(sexps.iter().map(|sexp| sexp.clone().flatten_or()).flatten().collect())
                } else {
                    *self = Or(sexps)
                }
            }

            Not(sexp) => match &**sexp {
                Not(sexp) => *self = (**sexp).clone(),
                True => *self = False,
                False => *self = True,
                _ => (),
            },

            Exists(_, sexp) => match &**sexp {
                False => *self = False,
                _ => (),
            },

            _ => (),
        }
    }

    /// Simplifies an S-expression, performing rewrites such as
    /// collapsing nested `And` and `Or` constructors, removing double
    /// negations, etc.
    ///
    /// # Arguments
    ///
    /// * `known_empty` - A list of set and/or relation names known to
    /// be empty. Expressions containing them can then be simplified.
    pub fn simplify(&mut self, known_empty: &HashSet<String>) {
        self.modify(&|exp| exp.simplification_step(known_empty))
    }

    /// Writes out the S-expression as a valid SMTLIB2 term.
    ///
    /// # Arguments
    ///
    /// * `output` - The sink to write to.
    /// * `indent` - Whether or not to indent the first line of the output
    /// * `amount` - The current indentation length
    /// * `newline` - If true, place a newline at the end of the expression.
    pub fn write_to(
        &self,
        output: &mut dyn Write,
        indent: bool,
        amount: usize,
        newline: bool,
    ) -> Result<(), Box<dyn Error>> {
        use Sexp::*;

        if indent {
            write!(output, "{}", String::from_utf8(vec![b' '; amount])?)?
        }

        match self {
            True => write!(output, "true")?,
            False => write!(output, "false")?,
            RelApp(r, ev1, ev2) => write!(output, "(|{}| ev{} ev{})", r, ev1, ev2)?,
            SetApp(r, ev) => write!(output, "(|{}| ev{})", r, ev)?,
            Eq(ev1, ev2) => write!(output, "(= ev{} ev{})", ev1, ev2)?,
            Not(sexp) => {
                write!(output, "(not\n")?;
                sexp.write_to(output, true, amount + 2, false)?;
                write!(output, ")")?
            }
            And(sexps) => {
                write!(output, "(and\n")?;
                for (i, sexp) in sexps.iter().enumerate() {
                    let last = i == sexps.len() - 1;
                    sexp.write_to(output, true, amount + 2, !last)?
                }
                write!(output, ")")?
            }
            Or(sexps) => {
                write!(output, "(or\n")?;
                for (i, sexp) in sexps.iter().enumerate() {
                    let last = i == sexps.len() - 1;
                    sexp.write_to(output, true, amount + 2, !last)?
                }
                write!(output, ")")?
            }
            Implies(sexp1, sexp2) => {
                write!(output, "(=> ")?;
                sexp1.write_to(output, false, amount + 4, true)?;
                sexp2.write_to(output, true, amount + 2, false)?;
                write!(output, ")")?
            }
            Exists(v, sexp) => {
                write!(output, "(exists ((ev{} Event))\n", v)?;
                sexp.write_to(output, true, amount + 2, false)?;
                write!(output, ")")?
            }
        }

        if newline {
            write!(output, "\n")?
        }

        Ok(())
    }
}

/// `compile_set(S, ev)` compiles the given expression into a
/// Bool-kinded S-expression representing `ev`∈`S`. Returns None if
/// the expression `S` does not denote a valid set.
pub fn compile_set(exp: &Exp<Ty>, ev: EventId) -> Option<Sexp> {
    use Sexp::*;
    Some(match exp {
        Exp::Empty(_) => False,
        Exp::Id(name, _) if name == "emptyset" => False,
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
        Exp::App(_, _, _) => False,
        _ => panic!("unfinished {:?}", exp),
    })
}

/// `compile_rel(R, ev1, ev2)` compiles the given expression in a
/// Bool-typed S-expression representing (`ev1`,`ev2`)∈`R`. Returns
/// None if the expression `R` does not denote a valid relation.
pub fn compile_rel(exp: &Exp<Ty>, ev1: EventId, ev2: EventId) -> Option<Sexp> {
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
        Exp::App(_, _, _) => False,
        _ => panic!("unfinished {:?}", exp),
    })
}

/// `compile_toplevel` compiles a toplevel expression into either a
/// set or relation depending on its type. The event names are
/// implicitly `ev1` and `ev2` for relations and `ev1` for sets, which
/// is why it is only valid at the toplevel.
pub fn compile_toplevel(exp: &Exp<Ty>) -> Option<Sexp> {
    match ty_of(exp) {
        Ty::Set => compile_set(exp, 1),
        Ty::Rel => compile_rel(exp, 1, 2),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplify_nested_and() {
        use Sexp::*;
        let eq = Eq(0, 1);
        let mut sexp1 = Not(Box::new(And(vec![eq.clone(), And(vec![eq.clone(), eq.clone()])])));
        sexp1.simplify(&HashSet::new());
        let sexp2 = Not(Box::new(And(vec![eq.clone(), eq.clone(), eq.clone()])));
        assert_eq!(sexp1, sexp2)
    }

    #[test]
    fn test_simplify_nested_or() {
        use Sexp::*;
        let eq = Eq(0, 1);
        let mut sexp1 = Not(Box::new(Or(vec![eq.clone(), Or(vec![Or(vec![eq.clone(), eq.clone()]), eq.clone()])])));
        sexp1.simplify(&HashSet::new());
        let sexp2 = Not(Box::new(Or(vec![eq.clone(), eq.clone(), eq.clone(), eq.clone()])));
        assert_eq!(sexp1, sexp2)
    }

    #[test]
    fn test_simplify_double_negation() {
        use Sexp::*;
        let eq = Eq(0, 1);
        let mut sexp1 = And(vec![eq.clone(), Not(Box::new(Not(Box::new(eq.clone()))))]);
        sexp1.simplify(&HashSet::new());
        let sexp2 = And(vec![eq.clone(), eq.clone()]);
        assert_eq!(sexp1, sexp2)
    }

    #[test]
    fn test_simplify_literal_negation() {
        use Sexp::*;
        let mut sexp = Not(Box::new(Not(Box::new(True))));
        sexp.simplify(&HashSet::new());
        assert_eq!(sexp, True)
    }
}

fn exp_args_ty(exp: &Exp<Ty>) -> &'static str {
    match ty_of(exp) {
        Ty::Rel => "(Event Event)",
        Ty::Set => "(Event)",
    }
}

fn exp_params(exp: &Exp<Ty>) -> &'static str {
    match ty_of(exp) {
        Ty::Rel => "((ev1 Event) (ev2 Event))",
        Ty::Set => "((ev1 Event))",
    }
}

fn exp_args(exp: &Exp<Ty>) -> &'static str {
    match ty_of(exp) {
        Ty::Rel => "ev1 ev2",
        Ty::Set => "ev1",
    }
}

/// Compile all the definitions in a cat model.
pub fn compile_cat(output: &mut dyn Write, cat: &Cat<Ty>) -> Result<(), Box<dyn Error>> {
    let mut known_empty = HashSet::new();

    for def in &cat.defs {
        match def {
            Def::Let(LetKind::Let, letbindings) => {
                for (id, exp) in letbindings {
                    writeln!(output, "(declare-fun |{}| {} Bool)", id, exp_args_ty(&exp))?;
                    let mut sexp = compile_toplevel(exp).unwrap();
                    sexp.simplify(&known_empty);
                    if sexp.is_false() {
                        known_empty.insert(id.clone());
                    }
                    writeln!(output, "(assert (forall {}\n  (= (|{}| {})", exp_params(&exp), id, exp_args(&exp))?;
                    sexp.write_to(output, true, 4, false)?;
                    writeln!(output, ")))\n")?;
                }
            }

            _ => (),
        }
    }
    Ok(())
}
