// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
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

//! This module implements the compilation from the high-order
//! relation-algebra style expressions used by cat into first-order
//! SMT definitions, where relations are represented as functions from
//! Event × Event → Bool and sets are Event → Bool functions.

use std::borrow::Cow;
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
    Var(EventId),
    Literal(String),
    RelApp(String, EventId, EventId),
    SetApp(String, EventId),
    Or(Vec<Sexp>),
    And(Vec<Sexp>),
    Not(Box<Sexp>),
    IfThenElse(Box<Sexp>, Box<Sexp>, Box<Sexp>),
    Eq(Box<Sexp>, Box<Sexp>),
    Exists(EventId, Box<Sexp>),
    Implies(Box<Sexp>, Box<Sexp>),
}

fn eq(ev1: u32, ev2: u32) -> Sexp {
    Sexp::Eq(Box::new(Sexp::Var(ev1)), Box::new(Sexp::Var(ev2)))
}

impl Sexp {
    /// Traverse a S-expression bottom up, applying `f` to every sub-expression
    pub fn modify<F>(&mut self, f: &F)
    where
        F: Fn(&mut Self),
    {
        use Sexp::*;
        match self {
            True | False | RelApp(_, _, _) | SetApp(_, _) | Var(_) | Literal(_) => (),
            Not(sexp) | Exists(_, sexp) => sexp.modify(f),
            Implies(sexp1, sexp2) | Eq(sexp1, sexp2) => {
                sexp1.modify(f);
                sexp2.modify(f)
            }
            IfThenElse(sexp1, sexp2, sexp3) => {
                sexp1.modify(f);
                sexp2.modify(f);
                sexp3.modify(f)
            }
            And(sexps) | Or(sexps) => sexps.iter_mut().for_each(|sexp| sexp.modify(f)),
        }
        f(self)
    }

    fn is_true(&self) -> bool {
        matches!(self, Sexp::True)
    }

    fn is_false(&self) -> bool {
        matches!(self, Sexp::False)
    }

    fn is_and(&self) -> bool {
        matches!(self, Sexp::And(_))
    }

    fn flatten_and(self) -> Vec<Self> {
        if let Sexp::And(sexps) = self {
            sexps
        } else {
            vec![self]
        }
    }

    fn is_or(&self) -> bool {
        matches!(self, Sexp::Or(_))
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
                } else if sexps.len() == 1 {
                    *self = sexps[0].clone()
                } else if sexps.iter().any(|sexp| sexp.is_false()) {
                    *self = False
                } else if sexps.iter().any(|sexp| sexp.is_and()) {
                    *self = And(sexps.iter().flat_map(|sexp| sexp.clone().flatten_and()).collect())
                } else {
                    *self = And(sexps);
                }
            }

            Or(sexps) => {
                let sexps: Vec<Sexp> = sexps.drain(..).filter(|sexp| !sexp.is_false()).collect();
                if sexps.is_empty() {
                    *self = False
                } else if sexps.len() == 1 {
                    *self = sexps[0].clone()
                } else if sexps.iter().any(|sexp| sexp.is_true()) {
                    *self = True
                } else if sexps.iter().any(|sexp| sexp.is_or()) {
                    *self = Or(sexps.iter().flat_map(|sexp| sexp.clone().flatten_or()).collect())
                } else {
                    *self = Or(sexps)
                }
            }

            IfThenElse(sexp1, sexp2, sexp3) => {
                if sexp1.is_true() {
                    *self = *sexp2.clone();
                } else if sexp1.is_false() {
                    *self = *sexp3.clone();
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
                True => *self = True,
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

    pub fn is_short(&self) -> bool {
        use Sexp::*;
        matches!(self, Var(_) | Literal(_) | RelApp(_, _, _) | SetApp(_, _))
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
            Var(ev) => write!(output, "ev{}", ev)?,
            Literal(ev) => write!(output, "{}", ev)?,
            RelApp(r, ev1, ev2) => write!(output, "(|{}| ev{} ev{})", r, ev1, ev2)?,
            SetApp(r, ev) => write!(output, "(|{}| ev{})", r, ev)?,
            Eq(sexp1, sexp2) if sexp1.is_short() && sexp2.is_short() => {
                write!(output, "(= ")?;
                sexp1.write_to(output, false, 0, false)?;
                sexp2.write_to(output, true, 1, false)?;
                write!(output, ")")?
            }
            Eq(sexp1, sexp2) => {
                write!(output, "(= ")?;
                sexp1.write_to(output, false, amount + 4, true)?;
                sexp2.write_to(output, true, amount + 2, false)?;
                write!(output, ")")?
            }
            Not(sexp) => {
                writeln!(output, "(not")?;
                sexp.write_to(output, true, amount + 2, false)?;
                write!(output, ")")?
            }
            And(sexps) => {
                writeln!(output, "(and")?;
                for (i, sexp) in sexps.iter().enumerate() {
                    let last = i == sexps.len() - 1;
                    sexp.write_to(output, true, amount + 2, !last)?
                }
                write!(output, ")")?
            }
            Or(sexps) => {
                writeln!(output, "(or")?;
                for (i, sexp) in sexps.iter().enumerate() {
                    let last = i == sexps.len() - 1;
                    sexp.write_to(output, true, amount + 2, !last)?
                }
                write!(output, ")")?
            }
            IfThenElse(sexp1, sexp2, sexp3) => {
                writeln!(output, "(ite ")?;
                sexp1.write_to(output, true, amount + 2, true)?;
                sexp2.write_to(output, true, amount + 2, true)?;
                sexp3.write_to(output, true, amount + 2, false)?;
                write!(output, ")")?
            }
            Implies(sexp1, sexp2) => {
                write!(output, "(=> ")?;
                sexp1.write_to(output, false, amount + 4, true)?;
                sexp2.write_to(output, true, amount + 2, false)?;
                write!(output, ")")?
            }
            Exists(v, sexp) => {
                writeln!(output, "(exists ((ev{} Event))", v)?;
                sexp.write_to(output, true, amount + 2, false)?;
                write!(output, ")")?
            }
        }

        if newline {
            writeln!(output)?
        }

        Ok(())
    }

    pub fn write_set(&self, output: &mut dyn Write, name: &str) -> Result<(), Box<dyn Error>> {
        writeln!(output, "(define-fun {} ((ev1 Event)) Bool", name)?;
        self.write_to(output, true, 2, false)?;
        writeln!(output, ")\n")?;
        Ok(())
    }

    pub fn write_rel(&self, output: &mut dyn Write, name: &str) -> Result<(), Box<dyn Error>> {
        writeln!(output, "(declare-fun {} (Event Event) Bool)", name)?;
        writeln!(output, "(assert (forall ((ev1 Event) (ev2 Event))")?;
        writeln!(output, "(= ({} ev1 ev2) ", name)?;
        self.write_to(output, true, 2, false)?;
        writeln!(output, ")))\n")?;
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
        Exp::Id(name, _) if name == "_" => True,
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
        Exp::IdentityUnion(_) => return None,
        Exp::Inverse(_) => return None,
        Exp::App(name, x, _) if name == "range" => {
            let domain = fresh();
            Exists(domain, Box::new(compile_rel(x, domain, ev)?))
        }
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
        Exp::Id(name, _) if name == "id" => eq(ev1, ev2),
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
        Exp::Identity(x) => And(vec![compile_set(x, ev1)?, compile_set(x, ev2)?, eq(ev1, ev2)]),
        Exp::IdentityUnion(x) => Or(vec![compile_rel(x, ev1, ev2)?, eq(ev1, ev2)]),
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

fn transitive_closure_for(output: &mut dyn Write, id: &str, tc_id: &str) -> Result<(), Box<dyn Error>> {
    writeln!(output, "(declare-fun |{}| (Event Event) Bool)", tc_id)?;
    writeln!(
        output,
        "(assert (forall ((ev1 Event) (ev2 Event))\n  \
         (=> (|{}| ev1 ev2) (|{}| ev1 ev2))))",
        id, tc_id
    )?;
    writeln!(
        output,
        "(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))\n  \
         (=> (and (|{}| ev1 ev2) (|{}| ev2 ev3))\n      \
         (|{}| ev1 ev3))))",
        tc_id, tc_id, tc_id
    )?;
    Ok(())
}

fn reflexive_transitive_closure_for(output: &mut dyn Write, id: &str, rtc_id: &str) -> Result<(), Box<dyn Error>> {
    writeln!(output, "(declare-fun |{}| (Event Event) Bool)", rtc_id)?;
    writeln!(
        output,
        "(assert (forall ((ev1 Event) (ev2 Event))\n  \
         (=> (|{}| ev1 ev2) (|{}| ev1 ev2))))",
        id, rtc_id
    )?;
    writeln!(
        output,
        "(assert (forall ((ev1 Event) (ev2 Event))\n  \
         (=> (|{}| ev1 ev2) (and (|{}| ev1 ev1) (|{}| ev2 ev2)))))",
        id, rtc_id, rtc_id
    )?;
    writeln!(
        output,
        "(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))\n  \
         (=> (and (|{}| ev1 ev2) (|{}| ev2 ev3))\n      \
         (|{}| ev1 ev3))))",
        rtc_id, rtc_id, rtc_id
    )?;
    Ok(())
}

/// Compile all the definitions in a cat model.
pub fn compile_cat(output: &mut dyn Write, cat: &Cat<Ty>) -> Result<(), Box<dyn Error>> {
    let mut known_empty = HashSet::new();

    for (i, def) in cat.defs.iter().enumerate() {
        match def {
            Def::Let(letbindings) => {
                for (id, exp) in letbindings {
                    writeln!(output, "(declare-fun |{}| {} Bool)", id, exp_args_ty(exp))?;
                    let mut sexp = compile_toplevel(exp).unwrap();
                    sexp.simplify(&known_empty);
                    if sexp.is_false() {
                        known_empty.insert(id.clone());
                    }
                    writeln!(output, "(assert (forall {}\n  (= (|{}| {})", exp_params(exp), id, exp_args(exp))?;
                    sexp.write_to(output, true, 4, false)?;
                    writeln!(output, ")))\n")?;
                }
            }

            Def::Check(check, exp, id) => {
                let id = match id {
                    Some(id) => Cow::Borrowed(id),
                    None => Cow::Owned(format!("anon:{}", i)),
                };

                writeln!(output, "(define-fun |check:{}| ((ev1 Event) (ev2 Event)) Bool", id)?;
                let mut sexp = compile_toplevel(exp).unwrap();
                sexp.simplify(&known_empty);
                sexp.write_to(output, true, 2, false)?;
                writeln!(output, ")")?;

                match check {
                    Check::Empty => {
                        writeln!(output, "(assert (forall ((ev1 Event) (ev2 Event)) (not (|check:{}| ev1 ev2))))", id)?
                    }
                    Check::NonEmpty => {
                        writeln!(output, "(declare-const |ne1:{}| Event)", id)?;
                        writeln!(output, "(declare-const |ne2:{}| Event)", id)?;
                        writeln!(output, "(assert (|check:{}| |ne1:{}| |ne2:{}|))", id, id, id)?;
                    }
                    Check::Irreflexive => {
                        writeln!(output, "(assert (forall ((ev1 Event)) (not (|check:{}| ev1 ev1))))", id)?
                    }
                    Check::NonIrreflexive => {
                        writeln!(output, "(declare-const |some:{}| Event)", id)?;
                        writeln!(output, "(assert (|check:{}| |some:{}| |some:{}|))", id, id, id)?;
                    }
                    Check::Acyclic => {
                        transitive_closure_for(output, &format!("check:{}", id), &format!("acyclic:{}", id))?;
                        writeln!(output, "(assert (forall ((ev1 Event)) (not (|acyclic:{}| ev1 ev1))))", id)?;
                    }
                    Check::NonAcyclic => {
                        transitive_closure_for(output, &format!("check:{}", id), &format!("non-acyclic:{}", id))?;
                        writeln!(output, "(declare-const |some:{}| Event)", id)?;
                        writeln!(output, "(assert (|non-acyclic:{}| |some:{}| |some:{}|))", id, id, id)?;
                    }
                }

                writeln!(output)?;
            }

            Def::TClosure(id, exp) => {
                writeln!(output, "(define-fun |TC:{}| ((ev1 Event) (ev2 Event)) Bool", id)?;
                let mut sexp = compile_toplevel(exp).unwrap();
                sexp.simplify(&known_empty);
                sexp.write_to(output, true, 2, false)?;
                writeln!(output, ")")?;

                transitive_closure_for(output, &format!("TC:{}", id), id)?;
                writeln!(output)?;
            }

            Def::RTClosure(id, exp) => {
                writeln!(output, "(define-fun |RTC:{}| ((ev1 Event) (ev2 Event)) Bool", id)?;
                let mut sexp = compile_toplevel(exp).unwrap();
                sexp.simplify(&known_empty);
                sexp.write_to(output, true, 2, false)?;
                writeln!(output, ")")?;

                reflexive_transitive_closure_for(output, &format!("RTC:{}", id), id)?;
                writeln!(output)?;
            }

            _ => (),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplify_nested_and() {
        use Sexp::*;
        let eq = eq(0, 1);
        let mut sexp1 = Not(Box::new(And(vec![eq.clone(), And(vec![eq.clone(), eq.clone()])])));
        sexp1.simplify(&HashSet::new());
        let sexp2 = Not(Box::new(And(vec![eq.clone(), eq.clone(), eq.clone()])));
        assert_eq!(sexp1, sexp2)
    }

    #[test]
    fn test_simplify_nested_or() {
        use Sexp::*;
        let eq = eq(0, 1);
        let mut sexp1 = Not(Box::new(Or(vec![eq.clone(), Or(vec![Or(vec![eq.clone(), eq.clone()]), eq.clone()])])));
        sexp1.simplify(&HashSet::new());
        let sexp2 = Not(Box::new(Or(vec![eq.clone(), eq.clone(), eq.clone(), eq.clone()])));
        assert_eq!(sexp1, sexp2)
    }

    #[test]
    fn test_simplify_double_negation() {
        use Sexp::*;
        let eq = eq(0, 1);
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
