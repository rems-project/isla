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

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::io::Write;

use isla_lib::axiomatic::relations::*;
use isla_lib::axiomatic::{AxEvent, ExecutionInfo, Pairs};
use isla_lib::concrete::{B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::footprint_analysis::{addr_dep, ctrl_dep, data_dep, Footprint};
use isla_lib::ir::{SharedState, Val};
use isla_lib::litmus::{Litmus, Loc, Prop};
use isla_lib::simplify::write_events_with_opts;
use isla_lib::smt::Event;

use isla_cat::smt::Sexp;

fn same_location(ev1: &AxEvent<B64>, ev2: &AxEvent<B64>) -> Sexp {
    use Sexp::*;
    match (ev1.address(), ev2.address()) {
        (Some(Val::Symbolic(sym1)), Some(Val::Symbolic(sym2))) => {
            if sym1 == sym2 {
                True
            } else {
                Literal(format!("(= v{} v{})", sym1, sym2))
            }
        }
        (Some(Val::Bits(bv)), Some(Val::Symbolic(sym))) | (Some(Val::Symbolic(sym)), Some(Val::Bits(bv))) => {
            Literal(format!("(= v{} {})", sym, bv))
        }
        (Some(Val::Bits(bv1)), Some(Val::Bits(bv2))) => {
            if bv1 == bv2 {
                True
            } else {
                Literal(format!("(= {} {})", bv1, bv2))
            }
        }
        (_, _) => False,
    }
}

fn read_write_pair(ev1: &AxEvent<B64>, ev2: &AxEvent<B64>) -> Sexp {
    use Sexp::*;
    match (ev1.write_data(), ev2.read_value()) {
        (Some(Val::Symbolic(sym1)), Some((Val::Symbolic(sym2), _))) => {
            if sym1 == sym2 {
                True
            } else {
                Literal(format!("(= v{} v{})", sym1, sym2))
            }
        }
        (Some(Val::Bits(bv)), Some((Val::Symbolic(sym), _))) | (Some(Val::Symbolic(sym)), Some((Val::Bits(bv), _))) => {
            Literal(format!("(= v{} {})", sym, bv))
        }
        (Some(Val::Bits(bv1)), Some((Val::Bits(bv2), _))) => {
            if bv1 == bv2 {
                True
            } else {
                Literal(format!("(= {} {})", bv1, bv2))
            }
        }
        (_, _) => False,
    }
}

fn read_zero(ev: &AxEvent<B64>) -> Sexp {
    use Sexp::*;
    match ev.read_value() {
        Some((Val::Symbolic(sym), bytes)) => {
            let bv = B64::new(0, 8 * bytes);
            Literal(format!("(= v{} {})", sym, bv))
        }
        Some((Val::Bits(bv), _)) => {
            if bv.bits == 0 {
                True
            } else {
                False
            }
        }
        _ => False,
    }
}

type BasicRel = fn(&AxEvent<B64>, &AxEvent<B64>) -> bool;

fn smt_basic_rel(rel: BasicRel, events: &[AxEvent<B64>]) -> Sexp {
    use Sexp::*;
    let mut deps = Vec::new();
    for (ev1, ev2) in Pairs::from_slice(&events).filter(|(ev1, ev2)| rel(ev1, ev2)) {
        deps.push(And(vec![
            Eq(Box::new(Var(1)), Box::new(Literal(ev1.name.to_string()))),
            Eq(Box::new(Var(2)), Box::new(Literal(ev2.name.to_string()))),
        ]))
    }
    let mut sexp = Or(deps);
    sexp.simplify(&HashSet::new());
    sexp
}

fn smt_condition_rel(rel: BasicRel, events: &[AxEvent<B64>], f: fn(&AxEvent<B64>, &AxEvent<B64>) -> Sexp) -> Sexp {
    use Sexp::*;
    let mut deps = Vec::new();
    for (ev1, ev2) in Pairs::from_slice(&events).filter(|(ev1, ev2)| rel(ev1, ev2)) {
        deps.push(And(vec![
            Eq(Box::new(Var(1)), Box::new(Literal(ev1.name.to_string()))),
            Eq(Box::new(Var(2)), Box::new(Literal(ev2.name.to_string()))),
            f(ev1, ev2),
        ]))
    }
    let mut sexp = Or(deps);
    sexp.simplify(&HashSet::new());
    sexp
}

fn smt_dep_rel(
    rel: DepRel<B64>,
    events: &[AxEvent<B64>],
    thread_opcodes: &[Vec<B64>],
    footprints: &HashMap<B64, Footprint>,
) -> Sexp {
    use Sexp::*;
    let mut deps = Vec::new();
    for (ev1, ev2) in Pairs::from_slice(&events).filter(|(ev1, ev2)| rel(ev1, ev2, &thread_opcodes, footprints)) {
        deps.push(And(vec![
            Eq(Box::new(Var(1)), Box::new(Literal(ev1.name.to_string()))),
            Eq(Box::new(Var(2)), Box::new(Literal(ev2.name.to_string()))),
        ]))
    }
    let mut sexp = Or(deps);
    sexp.simplify(&HashSet::new());
    sexp
}

fn smt_set<F>(set: F, events: &[AxEvent<B64>]) -> Sexp
where
    F: Fn(&AxEvent<B64>) -> bool,
{
    use Sexp::*;
    let mut deps = Vec::new();
    for ev in events.iter().filter(|ev| set(ev)) {
        deps.push(Eq(Box::new(Var(1)), Box::new(Literal(ev.name.to_string()))))
    }
    let mut sexp = Or(deps);
    sexp.simplify(&HashSet::new());
    sexp
}

fn smt_condition_set<F>(set: F, events: &[AxEvent<B64>]) -> Sexp
where
    F: Fn(&AxEvent<B64>) -> Sexp,
{
    use Sexp::*;
    let mut deps = Vec::new();
    for ev in events.iter() {
        deps.push(And(vec![Eq(Box::new(Var(1)), Box::new(Literal(ev.name.to_string()))), set(ev)]))
    }
    let mut sexp = Or(deps);
    sexp.simplify(&HashSet::new());
    sexp
}

fn loc_to_smt(loc: &Loc, final_writes: &HashMap<(u32, usize), &Val<B64>>) -> String {
    use Loc::*;
    match loc {
        Register { reg, thread_id } => match final_writes.get(&(*reg, *thread_id)) {
            Some(Val::Symbolic(sym)) => format!("v{}", sym),
            Some(Val::Bits(bv)) => format!("{}", bv),
            Some(_) => unreachable!(),
            None => "#x000000000000DEAD".to_string(),
        },
        _ => unreachable!(),
    }
}

fn prop_to_smt(prop: &Prop<B64>, final_writes: &HashMap<(u32, usize), &Val<B64>>) -> String {
    use Prop::*;
    match prop {
        EqLoc(loc, bv) => format!("(= {} {})", loc_to_smt(loc, final_writes), bv),
        And(props) => {
            let mut conjs = String::new();
            for prop in props {
                conjs = format!("{} {}", conjs, prop_to_smt(prop, final_writes))
            }
            format!("(and{})", conjs)
        }
        _ => unreachable!(),
    }
}

static COMMON_SMTLIB: &str = include_str!("smt_events.smt2");

pub fn smt_of_candidate(
    output: &mut dyn Write,
    exec: &ExecutionInfo<B64>,
    litmus: &Litmus<B64>,
    footprints: &HashMap<B64, Footprint>,
    shared_state: &SharedState<B64>,
    isa_config: &ISAConfig<B64>,
) -> Result<(), Box<dyn Error>> {
    let events = &exec.events;

    writeln!(output, "\n\n; === FINAL ASSERTION ===\n")?;
    writeln!(output, "(assert {})\n", prop_to_smt(&litmus.final_assertion, &exec.final_writes))?;

    writeln!(output, "; === EVENTS ===\n")?;
    write!(output, "(declare-datatypes ((Event 0))\n  ((")?;
    for ev in &exec.events {
        write!(output, "({}) ", ev.name)?;
    }
    writeln!(output, "(IW))))")?;

    smt_set(is_read, events).write_set(output, "R")?;
    smt_set(is_write, events).write_set(output, "W")?;
    smt_condition_set(read_zero, events).write_set(output, "r-zero")?;
    smt_basic_rel(rmw, events).write_rel(output, "rmw")?;
    smt_basic_rel(amo, events).write_rel(output, "amo")?;

    writeln!(output, "; === BASIC RELATIONS ===\n")?;
    smt_basic_rel(po, events).write_rel(output, "po")?;
    smt_basic_rel(internal, events).write_rel(output, "int")?;
    smt_basic_rel(external, events).write_rel(output, "ext")?;
    smt_condition_rel(disjoint, events, same_location).write_rel(output, "loc")?;
    smt_condition_rel(po, events, same_location).write_rel(output, "po-loc")?;
    smt_condition_rel(univ, events, read_write_pair).write_rel(output, "rw-pair")?;
    smt_dep_rel(addr, events, &exec.thread_opcodes, footprints).write_rel(output, "addr")?;
    smt_dep_rel(data, events, &exec.thread_opcodes, footprints).write_rel(output, "data")?;
    smt_dep_rel(ctrl, events, &exec.thread_opcodes, footprints).write_rel(output, "ctrl")?;

    writeln!(output, "; === COMMON SMTLIB ===\n")?;
    writeln!(output, "{}", COMMON_SMTLIB)?;

    writeln!(output, "; === BARRIERS ===\n")?;

    for (barrier_kind, name) in isa_config.barriers.iter() {
        let (bk, _) = shared_state.enum_members.get(&barrier_kind).unwrap();
        smt_set(|ev| ev.base.has_barrier_kind(*bk), events).write_set(output, name)?
    }

    writeln!(output, "; === CAT ===\n")?;

    Ok(())
}
