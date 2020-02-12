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

use isla_lib::concrete::{B64, BV};
use isla_lib::ir::{SharedState, Val};
use isla_lib::litmus::{Litmus, Loc, Prop};
use isla_lib::simplify::write_events_with_opts;
use isla_lib::smt::Event;

use isla_cat::smt::Sexp;

use crate::footprint_analysis::{addr_dep, ctrl_dep, data_dep, Footprint};

// First we define an iterator over all candidate executions

pub struct Candidates<'a> {
    index: Vec<usize>,
    max_index: Vec<usize>,
    threads: &'a [Vec<Vec<Event<B64>>>],
    out_of_bounds: bool,
}

impl<'a> Candidates<'a> {
    pub fn new(threads: &'a [Vec<Vec<Event<B64>>>]) -> Self {
        Candidates {
            index: vec![0; threads.len()],
            max_index: threads.iter().map(|t| t.len()).collect(),
            threads,
            out_of_bounds: !threads.iter().all(|t| !t.is_empty()),
        }
    }

    pub fn total(&self) -> usize {
        if self.threads.is_empty() {
            0
        } else {
            self.max_index.iter().product()
        }
    }
}

fn increment_index(index: &mut [usize], max_index: &[usize], carry: usize) -> bool {
    if carry == index.len() {
        return true;
    }

    index[carry] += 1;
    if index[carry] == max_index[carry] {
        index[carry] = 0;
        increment_index(index, max_index, carry + 1)
    } else {
        false
    }
}

impl<'a> Iterator for Candidates<'a> {
    type Item = Vec<&'a [Event<B64>]>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.out_of_bounds {
            None
        } else {
            let mut result = Vec::with_capacity(self.threads.len());
            self.threads.iter().zip(self.index.iter()).for_each(|(thread, i)| result.push(thread[*i].as_ref()));
            self.out_of_bounds = increment_index(&mut self.index, &self.max_index, 0);
            Some(result)
        }
    }
}

pub struct Pairs<'a, A> {
    index: (usize, usize),
    slice: &'a [A],
}

impl<'a, A> Pairs<'a, A> {
    fn from_slice(slice: &'a [A]) -> Self {
        Pairs { index: (0, 0), slice }
    }
}

impl<'a, A> Iterator for Pairs<'a, A> {
    type Item = (&'a A, &'a A);

    fn next(&mut self) -> Option<Self::Item> {
        self.index.1 += 1;
        if self.index.1 > self.slice.len() {
            self.index.1 = 1;
            self.index.0 += 1;
        }
        if self.index.0 >= self.slice.len() {
            return None;
        }
        Some((&self.slice[self.index.0], &self.slice[self.index.1 - 1]))
    }
}

#[derive(Debug)]
struct AxEvent<'a> {
    opcode: B64,
    po: usize,
    thread_id: usize,
    name: String,
    base: &'a Event<B64>,
}

fn is_write(ev: &AxEvent) -> bool {
    ev.base.is_memory_write()
}

fn is_read(ev: &AxEvent) -> bool {
    ev.base.is_memory_read()
}

fn rmw(_ev1: &AxEvent, _ev2: &AxEvent) -> bool {
    false
}

fn amo(_ev1: &AxEvent, _ev2: &AxEvent) -> bool {
    false
}

fn univ(_: &AxEvent, _: &AxEvent) -> bool {
    true
}

fn disjoint(ev1: &AxEvent, ev2: &AxEvent) -> bool {
    ev1.po != ev2.po || ev1.thread_id != ev2.thread_id
}

fn po(ev1: &AxEvent, ev2: &AxEvent) -> bool {
    ev1.po < ev2.po && ev1.thread_id == ev2.thread_id
}

fn internal(ev1: &AxEvent, ev2: &AxEvent) -> bool {
    ev1.po != ev2.po && ev1.thread_id == ev2.thread_id
}

fn external(ev1: &AxEvent, ev2: &AxEvent) -> bool {
    ev1.po != ev2.po && ev1.thread_id != ev2.thread_id
}

fn addr(ev1: &AxEvent, ev2: &AxEvent, thread_opcodes: &[Vec<B64>], footprints: &HashMap<B64, Footprint>) -> bool {
    po(ev1, ev2) && addr_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
}

fn data(ev1: &AxEvent, ev2: &AxEvent, thread_opcodes: &[Vec<B64>], footprints: &HashMap<B64, Footprint>) -> bool {
    po(ev1, ev2) && data_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
}

fn ctrl(ev1: &AxEvent, ev2: &AxEvent, thread_opcodes: &[Vec<B64>], footprints: &HashMap<B64, Footprint>) -> bool {
    po(ev1, ev2) && ctrl_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
}

fn address<'a>(ev: &'a AxEvent) -> Option<&'a Val<B64>> {
    match ev.base {
        Event::ReadMem { address, .. } | Event::WriteMem { address, .. } => Some(address),
        _ => None,
    }
}

fn read_value<'a>(ev: &'a AxEvent) -> Option<(&'a Val<B64>, u32)> {
    match ev.base {
        Event::ReadMem { value, bytes, .. } => Some((value, *bytes)),
        _ => None,
    }
}

fn write_data<'a>(ev: &'a AxEvent) -> Option<&'a Val<B64>> {
    match ev.base {
        Event::WriteMem { data, .. } => Some(data),
        _ => None,
    }
}

fn same_location(ev1: &AxEvent, ev2: &AxEvent) -> Sexp {
    use Sexp::*;
    match (address(ev1), address(ev2)) {
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

fn read_write_pair(ev1: &AxEvent, ev2: &AxEvent) -> Sexp {
    use Sexp::*;
    match (write_data(ev1), read_value(ev2)) {
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

fn read_zero(ev: &AxEvent) -> Sexp {
    use Sexp::*;
    match read_value(ev) {
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

type BasicRel = fn(&AxEvent, &AxEvent) -> bool;

fn smt_basic_rel(rel: BasicRel, events: &[AxEvent]) -> Sexp {
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

fn smt_condition_rel(rel: BasicRel, events: &[AxEvent], f: fn(&AxEvent, &AxEvent) -> Sexp) -> Sexp {
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

type DepRel = fn(&AxEvent, &AxEvent, &[Vec<B64>], &HashMap<B64, Footprint>) -> bool;

fn smt_dep_rel(
    rel: DepRel,
    events: &[AxEvent],
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

fn smt_set(set: fn(&AxEvent) -> bool, events: &[AxEvent]) -> Sexp {
    use Sexp::*;
    let mut deps = Vec::new();
    for ev in events.iter().filter(|ev| set(ev)) {
        deps.push(Eq(Box::new(Var(1)), Box::new(Literal(ev.name.to_string()))))
    }
    let mut sexp = Or(deps);
    sexp.simplify(&HashSet::new());
    sexp
}

fn smt_condition_set(set: fn(&AxEvent) -> Sexp, events: &[AxEvent]) -> Sexp {
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

pub fn prop_to_smt(prop: &Prop, final_writes: &HashMap<(u32, usize), &Val<B64>>) -> String {
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

pub fn smt_candidate(
    output: &mut dyn Write,
    candidate: &[&[Event<B64>]],
    litmus: &Litmus,
    footprints: &HashMap<B64, Footprint>,
    shared_state: &SharedState<B64>,
) -> Result<(), Box<dyn Error>> {
    // For each candidate execution build a list of events, containing
    // the instruction opcode associated with the event, the thread
    // id, a string symbol for the event in the SMT problem, and
    // finally the event itself.
    let mut events: Vec<AxEvent> = Vec::new();
    // We also need a vector of po-ordered instruction opcodes for each thread.
    let mut thread_opcodes: Vec<Vec<B64>> = vec![Vec::new(); candidate.len()];
    // The final write for each register in each thread
    let mut final_writes: HashMap<(u32, usize), &Val<B64>> = HashMap::new();

    for (tid, thread) in candidate.iter().enumerate() {
        writeln!(output, "\n; === THREAD {} ===", tid)?;
        write_events_with_opts(output, thread, &shared_state.symtab, true, true);

        for (po, cycle) in thread.split(|ev| ev.is_cycle()).skip(1).enumerate() {
            let mut cycle_events: Vec<(usize, String, &Event<B64>)> = Vec::new();
            let mut cycle_instr: Option<B64> = None;

            for (eid, event) in cycle.iter().enumerate() {
                match event {
                    Event::Instr(Val::Bits(bv)) => {
                        if cycle_instr.is_none() {
                            thread_opcodes[tid].push(*bv);
                            cycle_instr = Some(*bv)
                        } else {
                            panic!(
                                "Fetch-execute-decode cycle has multiple instructions! {:?} and {:?}",
                                bv, cycle_instr
                            )
                        }
                    }
                    Event::ReadMem { .. } => cycle_events.push((tid, format!("R{}_{}_{}", po, eid, tid), event)),
                    Event::WriteMem { .. } => cycle_events.push((tid, format!("W{}_{}_{}", po, eid, tid), event)),
                    Event::WriteReg(reg, _, val) => {
                        final_writes.insert((*reg, tid), val);
                    }
                    _ => (),
                }
            }

            for (tid, evid, ev) in cycle_events {
                events.push(AxEvent {
                    opcode: cycle_instr.expect("Every fetch-execute-decode cycle must have an instruction!"),
                    po,
                    thread_id: tid,
                    name: evid,
                    base: ev,
                })
            }
        }
    }

    writeln!(output, "\n\n; === FINAL ASSERTION ===\n")?;
    writeln!(output, "(assert {})\n", prop_to_smt(&litmus.final_assertion, &final_writes))?;

    writeln!(output, "; === EVENTS ===\n")?;
    write!(output, "(declare-datatypes ((Event 0))\n  ((")?;
    for ev in &events {
        write!(output, "({}) ", ev.name)?;
    }
    writeln!(output, "(IW))))")?;

    smt_set(is_read, &events).write_set(output, "R")?;
    smt_set(is_write, &events).write_set(output, "W")?;
    smt_condition_set(read_zero, &events).write_set(output, "r-zero")?;
    smt_basic_rel(rmw, &events).write_rel(output, "rmw")?;
    smt_basic_rel(amo, &events).write_rel(output, "amo")?;

    writeln!(output, "; === BASIC RELATIONS ===\n")?;
    smt_basic_rel(po, &events).write_rel(output, "po")?;
    smt_basic_rel(internal, &events).write_rel(output, "int")?;
    smt_basic_rel(external, &events).write_rel(output, "ext")?;
    smt_condition_rel(disjoint, &events, same_location).write_rel(output, "loc")?;
    smt_condition_rel(po, &events, same_location).write_rel(output, "po-loc")?;
    smt_condition_rel(univ, &events, read_write_pair).write_rel(output, "rw-pair")?;
    smt_dep_rel(addr, &events, &thread_opcodes, footprints).write_rel(output, "addr")?;
    smt_dep_rel(data, &events, &thread_opcodes, footprints).write_rel(output, "data")?;
    smt_dep_rel(ctrl, &events, &thread_opcodes, footprints).write_rel(output, "ctrl")?;

    writeln!(output, "; === COMMON SMTLIB ===\n")?;
    writeln!(output, "{}", COMMON_SMTLIB)?;

    writeln!(output, "; === CAT ===\n")?;

    Ok(())
}
