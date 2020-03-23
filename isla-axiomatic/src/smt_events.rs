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

use isla_lib::concrete::BV;
use isla_lib::config::ISAConfig;
use isla_lib::ir::{Name, SharedState, Val};
use isla_lib::smt::Event;

use isla_cat::smt::Sexp;

use crate::axiomatic::relations::*;
use crate::axiomatic::{AxEvent, ExecutionInfo, Pairs};
use crate::footprint_analysis::Footprint;
use crate::litmus::{Litmus, Loc, Prop, opcode_from_objdump};

fn smt_bitvec<B: BV>(val: &Val<B>) -> String {
    match val {
        Val::Symbolic(v) => format!("v{}", v),
        Val::Bits(bv) => format!("{}", bv),
        _ => panic!("Not bitvector value passed to smt_bitvec"),
    }
}

fn same_location<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> Sexp {
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

fn read_write_pair<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> Sexp {
    use Sexp::*;
    match (ev2.read_value(), ev1.write_data()) {
        (Some((Val::Symbolic(sym1), _rbytes)), Some((Val::Symbolic(sym2), _wbytes))) => {
            if sym1 == sym2 {
                True
            } else {
                Literal(format!("(= v{} v{})", sym1, sym2))
            }
        }
        (Some((Val::Bits(bv), rbytes)), Some((Val::Symbolic(sym), wbytes))) => {
            if rbytes == wbytes {
                Literal(format!("(= {} v{})", bv, sym))
            } else if rbytes > wbytes {
                Literal(format!("(= {} ((_ zero_extend {}) v{}))", bv, rbytes * 8 - wbytes * 8, sym))
            } else {
                Literal(format!("(= {} ((_ extract {} 0) v{}))", bv, rbytes * 8 - 1, sym))
            }
        }
        (Some((Val::Symbolic(sym), rbytes)), Some((Val::Bits(bv), wbytes))) => {
            if rbytes == wbytes {
                Literal(format!("(= v{} {})", sym, bv))
            } else if rbytes > wbytes {
                Literal(format!("(= v{} {})", sym, bv.zero_extend(rbytes * 8)))
            } else {
                Literal(format!("(= v{} {})", sym, bv.extract(rbytes * 8 - 1, 0).unwrap()))
            }
        }
        (Some((Val::Bits(bv1), _rbytes)), Some((Val::Bits(bv2), _wbytes))) => {
            if bv1 == bv2 {
                True
            } else {
                Literal(format!("(= {} {})", bv1, bv2))
            }
        }
        (_, _) => False,
    }
}

fn read_initial_symbolic<B: BV>(sym: u32, addr1: &Val<B>, bytes: u32, litmus: &Litmus<B>) -> Sexp {
    let mut expr = "".to_string();
    let mut ites = 0;

    for (sym_loc, value) in litmus.symbolic_locations.iter() {
        let addr2 = litmus.symbolic_addrs.get(sym_loc).expect("Could not find symbolic location");
        expr = format!(
            "{}(ite (= {} {}) (= v{} {}) ",
            expr,
            smt_bitvec(addr1),
            B::new(*addr2, 64),
            sym,
            B::new(*value, 8 * bytes)
        );
        ites += 1
    }

    expr = format!("{}(= v{} {})", expr, sym, B::new(0, 8 * bytes));

    for _ in 0..ites {
        expr = format!("{})", expr)
    }

    Sexp::Literal(expr)
}

fn read_initial_concrete<B: BV>(bv: B, addr1: &Val<B>, litmus: &Litmus<B>) -> Sexp {
    let mut expr = "".to_string();
    let mut ites = 0;

    for (sym_loc, value) in litmus.symbolic_locations.iter() {
        let addr2 = litmus.symbolic_addrs.get(sym_loc).expect("Could not find symbolic location");
        expr = format!(
            "{}(ite (= {} {}) {} ",
            expr,
            smt_bitvec(addr1),
            B::new(*addr2, 64),
            if bv.bits() == *value { "true" } else { "false " }
        );
        ites += 1
    }

    expr = format!("{}{}", expr, if bv.bits() == 0 { "true" } else { "false" });

    for _ in 0..ites {
        expr = format!("{})", expr)
    }

    Sexp::Literal(expr)
}

fn initial_write_values<B: BV>(addr_name: &str, width: u32, litmus: &Litmus<B>) -> String {
    let mut expr = "".to_string();
    let mut ites = 0;

    for (sym_loc, value) in litmus.symbolic_locations.iter() {
        let addr = litmus.symbolic_addrs.get(sym_loc).expect("Could not find symbolic location");
        expr = format!("{}(ite (= {} {}) {} ", expr, addr_name, B::new(*addr, 64), B::new(*value, width));
        ites += 1
    }

    expr = format!("{}{}", expr, B::zeros(width));

    for _ in 0..ites {
        expr = format!("{})", expr)
    }

    expr
}

/// Some symbolic locations can have custom initial values, otherwise
/// they are always read as zero.
fn read_initial<B: BV>(ev: &AxEvent<B>, litmus: &Litmus<B>) -> Sexp {
    use Sexp::*;
    match (ev.read_value(), ev.address()) {
        (Some((Val::Symbolic(sym), bytes)), Some(addr)) => read_initial_symbolic(*sym, addr, bytes, litmus),
        (Some((Val::Bits(bv), _)), Some(addr)) => read_initial_concrete(*bv, addr, litmus),
        _ => False,
    }
}

/// [ifetch_initial] checks if a ifetch is a valid fetch from the
/// initial state, using the opcodes in the objdump. It also performs
/// the same check as [ifetch_match], so they do not need to be used
/// together.
fn ifetch_initial<B: BV>(ev: &AxEvent<B>, litmus: &Litmus<B>) -> Sexp {
    use Sexp::*;
    match ev.address() {
        Some(Val::Bits(addr)) => {
            if let Some(opcode) = opcode_from_objdump(*addr, &litmus.objdump) {
                match ev.read_value() {
                    Some((Val::Symbolic(sym), _)) =>
                        Literal(format!("(= v{} {} {})", sym, opcode, ev.opcode)),
                    Some((Val::Bits(bv), _)) =>
                        Literal(format!("(= {} {} {})", bv, opcode, ev.opcode)),
                    _ => False,
                }
            } else {
                False
            }
        }
        _ => False,
    }
}

/// [ifetch_match] checks if a read event reads the same value as the
/// events opcode, which is required for a valid ifetch.
fn ifetch_match<B: BV>(ev: &AxEvent<B>) -> Sexp {
    use Sexp::*;
    match ev.read_value() {
        Some((Val::Symbolic(sym), _)) =>
            Literal(format!("(= v{} {})", sym, ev.opcode)),
        Some((Val::Bits(bv), _)) =>
            Literal(format!("(= {} {})", bv, ev.opcode)),
        _ => False,
    }
}

fn smt_basic_rel<B, F>(rel: F, events: &[AxEvent<B>]) -> Sexp
where
    B: BV,
    F: Fn(&AxEvent<B>, &AxEvent<B>) -> bool,
{
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

fn smt_condition_rel<B, F>(rel: F, events: &[AxEvent<B>], f: fn(&AxEvent<B>, &AxEvent<B>) -> Sexp) -> Sexp
where
    B: BV,
    F: Fn(&AxEvent<B>, &AxEvent<B>) -> bool,
{
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

fn smt_dep_rel<B: BV>(
    rel: DepRel<B>,
    events: &[AxEvent<B>],
    thread_opcodes: &[Vec<B>],
    footprints: &HashMap<B, Footprint>,
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

fn smt_set<B: BV, F>(set: F, events: &[AxEvent<B>]) -> Sexp
where
    F: Fn(&AxEvent<B>) -> bool,
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

fn smt_condition_set<B: BV, F>(set: F, events: &[AxEvent<B>]) -> Sexp
where
    F: Fn(&AxEvent<B>) -> Sexp,
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

fn eq_loc_to_smt<B: BV>(loc: &Loc, bv: B, final_writes: &HashMap<(Name, usize), &Val<B>>) -> String {
    use Loc::*;
    match loc {
        Register { reg, thread_id } => match final_writes.get(&(*reg, *thread_id)) {
            Some(Val::Symbolic(sym)) => format!("(= v{} {})", sym, bv),
            Some(Val::Bits(reg_bv)) => format!("(= {} {})", reg_bv, bv),
            Some(_) => unreachable!(),
            None => format!("(= #x000000000000DEAD {})", bv),
        },
        LastWriteTo { address, bytes } => format!("(last_write_to_{} {} {})", bytes * 8, B::new(*address, 64), bv),
    }
}

fn prop_to_smt<B: BV>(prop: &Prop<B>, final_writes: &HashMap<(Name, usize), &Val<B>>) -> String {
    use Prop::*;
    match prop {
        EqLoc(loc, bv) => eq_loc_to_smt(loc, *bv, final_writes),
        And(props) => {
            let mut conjs = String::new();
            for prop in props {
                conjs = format!("{} {}", conjs, prop_to_smt(prop, final_writes))
            }
            format!("(and{})", conjs)
        }
        Or(props) => {
            let mut disjs = String::new();
            for prop in props {
                disjs = format!("{} {}", disjs, prop_to_smt(prop, final_writes))
            }
            format!("(or{})", disjs)
        }
        Implies(prop1, prop2) => {
            format!("(=> {} {})", prop_to_smt(prop1, final_writes), prop_to_smt(prop2, final_writes))
        }
        Not(prop) => format!("(not {})", prop_to_smt(prop, final_writes)),
        True => "true".to_string(),
        False => "false".to_string(),
    }
}

fn subst_template<T: AsRef<str>, R: AsRef<str>>(template: T, subst: &str, replace: R) -> String {
    use regex::Regex;
    let subst_re = Regex::new(&format!(r"\${}", subst)).unwrap();
    subst_re.replace_all(template.as_ref(), replace.as_ref()).to_string()
}

fn ifetch_pair<B: BV>(rk_ifetch: usize, ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
    ev1.base.has_read_kind(rk_ifetch) && ev2.base.has_read_kind(rk_ifetch)
}

fn ifetch_to_execute<B: BV>(rk_ifetch: usize, ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
    ev1.base.has_read_kind(rk_ifetch)
        && !ev2.base.has_read_kind(rk_ifetch)
        && ev1.po == ev2.po
        && ev1.thread_id == ev2.thread_id
}

static COMMON_SMTLIB: &str = include_str!("smt_events.smt2");

static IFETCH_SMTLIB: &str = include_str!("ifetch.smt2");

static LAST_WRITE_TO: &str = include_str!("last_write_to.smt2");

pub fn smt_of_candidate<B: BV>(
    output: &mut dyn Write,
    exec: &ExecutionInfo<B>,
    litmus: &Litmus<B>,
    ignore_ifetch: bool,
    footprints: &HashMap<B, Footprint>,
    shared_state: &SharedState<B>,
    isa_config: &ISAConfig<B>,
) -> Result<(), Box<dyn Error>> {
    let events = &exec.events;

    writeln!(output, "\n\n; === EVENTS ===\n")?;
    write!(output, "(declare-datatypes ((Event 0))\n  ((")?;
    for ev in &exec.events {
        write!(output, "({}) ", ev.name)?;
    }
    writeln!(output, "(IW))))")?;

    let mut all_write_widths = HashSet::new();
    // Always make sure we have at least one width to avoid generating invalid SMT for writes
    all_write_widths.insert(&4);
    for ev in &exec.events {
        if let Event::WriteMem { bytes, .. } = ev.base {
            all_write_widths.insert(bytes);
        }
    }
    for &width in all_write_widths.iter() {
        assert!(*width > 0);
        writeln!(output, "(define-fun val_of_{} ((ev Event)) (_ BitVec {})", width * 8, width * 8)?;
        let mut ites: usize = 0;
        for ev in events {
            match ev.base {
                Event::WriteMem { bytes, data, .. } if bytes == width => {
                    writeln!(output, "  (ite (= ev {}) {}", ev.name, smt_bitvec(data))?;
                    ites += 1
                }
                _ => (),
            }
        }
        write!(output, "  {}", B::zeros(width * 8))?;
        for _ in 0..ites {
            write!(output, ")")?
        }
        writeln!(output, ")\n")?
    }

    {
        writeln!(output, "(define-fun addr_of ((ev Event)) (_ BitVec 64)")?;
        let mut ites: usize = 0;
        for ev in events {
            match ev.base {
                Event::WriteMem { address, .. } | Event::ReadMem { address, .. } => {
                    writeln!(output, "  (ite (= ev {}) {}", ev.name, smt_bitvec(address))?;
                    ites += 1
                }
                _ => (),
            }
        }
        write!(output, "  #x0000000000000000")?;
        for _ in 0..ites {
            write!(output, ")")?
        }
        writeln!(output, ")\n")?
    }

    let rk_ifetch = shared_state.enum_member("Read_ifetch").unwrap();

    let rk_acquire = shared_state.enum_member("Read_acquire").unwrap();
    let rk_exclusive_acquire = shared_state.enum_member("Read_exclusive_acquire").unwrap();
    let wk_release = shared_state.enum_member("Write_release").unwrap();
    let wk_exclusive_release = shared_state.enum_member("Write_exclusive_release").unwrap();

    smt_set(|ev| (is_read(ev) && !ev.base.has_read_kind(rk_ifetch)), events).write_set(output, "R")?;
    smt_set(|ev| ev.base.has_read_kind(rk_ifetch), events).write_set(output, "IF")?;
    smt_set(is_write, events).write_set(output, "W")?;

    smt_set(is_cache_op, events).write_set(output, "C")?;
    
    smt_set(|ev| ev.base.has_read_kind(rk_acquire) || ev.base.has_read_kind(rk_exclusive_acquire), events)
        .write_set(output, "A")?;
    smt_set(|ev| ev.base.has_write_kind(wk_release) || ev.base.has_write_kind(wk_exclusive_release), events)
        .write_set(output, "L")?;

    smt_condition_set(|ev| read_initial(ev, litmus), events).write_set(output, "r-initial")?;
    if !ignore_ifetch {
        smt_condition_set(ifetch_match, events).write_set(output, "ifetch-match")?;
        smt_condition_set(|ev| ifetch_initial(ev, litmus), events).write_set(output, "ifetch-initial")?;
    }
    
    smt_basic_rel(amo, events).write_rel(output, "amo")?;

    writeln!(output, "; === BASIC RELATIONS ===\n")?;

    if ignore_ifetch {
        smt_basic_rel(po, events).write_rel(output, "po")?;
    } else {
        smt_basic_rel(|ev1, ev2| po(ev1, ev2) && ifetch_pair(rk_ifetch, ev1, ev2), events).write_rel(output, "fpo")?;
        smt_basic_rel(|ev1, ev2| po(ev1, ev2) && !ifetch_pair(rk_ifetch, ev1, ev2), events).write_rel(output, "po")?;
        smt_basic_rel(|ev1, ev2| ifetch_to_execute(rk_ifetch, ev1, ev2), events).write_rel(output, "fe")?
    }

    smt_basic_rel(internal, events).write_rel(output, "int")?;
    smt_basic_rel(external, events).write_rel(output, "ext")?;
    smt_condition_rel(disjoint, events, same_location).write_rel(output, "loc")?;
    smt_condition_rel(po, events, same_location).write_rel(output, "po-loc")?;
    smt_condition_rel(univ, events, read_write_pair).write_rel(output, "rw-pair")?;
    smt_dep_rel(addr, events, &exec.thread_opcodes, footprints).write_rel(output, "addr")?;
    smt_dep_rel(data, events, &exec.thread_opcodes, footprints).write_rel(output, "data")?;
    smt_dep_rel(ctrl, events, &exec.thread_opcodes, footprints).write_rel(output, "ctrl")?;
    smt_dep_rel(rmw, events, &exec.thread_opcodes, footprints).write_rel(output, "rmw")?;

    writeln!(output, "; === COMMON SMTLIB ===\n")?;
    writeln!(output, "{}", COMMON_SMTLIB)?;

    if !ignore_ifetch {
        writeln!(output, "{}", IFETCH_SMTLIB)?;
    }

    for &width in all_write_widths.iter() {
        let lwt = subst_template(LAST_WRITE_TO, "INITIAL", initial_write_values("addr", 64, &litmus));
        let lwt = subst_template(lwt, "LEN_MINUS_1", format!("{}", width * 8 - 1));
        let lwt = subst_template(lwt, "LEN", format!("{}", width * 8));
        writeln!(output, "{}", lwt)?;
    }

    writeln!(output, "; === FINAL ASSERTION ===\n")?;
    writeln!(output, "(assert {})\n", prop_to_smt(&litmus.final_assertion, &exec.final_writes))?;

    writeln!(output, "; === BARRIERS ===\n")?;

    for (barrier_kind, name) in isa_config.barriers.iter() {
        let (bk, _) = shared_state.enum_members.get(&barrier_kind).unwrap();
        smt_set(|ev| ev.base.has_barrier_kind(*bk), events).write_set(output, name)?
    }

    writeln!(output, "; === CAT ===\n")?;

    Ok(())
}
