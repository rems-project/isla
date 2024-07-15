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

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::io::Write;

use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::ir::{Name, SharedState, Val};
use isla_lib::log;
use isla_lib::memory::Memory;
use isla_lib::smt::{Event, Sym};

use isla_cat::smt::Sexp;
use isla_mml::accessor::ModelEvent;

use crate::axiomatic::relations::*;
use crate::axiomatic::{AxEvent, ExecutionInfo};
use crate::footprint_analysis::Footprint;
use crate::litmus::{exp::Exp, exp::Loc, opcode_from_objdump, Litmus};
use crate::smt_model::pairwise::Pairs;

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
                False
            }
        }
        (_, _) => False,
    }
}

fn overlap_location<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> Sexp {
    use Sexp::*;

    let mut checks = vec![False];

    for addr1 in ev1.addresses() {
        for addr2 in ev2.addresses() {
            match (addr1, addr2) {
                (Val::Symbolic(sym1), Val::Symbolic(sym2)) => {
                    if sym1 == sym2 {
                        checks.push(True)
                    } else {
                        checks.push(Literal(format!("(= v{} v{})", sym1, sym2)))
                    }
                }
                (Val::Bits(bv), Val::Symbolic(sym)) | (Val::Symbolic(sym), Val::Bits(bv)) => {
                    checks.push(Literal(format!("(= v{} {})", sym, bv)))
                }
                (Val::Bits(bv1), Val::Bits(bv2)) => {
                    if bv1 == bv2 {
                        checks.push(True)
                    } else {
                        checks.push(False)
                    }
                }
                (_, _) => checks.push(False),
            }
        }
    }
    let mut sexp = Or(checks);
    sexp.simplify(&HashSet::new());
    sexp
}

#[allow(clippy::comparison_chain)]
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
                False
            }
        }
        (_, _) => False,
    }
}

fn read_initial_symbolic<B: BV>(
    sym: Sym,
    addr1: &Val<B>,
    bytes: u32,
    memory: &Memory<B>,
    initial_addrs: &HashMap<u64, u64>,
) -> Sexp {
    use Sexp::*;

    let sym = Val::Symbolic::<B>(sym);

    let region_info = if let Val::Bits(concrete_addr) = addr1 {
        memory.in_custom_region(concrete_addr.lower_u64()).map(|region| (region, concrete_addr.lower_u64()))
    } else {
        None
    };

    let mut expr = {
        let bv = if let Some((region, concrete_addr)) = region_info {
            match region.initial_value(concrete_addr, bytes) {
                Some(bv) => bv,
                None => B::new(0, 8 * bytes),
            }
        } else {
            B::new(0, 8 * bytes)
        };
        let bv = Val::Bits(bv);
        Eq(Box::new(Literal(smt_bitvec(&sym))), Box::new(Literal(smt_bitvec(&bv))))
    };

    for (addr2, value) in initial_addrs {
        let addr2 = Val::Bits(B::new(*addr2, 64));
        let value = Val::Bits(B::new(*value, 8 * bytes));

        expr = IfThenElse(
            Box::new(Eq(Box::new(Literal(smt_bitvec(addr1))), Box::new(Literal(smt_bitvec(&addr2))))),
            Box::new(Eq(Box::new(Literal(smt_bitvec(&value))), Box::new(Literal(smt_bitvec(&sym))))),
            Box::new(expr),
        );
    }

    expr
}

fn read_initial_concrete<B: BV>(bv: B, addr1: &Val<B>, memory: &Memory<B>, initial_addrs: &HashMap<u64, u64>) -> Sexp {
    use Sexp::*;

    let region_info = if let Val::Bits(concrete_addr) = addr1 {
        memory.in_custom_region(concrete_addr.lower_u64()).map(|region| (region, concrete_addr.lower_u64()))
    } else {
        None
    };

    let mut expr = if let Some((region, concrete_addr)) = region_info {
        if Some(bv) == region.initial_value(concrete_addr, bv.len() / 8) {
            True
        } else {
            False
        }
    } else {
        if bv.is_zero() {
            True
        } else {
            False
        }
    };

    for (addr2, value) in initial_addrs {
        let addr2 = Val::Bits(B::new(*addr2, 64));
        expr = IfThenElse(
            Box::new(Eq(Box::new(Literal(smt_bitvec(addr1))), Box::new(Literal(smt_bitvec(&addr2))))),
            Box::new(if bv.lower_u64() == *value { True } else { False }),
            Box::new(expr),
        );
    }

    expr
}

fn initial_write_values<B: BV>(addr_name: &str, width: u32, initial_addrs: &HashMap<u64, u64>) -> String {
    let mut expr = "".to_string();
    let mut ites = 0;

    for (addr, value) in initial_addrs {
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
fn read_initial<B: BV>(ev: &AxEvent<B>, memory: &Memory<B>, initial_addrs: &HashMap<u64, u64>) -> Sexp {
    use Sexp::*;
    match (ev.read_value(), ev.address()) {
        (Some((Val::Symbolic(sym), bytes)), Some(addr)) => {
            read_initial_symbolic(*sym, addr, bytes, memory, initial_addrs)
        }
        (Some((Val::Bits(bv), _)), Some(addr)) => read_initial_concrete(*bv, addr, memory, initial_addrs),
        _ => False,
    }
}

/// Error when trying to get an opcode from [ifetch_initial_opcode]
/// Either the event didn't have an address at all to fetch,
/// or could not find the opcode in the objdump
#[derive(Debug)]
enum MissingOpcodeError<B: BV> {
    MissingObjdump(B),
    NoAddress,
}

impl<B: BV> fmt::Display for MissingOpcodeError<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MissingOpcodeError::MissingObjdump(addr) => {
                write!(f, "opcode missing for address {}", addr)
            }
            MissingOpcodeError::NoAddress => {
                write!(f, "event address missing")
            }
        }
    }
}

impl<B: BV> Error for MissingOpcodeError<B> {}

/// [ifetch_initial_opcode] gets the original opcode
/// (i.e. what will become the initial write for that location)
/// for a given ifetch event `ev`
/// using the opcodes in the objdump.
fn ifetch_initial_opcode<B: BV>(ev: &AxEvent<B>, litmus: &Litmus<B>) -> Result<Sexp, MissingOpcodeError<B>> {
    use Sexp::*;
    match ev.address() {
        Some(Val::Bits(addr)) => {
            if let Some(opcode) = opcode_from_objdump(*addr, &litmus.objdump) {
                Ok(Literal(format!("{}", opcode)))
            } else {
                Err(MissingOpcodeError::MissingObjdump(*addr))
            }
        }
        _ => Err(MissingOpcodeError::NoAddress),
    }
}

/// [ifetch_initial] checks if a ifetch is a valid fetch from the
/// initial state, using the opcodes in the objdump. It also performs
/// the same check as [ifetch_match], so they do not need to be used
/// together.
fn ifetch_initial<B: BV>(ev: &AxEvent<B>, litmus: &Litmus<B>) -> Sexp {
    use Sexp::*;

    let Some(opcode) = ev.opcode else {
        return False;
    };

    match ev.address() {
        Some(Val::Bits(addr)) => {
            if let Some(initial_opcode) = opcode_from_objdump(*addr, &litmus.objdump) {
                match ev.read_value() {
                    Some((Val::Symbolic(sym), _)) => Literal(format!("(= v{} {} {})", sym, initial_opcode, opcode)),
                    Some((Val::Bits(bv), _)) => Literal(format!("(= {} {} {})", bv, initial_opcode, opcode)),
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

    if !ev.is_ifetch {
        return False;
    }

    let Some(opcode) = ev.opcode else { return False };

    match ev.read_value() {
        Some((Val::Symbolic(sym), _)) => Literal(format!("(= v{} {})", sym, opcode)),
        Some((Val::Bits(bv), _)) => Literal(format!("(= {} {})", bv, opcode)),
        _ => False,
    }
}

fn translate_read_invalid<B: BV>(ev: &AxEvent<B>) -> Sexp {
    if is_translate(ev) {
        let mut conds = Vec::new();
        for base_event in &ev.base {
            match base_event {
                Event::ReadMem { value: Val::Bits(bv), bytes, .. } if *bytes == 8 => {
                    if bv.slice(0, 1).unwrap() == B::zeros(1) {
                        conds.push(Sexp::True)
                    }
                }
                Event::ReadMem { value, bytes, .. } if *bytes == 8 => conds.push(Sexp::Literal(format!(
                    "(= (bvand {} #x0000000000000001) #x0000000000000000)",
                    smt_bitvec(value)
                ))),
                _ => (),
            }
        }
        Sexp::Or(conds)
    } else {
        Sexp::False
    }
}

fn dep_rel_target<B: BV>(ev: &AxEvent<B>, shared_state: &SharedState<B>) -> Sexp {
    if is_read(ev) || is_write(ev) {
        return Sexp::True;
    }

    if let [base_event] = ev.base_events() {
        match base_event {
            Event::Abstract { name, .. } if shared_state.symtab.to_str(*name) == "zsail_system_register_write" => {
                return Sexp::True
            }
            _ => (),
        }
    }

    translate_read_invalid(ev)
}

fn smt_empty() -> Sexp {
    Sexp::False
}

fn smt_basic_rel<B, F>(rel: F, events: &[AxEvent<B>]) -> Sexp
where
    B: BV,
    F: Fn(&AxEvent<B>, &AxEvent<B>) -> bool,
{
    use Sexp::*;
    let mut deps = Vec::new();
    for (ev1, ev2) in Pairs::from_slice(events).filter(|(ev1, ev2)| rel(ev1, ev2)) {
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
    for (ev1, ev2) in Pairs::from_slice(events).filter(|(ev1, ev2)| rel(ev1, ev2)) {
        deps.push(And(vec![
            Eq(Box::new(Var(1)), Box::new(Literal(ev1.name.to_string()))),
            Eq(Box::new(Var(2)), Box::new(Literal(ev2.name.to_string()))),
            f(ev1, ev2),
        ]))
    }
    deps.push(False);
    let mut sexp = Or(deps);
    sexp.simplify(&HashSet::new());
    sexp
}

fn smt_dep_rel2<B: BV>(
    rel: DepRel<B>,
    events: &[AxEvent<B>],
    thread_opcodes: &[Vec<Option<B>>],
    footprints: &HashMap<B, Footprint>,
    shared_state: &SharedState<B>,
) -> Sexp {
    use Sexp::*;
    let mut deps = Vec::new();
    for (ev1, ev2) in Pairs::from_slice(events).filter(|(ev1, ev2)| rel(ev1, ev2, thread_opcodes, footprints)) {
        deps.push(And(vec![
            Eq(Box::new(Var(1)), Box::new(Literal(ev1.name.to_string()))),
            Eq(Box::new(Var(2)), Box::new(Literal(ev2.name.to_string()))),
            dep_rel_target(ev2, shared_state),
        ]))
    }
    let mut sexp = Or(deps);
    sexp.simplify(&HashSet::new());
    sexp
}

fn smt_dep_rel<B: BV>(
    rel: DepRel<B>,
    events: &[AxEvent<B>],
    thread_opcodes: &[Vec<Option<B>>],
    footprints: &HashMap<B, Footprint>,
) -> Sexp {
    use Sexp::*;
    let mut deps = Vec::new();
    for (ev1, ev2) in Pairs::from_slice(events).filter(|(ev1, ev2)| rel(ev1, ev2, thread_opcodes, footprints)) {
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
    deps.push(False);
    let mut sexp = Or(deps);
    sexp.simplify(&HashSet::new());
    sexp
}

fn eq_loc_to_smt<B: BV>(loc: &Loc<u64>, exp: &Exp<u64>, final_writes: &HashMap<(Name, usize), &Val<B>>) -> String {
    use Loc::*;
    match loc {
        Register { reg, thread_id } => match final_writes.get(&(*reg, *thread_id)) {
            Some(Val::Symbolic(sym)) => format!("(= v{} {})", sym, exp_to_smt(exp, final_writes)),
            Some(Val::Bits(reg_bv)) => format!("(= {} {})", reg_bv, exp_to_smt(exp, final_writes)),
            Some(_) => unreachable!(),
            None => "false".to_string(),
        },
        LastWriteTo { address, bytes } => {
            format!("(last_write_to_{} {} {})", bytes * 8, B::from_u64(*address), exp_to_smt(exp, final_writes))
        }
    }
}

fn exp_to_smt<B: BV>(exp: &Exp<u64>, final_writes: &HashMap<(Name, usize), &Val<B>>) -> String {
    use Exp::*;
    match exp {
        EqLoc(loc, exp) => eq_loc_to_smt(loc, exp, final_writes),
        Loc(address) => B::from_u64(*address).to_string(),
        Label(_) => unimplemented!(),
        App(f, exps, _) => {
            let mut args = String::new();
            for exp in exps {
                args = format!("{} {}", args, exp_to_smt(exp, final_writes))
            }
            format!("({}{})", f, args)
        }
        And(exps) => {
            let mut conjs = String::new();
            for exp in exps {
                conjs = format!("{} {}", conjs, exp_to_smt(exp, final_writes))
            }
            format!("(and{})", conjs)
        }
        Or(exps) => {
            let mut disjs = String::new();
            for exp in exps {
                disjs = format!("{} {}", disjs, exp_to_smt(exp, final_writes))
            }
            format!("(or{})", disjs)
        }
        Implies(exp1, exp2) => format!("(=> {} {})", exp_to_smt(exp1, final_writes), exp_to_smt(exp2, final_writes)),
        Not(exp) => format!("(not {})", exp_to_smt(exp, final_writes)),
        True => "true".to_string(),
        False => "false".to_string(),
        Bin(bv) => format!("#b{}", bv),
        Hex(bv) => format!("#x{}", bv),
        Bits64(bits, len) => B::new(*bits, *len).to_string(),
        Nat(n) => B::from_u64(*n).to_string(),
    }
}

fn subst_template<T: AsRef<str>, R: AsRef<str>>(template: T, subst: &str, replace: R) -> String {
    use regex::Regex;
    let subst_re = Regex::new(&format!(r"\${}", subst)).unwrap();
    subst_re.replace_all(template.as_ref(), replace.as_ref()).to_string()
}

fn ifetch_pair<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
    ev1.is_ifetch && ev2.is_ifetch
}

static COMMON_SMTLIB: &str = include_str!("smt_events.smt2");

static IFETCH_SMTLIB: &str = include_str!("ifetch.smt2");

static LAST_WRITE_TO: &str = include_str!("last_write_to.smt2");

#[allow(clippy::too_many_arguments)]
pub fn smt_of_candidate<B: BV>(
    output: &mut dyn Write,
    exec: &ExecutionInfo<B>,
    litmus: &Litmus<B>,
    ignore_ifetch: bool,
    armv8_page_tables: bool,
    footprints: &HashMap<B, Footprint>,
    memory: &Memory<B>,
    initial_physical_addrs: &HashMap<u64, u64>,
    final_assertion: &Exp<u64>,
    shared_state: &SharedState<B>,
    isa_config: &ISAConfig<B>,
) -> Result<(), Box<dyn Error>> {
    let events = &exec.smt_events;
    let translations = exec.translations();

    log!(log::LITMUS, "generating smt for candidate");

    writeln!(output, "\n\n; === EVENTS ===\n")?;
    log!(log::LITMUS, "generating smt events");

    write!(output, "(declare-datatypes ((Event 0))\n  ((")?;
    for ev in &exec.smt_events {
        write!(output, "({}) ", ev.name)?;
    }
    writeln!(output, "(IW))))")?;

    // these sets really ought to come from the interface
    // instead of being hard-coded in isla
    smt_set(is_read, events).write_set(output, "R")?;
    smt_set(is_write, events).write_set(output, "W")?;
    smt_set(is_translate, events).write_set(output, "AT")?;
    smt_set(|ev| is_translate(ev) && ev.base.iter().any(|b| b.is_memory_read()), events).write_set(output, "T")?;
    smt_set(|ev| is_translate(ev) && is_in_s1_table(ev), events).write_set(output, "Stage1")?;
    smt_set(|ev| is_translate(ev) && is_in_s2_table(ev), events).write_set(output, "Stage2")?;

    let mut all_write_widths = HashSet::new();
    // Always make sure we have at least one width to avoid generating invalid SMT for writes
    all_write_widths.insert(&8);
    for (_, _, ev) in exec.base_events() {
        if let Event::WriteMem { bytes, .. } = ev {
            all_write_widths.insert(bytes);
        }
    }

    for &width in all_write_widths.iter() {
        assert!(*width > 0);
        writeln!(output, "(define-fun val_of_{} ((ev Event)) (_ BitVec {})", width * 8, width * 8)?;
        let mut ites: usize = 0;
        for ev in events {
            match ev.base() {
                Some(Event::WriteMem { bytes, data, .. }) if bytes == width => {
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
        // TODO: don't hardcode 32-bit ifetch opcode, or at least pad out to max word size
        writeln!(output, "(define-fun ifetch_initial_opcode ((ev Event)) (_ BitVec 32)")?;
        let mut ites: usize = 0;
        for ev in events {
            match ev.base() {
                Some(Event::ReadMem { opts, .. }) if opts.is_ifetch => {
                    write!(output, "{}", String::from_utf8(vec![b' '; 1 + ites])?)?;
                    write!(output, "(ite (= ev {}) ", ev.name)?;
                    ifetch_initial_opcode(ev, litmus)?.write_to(output, false, 0, true)?;
                    ites += 1
                }
                _ => (),
            }
        }
        write!(output, " {}", B::zeros(32))?;
        for _ in 0..ites {
            write!(output, ")")?
        }
        writeln!(output, ")\n")?
    }

    {
        writeln!(output, "(define-fun addr_of ((ev Event)) (_ BitVec 64)")?;
        let mut ites: usize = 0;
        for ev in events {
            match ev.base() {
                Some(Event::WriteMem { address, .. }) | Some(Event::ReadMem { address, .. }) => {
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

    write!(output, "(define-fun read_addr_of ((ev Event) (addr (_ BitVec 64))) Bool\n  (or false")?;
    for (ax_event, _, base_event) in exec.base_events() {
        if let Event::ReadMem { address, .. } = base_event {
            write!(output, "\n    (and (= ev {}) (= addr {}))", ax_event.name, smt_bitvec(address))?;
        }
    }
    writeln!(output, "))\n")?;

    for &width in all_write_widths.iter() {
        assert!(*width > 0);
        write!(
            output,
            "(define-fun write_data_of_{} ((ev Event) (data (_ BitVec {}))) Bool\n (or\n",
            width * 8,
            width * 8
        )?;
        for (ax_event, _, base_event) in exec.base_events() {
            if let Event::WriteMem { bytes, data, .. } = base_event {
                if bytes == width {
                    writeln!(output, "    (and (= ev {}) (= data {}))", ax_event.name, smt_bitvec(data))?;
                }
            }
        }
        writeln!(output, "    false))\n")?
    }

    for &width in all_write_widths.iter() {
        assert!(*width > 0);
        write!(
            output,
            "(define-fun write_addr_data_of_{} ((ev Event) (addr (_ BitVec 64)) (data (_ BitVec {}))) Bool\n (or\n",
            width * 8,
            width * 8
        )?;
        for (ax_event, _, base_event) in exec.base_events() {
            if let Event::WriteMem { address, bytes, data, .. } = base_event {
                if bytes == width {
                    writeln!(
                        output,
                        "    (and (= ev {}) (= addr {}) (= data {}))",
                        ax_event.name,
                        smt_bitvec(address),
                        smt_bitvec(data)
                    )?;
                }
            }
        }
        writeln!(output, "    false))\n")?
    }

    if armv8_page_tables {
        write!(
            output,
            "(define-fun translated_before ((ev Event) (addr1 (_ BitVec 64)) (addr2 (_ BitVec 64))) Bool\n  (or false"
        )?;
        for ax_event in events {
            if is_translate(ax_event) {
                let mut previous = Vec::new();
                write!(output, "\n    (and (= ev {})", ax_event.name)?;
                for base_event in &ax_event.base {
                    if let Event::ReadMem { address: Val::Bits(addr2), .. } = base_event {
                        if !previous.is_empty() {
                            write!(output, "\n      (or")?;
                            for addr1 in &previous {
                                write!(output, "\n        (and (= addr1 {}) (= addr2 {}))", addr1, addr2)?
                            }
                            write!(output, ")")?
                        }
                        previous.push(addr2);
                    }
                }
                write!(output, ")")?
            }
        }
        writeln!(output, "))\n")?;

        {
            writeln!(output, "(define-fun translate_va ((ev Event)) (_ BitVec 64)")?;
            let mut ites: usize = 0;
            for ax_event in events {
                if let Some(translation_id) = ax_event.translate {
                    if let Some(va) = translations.va_page(translation_id) {
                        writeln!(output, "  (ite (= ev {}) {}", ax_event.name, B::from_u64(va.bits()))?;
                        ites += 1
                    }
                }
            }
            write!(output, "  #x0000000000000000")?;
            for _ in 0..ites {
                write!(output, ")")?
            }
            writeln!(output, ")\n")?
        }

        {
            writeln!(output, "(define-fun translate_ipa ((ev Event)) (_ BitVec 64)")?;
            let mut ites: usize = 0;
            for ax_event in events {
                if let Some(translation_id) = ax_event.translate {
                    if let Some(va) = translations.ipa_page(translation_id) {
                        writeln!(output, "  (ite (= ev {}) {}", ax_event.name, B::from_u64(va.bits()))?;
                        ites += 1
                    }
                }
            }
            write!(output, "  #x0000000000000000")?;
            for _ in 0..ites {
                write!(output, ")")?
            }
            writeln!(output, ")\n")?
        }

        write!(output, "(define-fun tt_init ((addr (_ BitVec 64)) (data (_ BitVec 64))) Bool\n  (or false")?;
        for (ax_event, _, base_event) in exec.base_events() {
            if let Event::ReadMem { address: Val::Bits(address), bytes, .. } = base_event {
                if is_translate(ax_event) && *bytes == 8 {
                    let data = memory
                        .read_initial(address.lower_u64(), 8)
                        .unwrap_or_else(|_| Val::Bits(B::from_u64(0)))
                        .as_bits()
                        .copied()
                        .unwrap();
                    write!(output, "\n    (and (= addr {}) (= data {}))", address, data)?
                }
            }
        }
        writeln!(output, "))\n")?;

        writeln!(output, "(define-fun tt_write ((ev Event) (addr (_ BitVec 64)) (data (_ BitVec 64))) Bool\n  (or (and (= ev IW) (tt_init addr data)) (and (W ev) (write_addr_data_of_64 ev addr data))))\n")?;

        {
            let mut write_translates: Vec<(String, String, usize, bool)> = Vec::new();
            for (i, (ax_event, base_index, base_event)) in exec.base_events().enumerate() {
                if let Event::ReadMem { value, address, bytes, region, .. } = base_event {
                    if is_translate(ax_event) && *bytes == 8 {
                        let write_event = format!("{}_W{}", ax_event.name, i);
                        writeln!(output, "(declare-const {} Event)", write_event)?;
                        writeln!(
                            output,
                            "(assert (tt_write {} {} {}))",
                            write_event,
                            smt_bitvec(address),
                            smt_bitvec(value)
                        )?;
                        write_translates.push((write_event, ax_event.name.clone(), base_index, *region == "stage 1"))
                    }
                }
            }
            write!(output, "(define-fun trf1-internal ((ev1 Event) (ev2 Event)) Bool\n  (or")?;
            for (write, translate, _, s1) in &write_translates {
                if *s1 {
                    write!(output, "\n    (and (= ev1 {}) (= ev2 {}))", write, translate)?
                }
            }
            writeln!(output, "\n    false))")?;
            write!(output, "(define-fun trf2-internal ((ev1 Event) (ev2 Event)) Bool\n  (or")?;
            for (write, translate, _, s1) in &write_translates {
                if !*s1 {
                    write!(output, "\n    (and (= ev1 {}) (= ev2 {}))", write, translate)?
                }
            }
            writeln!(output, "\n    false))")?;
        }

        smt_condition_set(|ev| translate_read_invalid(ev), events).write_set(output, "T_f")?;
    } else {
        smt_empty().write_rel(output, "trf1-internal")?;
        smt_empty().write_rel(output, "trf2-internal")?;
        smt_empty().write_set(output, "T_f")?;
    }

    smt_set(|ev| is_read(ev) || is_write(ev), events).write_set(output, "M")?;
    smt_set(is_ifetch, events).write_set(output, "IF")?;

    for (set, kinds) in isa_config.register_event_sets.iter() {
        smt_set(|ev| kinds.iter().any(|k| k.is_read() && ev.has_read_reg_of(k.name())), events)
            .write_set(output, &format!("read_{}", set))?;
        smt_set(|ev| kinds.iter().any(|k| k.is_write() && ev.has_read_reg_of(k.name())), events)
            .write_set(output, &format!("write_{}", set))?;

        writeln!(output, "(define-fun val_of_read_{} ((ev Event)) (_ BitVec 64)", set)?;
        let mut ites: usize = 0;
        for ax_event in events {
            let mut set_reads = Vec::new();

            for ev in ax_event.base.iter() {
                for kind in kinds {
                    if kind.is_read() && ev.is_read_reg_of(kind.name()) {
                        set_reads.push(ev.reg_value().unwrap())
                    }
                }
            }

            if !set_reads.is_empty() {
                for read in set_reads[1..].iter().copied() {
                    if set_reads[0] != read {
                        panic!("Non-identical read in event")
                    }
                }
                write!(output, "  (ite (= ev {}) {}", ax_event.name, smt_bitvec(set_reads[0]))?;
                ites += 1
            }
        }
        write!(output, "  {}", B::zeros(64))?;
        for _ in 0..ites {
            write!(output, ")")?
        }
        writeln!(output, ")\n")?
    }

    smt_condition_set(|ev| read_initial(ev, memory, initial_physical_addrs), events).write_set(output, "r-initial")?;
    if !ignore_ifetch {
        smt_condition_set(ifetch_match, events).write_set(output, "ifetch-match")?;
        smt_condition_set(|ev| ifetch_initial(ev, litmus), events).write_set(output, "ifetch-initial")?;
    }

    smt_dep_rel(amo, events, &exec.thread_opcodes, footprints).write_rel(output, "amo")?;

    writeln!(output, "; === BASIC RELATIONS ===\n")?;
    log!(log::LITMUS, "generating smt basic relations");

    // instruction-order is the superset of all the `po`-related relations
    // it relates all events to all events that come from instructions from program-order later instructions
    smt_basic_rel(instruction_order, events).write_rel(output, "instruction-order")?;
    smt_basic_rel(po, events).write_rel(output, "po")?;

    // In the ifetch model, rather than just po, we have a relation
    // fpo for ifetch events, while po relates only non-ifetch
    // events. The relation fe (fetch-to-execute) relates an ifetch
    // with all events executed by the fetched instruction.
    if !ignore_ifetch {
        smt_basic_rel(|ev1, ev2| instruction_order(ev1, ev2) && ifetch_pair(ev1, ev2), events)
            .write_rel(output, "fpo")?;
        smt_basic_rel(|ev1, ev2| ifetch_to_execute(ev1, ev2), events).write_rel(output, "fe")?
    } else {
        smt_empty().write_rel(output, "fpo")?;
        smt_empty().write_rel(output, "fe")?;
    }

    smt_basic_rel(|ev1, ev2| intra_instruction_ordered(ev1, ev2), events).write_rel(output, "iio")?;

    smt_basic_rel(internal, events).write_rel(output, "int")?;
    smt_basic_rel(external, events).write_rel(output, "ext")?;
    smt_basic_rel(same_translation, events).write_rel(output, "same-translation")?;
    smt_condition_rel(disjoint, events, same_location).write_rel(output, "loc")?;
    smt_condition_rel(disjoint, events, overlap_location).write_rel(output, "overlap-loc")?;
    smt_condition_rel(po, events, same_location).write_rel(output, "po-loc")?;
    smt_condition_rel(univ, events, read_write_pair).write_rel(output, "rw-pair")?;
    smt_dep_rel2(addr, events, &exec.thread_opcodes, footprints, shared_state).write_rel(output, "addr")?;
    smt_dep_rel2(data, events, &exec.thread_opcodes, footprints, shared_state).write_rel(output, "data")?;
    smt_dep_rel(ctrl, events, &exec.thread_opcodes, footprints).write_rel(output, "ctrl")?;
    smt_dep_rel(rmw, events, &exec.thread_opcodes, footprints).write_rel(output, "rmw")?;
    smt_basic_rel(|ev1, ev2| same_va_page(ev1, ev2, &translations), events)
        .write_rel(output, "translate-same-va-page")?;
    smt_basic_rel(|ev1, ev2| same_ipa_page(ev1, ev2, &translations), events)
        .write_rel(output, "translate-same-ipa-page")?;

    writeln!(output, "; === COMMON SMTLIB ===\n")?;
    log!(log::LITMUS, "generating smtlib");
    writeln!(output, "{}", COMMON_SMTLIB)?;

    if !ignore_ifetch {
        writeln!(output, "{}", IFETCH_SMTLIB)?;
    } else {
        smt_empty().write_rel(output, "irf")?;
    }

    for &width in all_write_widths.iter() {
        let lwt =
            subst_template(LAST_WRITE_TO, "INITIAL", initial_write_values::<B>("addr", 64, initial_physical_addrs));
        let lwt = subst_template(lwt, "LEN_MINUS_1", format!("{}", width * 8 - 1));
        let lwt = subst_template(lwt, "LEN", format!("{}", width * 8));
        writeln!(output, "{}", lwt)?;
    }

    writeln!(output, "; === FINAL ASSERTION ===\n")?;
    log!(log::LITMUS, "generating smt final assertion");
    writeln!(output, "(assert {})\n", exp_to_smt(final_assertion, &exec.final_writes))?;

    Ok(())
}
