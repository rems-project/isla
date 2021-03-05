// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
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

//! This module implements various routines for simplifying event
//! traces, as well as printing the generated traces.

use std::borrow::{Borrow, BorrowMut};
use std::collections::{HashMap, HashSet};
use std::io::Write;

use crate::bitvector::{write_bits64, BV};
use crate::ir::{Name, Symtab, Val, HAVE_EXCEPTION};
use crate::smt::smtlib::*;
use crate::smt::Event::*;
use crate::smt::{Accessor, Event, Sym};
use crate::zencode;

/// `renumber_event` Renumbers all the symbolic variables in an event such that multiple event
/// sequences can have disjoint variable identifiers. It takes two `u32` arguments `i` and `total`,
/// such that `i` is the index of our event sequence in the range `0..(total - 1)` inclusive where
/// `total` is the number of event sequences we want to make disjoint.
#[allow(clippy::unneeded_field_pattern)]
pub fn renumber_event<B>(event: &mut Event<B>, i: u32, total: u32) {
    assert!(i < total);
    use Event::*;
    match event {
        Smt(def) => renumber_def(def, i, total),
        Fork(_, v, _) | Sleeping(v) => *v = Sym { id: (v.id * total) + i },
        ReadReg(_, _, value) | WriteReg(_, _, value) | Instr(value) => renumber_val(value, i, total),
        Branch { address } => renumber_val(address, i, total),
        Barrier { barrier_kind } => renumber_val(barrier_kind, i, total),
        ReadMem { value, read_kind, address, bytes: _, tag_value, kind: _ } => {
            renumber_val(value, i, total);
            renumber_val(read_kind, i, total);
            renumber_val(address, i, total);
            if let Some(v) = tag_value {
                renumber_val(v, i, total);
            }
        }
        WriteMem { value: v, write_kind, address, data, bytes: _, tag_value, kind: _ } => {
            *v = Sym { id: (v.id * total) + i };
            renumber_val(write_kind, i, total);
            renumber_val(address, i, total);
            renumber_val(data, i, total);
            if let Some(v) = tag_value {
                renumber_val(v, i, total);
            }
        }
        CacheOp { cache_op_kind, address } => {
            renumber_val(cache_op_kind, i, total);
            renumber_val(address, i, total);
        }
        Cycle | SleepRequest | WakeupRequest | MarkReg { .. } | Function { .. } => (),
    }
}

fn renumber_exp(exp: &mut Exp, i: u32, total: u32) {
    exp.modify(
        &(|exp| {
            if let Exp::Var(v) = exp {
                *v = Sym { id: (v.id * total) + i }
            }
        }),
    )
}

fn renumber_val<B>(val: &mut Val<B>, i: u32, total: u32) {
    use Val::*;
    match val {
        Symbolic(v) => *v = Sym { id: (v.id * total) + i },
        I64(_) | I128(_) | Bool(_) | Bits(_) | Enum(_) | String(_) | Unit | Ref(_) | Poison => (),
        List(vals) | Vector(vals) => vals.iter_mut().for_each(|val| renumber_val(val, i, total)),
        Struct(fields) => fields.iter_mut().for_each(|(_, val)| renumber_val(val, i, total)),
        Ctor(_, val) => renumber_val(val, i, total),
    }
}

fn renumber_def(def: &mut Def, i: u32, total: u32) {
    use Def::*;
    match def {
        DeclareConst(v, _) | DeclareFun(v, _, _) | DefineEnum(v, _) => *v = Sym { id: (v.id * total) + i },
        DefineConst(v, exp) => {
            *v = Sym { id: (v.id * total) + i };
            renumber_exp(exp, i, total)
        }
        Assert(exp) => renumber_exp(exp, i, total),
    }
}

/// `uses_in_exp` counts the number of occurences of each variable in an SMTLIB expression.
fn uses_in_exp(uses: &mut HashMap<Sym, u32>, exp: &Exp) {
    use Exp::*;
    match exp {
        Var(v) => {
            uses.insert(*v, uses.get(&v).unwrap_or(&0) + 1);
        }
        Bits(_) | Bits64(_) | Enum(_) | Bool(_) => (),
        Not(exp) | Bvnot(exp) | Bvneg(exp) | Extract(_, _, exp) | ZeroExtend(_, exp) | SignExtend(_, exp) => {
            uses_in_exp(uses, exp)
        }
        Eq(lhs, rhs)
        | Neq(lhs, rhs)
        | And(lhs, rhs)
        | Or(lhs, rhs)
        | Bvand(lhs, rhs)
        | Bvor(lhs, rhs)
        | Bvxor(lhs, rhs)
        | Bvnand(lhs, rhs)
        | Bvnor(lhs, rhs)
        | Bvxnor(lhs, rhs)
        | Bvadd(lhs, rhs)
        | Bvsub(lhs, rhs)
        | Bvmul(lhs, rhs)
        | Bvudiv(lhs, rhs)
        | Bvsdiv(lhs, rhs)
        | Bvurem(lhs, rhs)
        | Bvsrem(lhs, rhs)
        | Bvsmod(lhs, rhs)
        | Bvult(lhs, rhs)
        | Bvslt(lhs, rhs)
        | Bvule(lhs, rhs)
        | Bvsle(lhs, rhs)
        | Bvuge(lhs, rhs)
        | Bvsge(lhs, rhs)
        | Bvugt(lhs, rhs)
        | Bvsgt(lhs, rhs)
        | Bvshl(lhs, rhs)
        | Bvlshr(lhs, rhs)
        | Bvashr(lhs, rhs)
        | Concat(lhs, rhs) => {
            uses_in_exp(uses, lhs);
            uses_in_exp(uses, rhs)
        }
        Ite(cond, then_exp, else_exp) => {
            uses_in_exp(uses, cond);
            uses_in_exp(uses, then_exp);
            uses_in_exp(uses, else_exp)
        }
        App(f, args) => {
            uses.insert(*f, uses.get(&f).unwrap_or(&0) + 1);
            for arg in args {
                uses_in_exp(uses, arg);
            }
        }
        Select(array, index) => {
            uses_in_exp(uses, array);
            uses_in_exp(uses, index)
        }
        Store(array, index, val) => {
            uses_in_exp(uses, array);
            uses_in_exp(uses, index);
            uses_in_exp(uses, val)
        }
    }
}

fn uses_in_value<B>(uses: &mut HashMap<Sym, u32>, val: &Val<B>) {
    use Val::*;
    match val {
        Symbolic(v) => {
            uses.insert(*v, uses.get(&v).unwrap_or(&0) + 1);
        }
        I64(_) | I128(_) | Bool(_) | Bits(_) | Enum(_) | String(_) | Unit | Ref(_) | Poison => (),
        List(vals) | Vector(vals) => vals.iter().for_each(|val| uses_in_value(uses, val)),
        Struct(fields) => fields.iter().for_each(|(_, val)| uses_in_value(uses, val)),
        Ctor(_, val) => uses_in_value(uses, val),
    }
}

pub type Taints = HashSet<(Name, Vec<Accessor>)>;

/// The `EventReferences` struct contains for every variable `v` in a
/// trace, the set of all it's immediate dependencies, i.e. all the
/// symbols used to directly define `v`, as computed by `uses_in_exp`.
pub struct EventReferences {
    references: HashMap<Sym, HashMap<Sym, u32>>,
}

impl EventReferences {
    pub fn from_events<B, E: Borrow<Event<B>>>(events: &[E]) -> Self {
        let mut references = HashMap::new();

        for event in events.iter() {
            if let Smt(Def::DefineConst(id, exp)) = event.borrow() {
                let mut uses = HashMap::new();
                uses_in_exp(&mut uses, exp);
                references.insert(*id, uses);
            }
        }
        EventReferences { references }
    }

    /// Follow all the dependencies of a symbol in the events,
    /// returning the set of symbols it recursively depends on,
    /// (including itself).
    pub fn dependencies(&self, symbol: Sym) -> HashSet<Sym> {
        let empty_map = HashMap::new();
        // The dependencies for symbol
        let mut deps = HashSet::new();
        deps.insert(symbol);
        // Add symbols to this set once all their immediate
        // dependencies have been added to deps
        let mut seen = HashSet::new();

        loop {
            let mut next = HashSet::new();

            for symbol in deps.iter() {
                if !seen.contains(symbol) {
                    let immediate_deps = self.references.get(&symbol).unwrap_or_else(|| &empty_map);
                    for k in immediate_deps.keys() {
                        next.insert(*k);
                    }
                    seen.insert(*symbol);
                }
            }

            // Terminate when we have no more dependencies to add
            if next.is_empty() {
                break;
            } else {
                for symbol in next.iter() {
                    deps.insert(*symbol);
                }
            }
        }

        deps
    }

    /// Returns the set of registers a symbolic variable is tainted
    /// by, i.e. any symbolic registers upon which the variable
    /// depends upon. Also returns whether the value depends upon a
    /// symbolic memory read.
    pub fn taints<B: BV, E: Borrow<Event<B>>>(&self, symbol: Sym, events: &[E]) -> (Taints, bool) {
        let mut taints = HashSet::new();
        let mut memory = false;
        self.collect_taints(symbol, events, &mut taints, &mut memory);
        (taints, memory)
    }

    /// Like `taints` but for all symbolic variables in a value
    pub fn value_taints<B: BV, E: Borrow<Event<B>>>(&self, val: &Val<B>, events: &[E]) -> (Taints, bool) {
        let mut taints = HashSet::new();
        let mut memory = false;
        self.collect_value_taints(val, events, &mut taints, &mut memory);
        (taints, memory)
    }

    pub fn collect_taints<B: BV, E: Borrow<Event<B>>>(
        &self,
        symbol: Sym,
        events: &[E],
        taints: &mut Taints,
        memory: &mut bool,
    ) {
        let deps = self.dependencies(symbol);

        for event in events.iter() {
            match event.borrow() {
                ReadReg(reg, accessor, value) => {
                    let mut uses = HashMap::new();
                    uses_in_value(&mut uses, value);
                    for (taint, _) in uses.iter() {
                        if deps.contains(taint) {
                            taints.insert((*reg, accessor.clone()));
                            break;
                        }
                    }
                }

                ReadMem { value: Val::Symbolic(taint), .. } if deps.contains(taint) => *memory = true,
                ReadMem { tag_value: Some(Val::Symbolic(taint)), .. } if deps.contains(taint) => *memory = true,

                _ => (),
            }
        }
    }

    pub fn collect_value_taints<B: BV, E: Borrow<Event<B>>>(
        &self,
        val: &Val<B>,
        events: &[E],
        taints: &mut Taints,
        memory: &mut bool,
    ) {
        for symbol in val.symbolic_variables() {
            self.collect_taints(symbol, events, taints, memory)
        }
    }
}

#[allow(clippy::unneeded_field_pattern)]
fn calculate_uses<B, E: Borrow<Event<B>>>(events: &[E]) -> HashMap<Sym, u32> {
    let mut uses: HashMap<Sym, u32> = HashMap::new();

    for event in events.iter().rev() {
        use Event::*;
        match event.borrow() {
            Smt(Def::DeclareConst(_, _)) => (),
            Smt(Def::DeclareFun(_, _, _)) => (),
            Smt(Def::DefineConst(_, exp)) => uses_in_exp(&mut uses, exp),
            Smt(Def::DefineEnum(_, _)) => (),
            Smt(Def::Assert(exp)) => uses_in_exp(&mut uses, exp),
            ReadReg(_, _, val) => uses_in_value(&mut uses, val),
            WriteReg(_, _, val) => uses_in_value(&mut uses, val),
            ReadMem { value: val, read_kind, address, bytes: _, tag_value, kind: _ } => {
                uses_in_value(&mut uses, val);
                uses_in_value(&mut uses, read_kind);
                uses_in_value(&mut uses, address);
                if let Some(v) = tag_value {
                    uses_in_value(&mut uses, v);
                }
            }
            WriteMem { value: sym, write_kind, address, data, bytes: _, tag_value, kind: _ } => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
                uses_in_value(&mut uses, write_kind);
                uses_in_value(&mut uses, address);
                uses_in_value(&mut uses, data);
                if let Some(v) = tag_value {
                    uses_in_value(&mut uses, v);
                }
            }
            Branch { address } => uses_in_value(&mut uses, address),
            Barrier { barrier_kind } => uses_in_value(&mut uses, barrier_kind),
            CacheOp { cache_op_kind, address } => {
                uses_in_value(&mut uses, cache_op_kind);
                uses_in_value(&mut uses, address)
            }
            Fork(_, sym, _) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            Cycle => (),
            Instr(val) => uses_in_value(&mut uses, val),
            Sleeping(sym) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            MarkReg { .. } => (),
            WakeupRequest => (),
            SleepRequest => (),
            Function { .. } => (),
        }
    }

    uses
}

/// We cannot remove symbols from traces if they appear in a few
/// places, this function returns the set of such symbols.
fn calculate_required_uses<B, E: Borrow<Event<B>>>(events: &[E]) -> HashMap<Sym, u32> {
    let mut uses: HashMap<Sym, u32> = HashMap::new();

    for event in events.iter().rev() {
        use Event::*;
        match event.borrow() {
            Smt(Def::DeclareConst(sym, _)) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            Smt(Def::DeclareFun(sym, _, _)) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            Smt(Def::DefineEnum(sym, _)) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            Smt(_) => (),
            ReadReg(_, _, val) => uses_in_value(&mut uses, val),
            WriteReg(_, _, val) => uses_in_value(&mut uses, val),
            ReadMem { value: val, read_kind, address, bytes: _, tag_value, kind: _ } => {
                uses_in_value(&mut uses, val);
                uses_in_value(&mut uses, read_kind);
                uses_in_value(&mut uses, address);
                if let Some(v) = tag_value {
                    uses_in_value(&mut uses, v);
                }
            }
            WriteMem { value: sym, write_kind, address, data, bytes: _, tag_value, kind: _ } => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
                uses_in_value(&mut uses, write_kind);
                uses_in_value(&mut uses, address);
                uses_in_value(&mut uses, data);
                if let Some(v) = tag_value {
                    uses_in_value(&mut uses, v);
                }
            }
            Branch { address } => uses_in_value(&mut uses, address),
            Barrier { barrier_kind } => uses_in_value(&mut uses, barrier_kind),
            CacheOp { cache_op_kind, address } => {
                uses_in_value(&mut uses, cache_op_kind);
                uses_in_value(&mut uses, address)
            }
            Fork(_, sym, _) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            Cycle => (),
            Instr(val) => uses_in_value(&mut uses, val),
            Sleeping(sym) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            MarkReg { .. } => (),
            WakeupRequest => (),
            SleepRequest => (),
            Function { .. } => (),
        }
    }

    uses
}

fn remove_unused_pass<B, E: Borrow<Event<B>>>(events: &mut Vec<E>) -> u32 {
    let uses = calculate_uses(&events);
    let mut removed = 0;

    events.retain(|event| match event.borrow() {
        Smt(Def::DeclareConst(v, _)) => {
            if uses.contains_key(v) {
                true
            } else {
                removed += 1;
                false
            }
        }
        Smt(Def::DefineConst(v, _)) => {
            if uses.contains_key(v) {
                true
            } else {
                removed += 1;
                false
            }
        }
        _ => true,
    });

    removed
}

/// Removes register effects from before the first `(cycle)`
/// event. When combined with `remove_unused` this will reduce the
/// amount of initialization that appears in the trace.
pub fn hide_initialization<B: BV, E: Borrow<Event<B>>>(events: &mut Vec<E>) {
    let mut keep = vec![true; events.len()];
    let mut init_cycle = true;
    for (i, event) in events.iter().enumerate().rev() {
        match event.borrow() {
            WriteReg { .. } if init_cycle => keep[i] = false,
            ReadReg { .. } if init_cycle => keep[i] = false,
            Cycle => init_cycle = false,
            _ => (),
        }
    }
    let mut i = 0;
    events.retain(|_| {
        i += 1;
        keep[i - 1]
    })
}

/// Removes SMT events that are not used by any observable event (such
/// as a memory read or write).
pub fn remove_unused<B: BV, E: Borrow<Event<B>>>(events: &mut Vec<E>) {
    loop {
        if remove_unused_pass(events) == 0 {
            break;
        }
    }
}

/// This rewrite looks for events of the form `(define-const v
/// (expression))`, and if `v` is only used exactly once in subsequent
/// events it will replace that use of `v` by the expression.
pub fn propagate_forwards_used_once<B: BV, E: BorrowMut<Event<B>>>(events: &mut Vec<E>) {
    let uses = calculate_uses(&events);
    let required_uses = calculate_required_uses(&events);

    let mut substs: HashMap<Sym, Option<Exp>> = HashMap::new();

    for (sym, count) in uses {
        if count == 1 && !required_uses.contains_key(&sym) {
            substs.insert(sym, None);
        }
    }

    let mut keep = vec![true; events.len()];

    for (i, event) in events.iter_mut().enumerate().rev() {
        match event.borrow_mut() {
            Event::Smt(Def::DefineConst(sym, exp)) => {
                exp.subst_once_in_place(&mut substs);

                if substs.contains_key(&sym) {
                    let exp = std::mem::replace(exp, Exp::Bool(false));
                    keep[i] = false;
                    substs.insert(*sym, Some(exp));
                }
            }
            Event::Smt(Def::Assert(exp)) => exp.subst_once_in_place(&mut substs),
            _ => (),
        }
    }

    let mut i = 0;
    events.retain(|_| {
        i += 1;
        keep[i - 1]
    })
}

/// Evaluate SMT subexpressions if all their arguments are constant
pub fn eval<B: BV, E: BorrowMut<Event<B>>>(events: &mut Vec<E>) {
    for event in events.iter_mut() {
        match event.borrow_mut() {
            Event::Smt(Def::DefineConst(_, exp)) | Event::Smt(Def::Assert(exp)) => {
                let e = std::mem::replace(exp, Exp::Bool(false));
                *exp = e.eval();
            }
            _ => (),
        }
    }
}

/// This rewrite pushes extract expressions inwards where possible, so
/// ```text
/// (extract (f a b))
/// ```
/// would be re-written to
/// ```text
/// (f (extract a) (extract b))
/// ```
///
/// This enables further simplifications (such as the extract
/// cancelling with an inner zero extend), which have the end result
/// of reducing the size of bitvectors contained within the generated
/// SMT.
pub fn commute_extract<B: BV, E: BorrowMut<Event<B>>>(events: &mut Vec<E>) {
    for event in events.iter_mut() {
        match event.borrow_mut() {
            Event::Smt(Def::DefineConst(_, exp)) | Event::Smt(Def::Assert(exp)) => exp.modify_top_down(&Exp::commute_extract),
            _ => (),
        }
    }
}

fn accessor_to_string(acc: &[Accessor], symtab: &Symtab) -> String {
    acc.iter()
        .map(|elem| elem.to_string(symtab))
        .fold(None, |acc, elem| if let Some(prefix) = acc { Some(format!("{} {}", prefix, elem)) } else { Some(elem) })
        .map_or("nil".to_string(), |acc| format!("({})", acc))
}

/// Options for writing event traces
pub struct WriteOpts {
    /// A prefix for all variable identifiers
    pub variable_prefix: String,
    /// The prefix for enumeration members
    pub enum_prefix: String,
    /// Will add type annotations to DefineConst constructors
    pub types: bool,
    /// If true, just print the SMT parts of the trace. When false,
    /// the trace is also wrapped in a `(trace ...)` S-expression.
    pub just_smt: bool,
    /// Print the sizes of enumerations declared during symbolic
    /// evaluation.
    pub define_enum: bool,
}

impl WriteOpts {
    pub fn smtlib() -> Self {
        WriteOpts {
            variable_prefix: "v".to_string(),
            enum_prefix: "e".to_string(),
            types: true,
            just_smt: true,
            define_enum: false,
        }
    }
}

impl Default for WriteOpts {
    fn default() -> Self {
        WriteOpts {
            variable_prefix: "v".to_string(),
            enum_prefix: "e".to_string(),
            types: false,
            just_smt: false,
            define_enum: true,
        }
    }
}

fn write_bits(buf: &mut dyn Write, bits: &[bool]) -> std::io::Result<()> {
    if bits.len() % 4 == 0 {
        write!(buf, "#x")?;
        for i in (0..(bits.len() / 4)).rev() {
            let j = i * 4;
            let hex = (if bits[j] { 0b0001 } else { 0 })
                | (if bits[j + 1] { 0b0010 } else { 0 })
                | (if bits[j + 2] { 0b0100 } else { 0 })
                | (if bits[j + 3] { 0b1000 } else { 0 });
            write!(buf, "{:x}", hex)?;
        }
    } else {
        write!(buf, "#b")?;
        for bit in bits.iter().rev() {
            if *bit {
                write!(buf, "1")?
            } else {
                write!(buf, "0")?
            }
        }
    }
    Ok(())
}

fn write_exp(buf: &mut dyn Write, exp: &Exp, opts: &WriteOpts, enums: &[usize]) -> std::io::Result<()> {
    use Exp::*;
    match exp {
        Var(v) => write!(buf, "{}{}", opts.variable_prefix, v),
        Bits(bv) => write_bits(buf, bv),
        Bits64(bv) => write_bits64(buf, bv.lower_u64(), bv.len()),
        Enum(e) => write!(buf, "{}{}_{}", opts.enum_prefix, enums[e.enum_id], e.member),
        Bool(b) => write!(buf, "{}", b),
        Eq(lhs, rhs) => write_binop(buf, "=", lhs, rhs, opts, enums),
        Neq(lhs, rhs) => {
            write!(buf, "(not ")?;
            write_binop(buf, "=", lhs, rhs, opts, enums)?;
            write!(buf, ")")
        }
        And(lhs, rhs) => write_binop(buf, "and", lhs, rhs, opts, enums),
        Or(lhs, rhs) => write_binop(buf, "or", lhs, rhs, opts, enums),
        Not(exp) => write_unop(buf, "not", exp, opts, enums),
        Bvnot(exp) => write_unop(buf, "bvnot", exp, opts, enums),
        Bvand(lhs, rhs) => write_binop(buf, "bvand", lhs, rhs, opts, enums),
        Bvor(lhs, rhs) => write_binop(buf, "bvor", lhs, rhs, opts, enums),
        Bvxor(lhs, rhs) => write_binop(buf, "bvxor", lhs, rhs, opts, enums),
        Bvnand(lhs, rhs) => write_binop(buf, "bvnand", lhs, rhs, opts, enums),
        Bvnor(lhs, rhs) => write_binop(buf, "bvnor", lhs, rhs, opts, enums),
        Bvxnor(lhs, rhs) => write_binop(buf, "bvxnor", lhs, rhs, opts, enums),
        Bvneg(exp) => write_unop(buf, "bvneg", exp, opts, enums),
        Bvadd(lhs, rhs) => write_binop(buf, "bvadd", lhs, rhs, opts, enums),
        Bvsub(lhs, rhs) => write_binop(buf, "bvsub", lhs, rhs, opts, enums),
        Bvmul(lhs, rhs) => write_binop(buf, "bvmul", lhs, rhs, opts, enums),
        Bvudiv(lhs, rhs) => write_binop(buf, "bvudiv", lhs, rhs, opts, enums),
        Bvsdiv(lhs, rhs) => write_binop(buf, "bvsdiv", lhs, rhs, opts, enums),
        Bvurem(lhs, rhs) => write_binop(buf, "bvurem", lhs, rhs, opts, enums),
        Bvsrem(lhs, rhs) => write_binop(buf, "bvsrem", lhs, rhs, opts, enums),
        Bvsmod(lhs, rhs) => write_binop(buf, "bvsmod", lhs, rhs, opts, enums),
        Bvult(lhs, rhs) => write_binop(buf, "bvult", lhs, rhs, opts, enums),
        Bvslt(lhs, rhs) => write_binop(buf, "bvslt", lhs, rhs, opts, enums),
        Bvule(lhs, rhs) => write_binop(buf, "bvule", lhs, rhs, opts, enums),
        Bvsle(lhs, rhs) => write_binop(buf, "bvsle", lhs, rhs, opts, enums),
        Bvuge(lhs, rhs) => write_binop(buf, "bvuge", lhs, rhs, opts, enums),
        Bvsge(lhs, rhs) => write_binop(buf, "bvsge", lhs, rhs, opts, enums),
        Bvugt(lhs, rhs) => write_binop(buf, "bvugt", lhs, rhs, opts, enums),
        Bvsgt(lhs, rhs) => write_binop(buf, "bvsgt", lhs, rhs, opts, enums),
        Extract(i, j, exp) => {
            write!(buf, "((_ extract {} {}) ", i, j)?;
            write_exp(buf, exp, opts, enums)?;
            write!(buf, ")")
        }
        ZeroExtend(n, exp) => {
            write!(buf, "((_ zero_extend {}) ", n)?;
            write_exp(buf, exp, opts, enums)?;
            write!(buf, ")")
        }
        SignExtend(n, exp) => {
            write!(buf, "((_ sign_extend {}) ", n)?;
            write_exp(buf, exp, opts, enums)?;
            write!(buf, ")")
        }
        Bvshl(lhs, rhs) => write_binop(buf, "bvshl", lhs, rhs, opts, enums),
        Bvlshr(lhs, rhs) => write_binop(buf, "bvlshr", lhs, rhs, opts, enums),
        Bvashr(lhs, rhs) => write_binop(buf, "bvashr", lhs, rhs, opts, enums),
        Concat(lhs, rhs) => write_binop(buf, "concat", lhs, rhs, opts, enums),
        Ite(cond, then_exp, else_exp) => {
            write!(buf, "(ite ")?;
            write_exp(buf, cond, opts, enums)?;
            write!(buf, " ")?;
            write_exp(buf, then_exp, opts, enums)?;
            write!(buf, " ")?;
            write_exp(buf, else_exp, opts, enums)?;
            write!(buf, ")")
        }
        App(f, args) => {
            write!(buf, "({}{}", opts.variable_prefix, f)?;
            for arg in args {
                write!(buf, " ")?;
                write_exp(buf, arg, opts, enums)?;
            }
            write!(buf, ")")
        }
        Select(array, index) => write_binop(buf, "select", array, index, opts, enums),
        Store(array, index, val) => {
            write!(buf, "(store ")?;
            write_exp(buf, array, opts, enums)?;
            write!(buf, " ")?;
            write_exp(buf, index, opts, enums)?;
            write!(buf, " ")?;
            write_exp(buf, val, opts, enums)?;
            write!(buf, ")")
        }
    }
}

fn write_unop(buf: &mut dyn Write, op: &str, exp: &Exp, opts: &WriteOpts, enums: &[usize]) -> std::io::Result<()> {
    write!(buf, "({} ", op)?;
    write_exp(buf, exp, opts, enums)?;
    write!(buf, ")")
}

fn write_binop(
    buf: &mut dyn Write,
    op: &str,
    lhs: &Exp,
    rhs: &Exp,
    opts: &WriteOpts,
    enums: &[usize],
) -> std::io::Result<()> {
    write!(buf, "({} ", op)?;
    write_exp(buf, lhs, opts, enums)?;
    write!(buf, " ")?;
    write_exp(buf, rhs, opts, enums)?;
    write!(buf, ")")
}

pub fn write_events_with_opts<B: BV>(
    buf: &mut dyn Write,
    events: &[Event<B>],
    symtab: &Symtab,
    opts: &WriteOpts,
) -> std::io::Result<()> {
    let mut tcx: HashMap<Sym, Ty> = HashMap::new();
    let mut ftcx: HashMap<Sym, (Vec<Ty>, Ty)> = HashMap::new();
    let mut enums: Vec<usize> = Vec::new();

    if !opts.just_smt {
        write!(buf, "(trace").unwrap();
    }
    for event in events.iter().filter(|ev| !opts.just_smt || ev.is_smt()) {
        (match event {
            // TODO: rename this
            Fork(n, _, loc) => write!(buf, "\n  (branch {} \"{}\")", n, loc),

            Function { name, call } => {
                let name = zencode::decode(symtab.to_str(*name));
                if *call {
                    write!(buf, "(call |{}|)", name)
                } else {
                    write!(buf, "(return |{}|)", name)
                }
            }
            
            Smt(Def::DefineEnum(_, size)) if !opts.define_enum => {
                enums.push(*size);
                Ok(())
            }

            Smt(def) => {
                if opts.just_smt {
                    writeln!(buf)?
                } else {
                    write!(buf, "\n  ")?;
                }
                match def {
                    Def::DeclareConst(v, ty) => {
                        tcx.insert(*v, ty.clone());
                        write!(buf, "(declare-const {}{} {})", opts.variable_prefix, v, ty)
                    }
                    Def::DeclareFun(v, arg_tys, result_ty) => {
                        ftcx.insert(*v, (arg_tys.clone(), result_ty.clone()));
                        write!(buf, "(declare_fun {}{} (", opts.variable_prefix, v)?;
                        for ty in arg_tys {
                            write!(buf, "{} ", ty)?
                        }
                        write!(buf, ") {})", result_ty)
                    }
                    Def::DefineConst(v, exp) => {
                        if opts.types {
                            let ty = exp.infer(&tcx, &ftcx).expect("SMT expression was badly-typed");
                            tcx.insert(*v, ty.clone());
                            write!(buf, "(define-const v{} {} ", v, ty)?;
                            write_exp(buf, exp, opts, &enums)?;
                            write!(buf, ")")
                        } else {
                            write!(buf, "(define-const v{} ", v)?;
                            write_exp(buf, exp, opts, &enums)?;
                            write!(buf, ")")
                        }
                    }
                    Def::DefineEnum(_, size) => {
                        if !opts.just_smt {
                            write!(buf, "(define-enum {})", size)?
                        }
                        enums.push(*size);
                        Ok(())
                    }
                    Def::Assert(exp) => {
                        write!(buf, "(assert ")?;
                        write_exp(buf, exp, opts, &enums)?;
                        write!(buf, ")")
                    }
                }
            }

            ReadMem { value, read_kind, address, bytes, tag_value, kind: _ } => write!(
                buf,
                "\n  (read-mem {} {} {} {} {})",
                value.to_string(symtab),
                read_kind.to_string(symtab),
                address.to_string(symtab),
                bytes,
                match tag_value {
                    None => "None".to_string(),
                    Some(v) => format!("Some({})", v.to_string(symtab)),
                }
            ),

            WriteMem { value, write_kind, address, data, bytes, tag_value, kind: _ } => write!(
                buf,
                "\n  (write-mem v{} {} {} {} {} {})",
                value,
                write_kind.to_string(symtab),
                address.to_string(symtab),
                data.to_string(symtab),
                bytes,
                match tag_value {
                    None => "None".to_string(),
                    Some(v) => format!("Some({})", v.to_string(symtab)),
                }
            ),

            Branch { address } => write!(buf, "\n  (branch-address {})", address.to_string(symtab)),

            Barrier { barrier_kind } => write!(buf, "\n  (barrier {})", barrier_kind.to_string(symtab)),

            CacheOp { cache_op_kind, address } => {
                write!(buf, "\n  (cache-op {} {})", cache_op_kind.to_string(symtab), address.to_string(symtab))
            }

            WriteReg(n, acc, v) => write!(
                buf,
                "\n  (write-reg |{}| {} {})",
                zencode::decode(symtab.to_str(*n)),
                accessor_to_string(acc, symtab),
                v.to_string(symtab)
            ),

            ReadReg(n, acc, v) => {
                if *n == HAVE_EXCEPTION {
                    Ok(())
                } else {
                    write!(
                        buf,
                        "\n  (read-reg |{}| {} {})",
                        zencode::decode(symtab.to_str(*n)),
                        accessor_to_string(acc, symtab),
                        v.to_string(symtab)
                    )
                }
            }

            MarkReg { regs, mark } => {
                for reg in regs {
                    write!(buf, "\n  (mark-reg |{}| \"{}\")", zencode::decode(symtab.to_str(*reg)), mark)?
                }
                Ok(())
            }

            Cycle => write!(buf, "\n  (cycle)"),

            Instr(value) => write!(buf, "\n  (instr {})", value.to_string(symtab)),

            Sleeping(value) => write!(buf, "\n  (sleeping v{})", value),

            SleepRequest => write!(buf, "\n  (sleep-request)"),

            WakeupRequest => write!(buf, "\n  (wake-request)"),
        })?
    }
    if !opts.just_smt {
        writeln!(buf, ")")?;
    }
    Ok(())
}

pub fn write_events<B: BV>(buf: &mut dyn Write, events: &[Event<B>], symtab: &Symtab) {
    write_events_with_opts(buf, events, symtab, &WriteOpts::default()).unwrap()
}
