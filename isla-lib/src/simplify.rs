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

use std::borrow::{Borrow, BorrowMut, Cow};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::PathBuf;

use crate::bitvector::{write_bits64, BV};
use crate::ir::{source_loc::SourceLoc, BitsSegment, Loc, Name, Symtab, Val, HAVE_EXCEPTION};
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
        Smt(def, _) => renumber_def(def, i, total),
        Fork(_, v, _, _) | Sleeping(v) => *v = Sym { id: (v.id * total) + i },
        ReadReg(_, _, value) | WriteReg(_, _, value) | Instr(value) | AssumeReg(_, _, value) => {
            renumber_val(value, i, total)
        }
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
        CacheOp { cache_op_kind, address, extra_data } => {
            renumber_val(cache_op_kind, i, total);
            renumber_val(address, i, total);
            renumber_val(extra_data, i, total);
        }
        Cycle | SleepRequest | WakeupRequest | MarkReg { .. } | Function { .. } | Assume(_) => (),
    }
}

fn renumber_exp(exp: &mut Exp<Sym>, i: u32, total: u32) {
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
        MixedBits(segments) => segments.iter_mut().for_each(|segment| match segment {
            BitsSegment::Symbolic(v) => *v = Sym { id: (v.id * total) + i },
            BitsSegment::Concrete(_) => (),
        }),
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
fn uses_in_exp(uses: &mut HashMap<Sym, u32>, exp: &Exp<Sym>) {
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
        Distinct(exps) => {
            for exp in exps {
                uses_in_exp(uses, exp);
            }
        }
    }
}

fn uses_in_value<B>(uses: &mut HashMap<Sym, u32>, val: &Val<B>) {
    use Val::*;
    match val {
        Symbolic(v) => {
            uses.insert(*v, uses.get(&v).unwrap_or(&0) + 1);
        }
        MixedBits(segments) => segments.iter().for_each(|segment| match segment {
            BitsSegment::Symbolic(v) => {
                uses.insert(*v, uses.get(&v).unwrap_or(&0) + 1);
            }
            BitsSegment::Concrete(_) => (),
        }),
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
            if let Smt(Def::DefineConst(id, exp), _) = event.borrow() {
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
fn calculate_more_uses<B, E: Borrow<Event<B>>>(events: &[E], uses: &mut HashMap<Sym, u32>) {
    for event in events.iter().rev() {
        use Event::*;
        match event.borrow() {
            Smt(Def::DeclareConst(_, _), _) => (),
            Smt(Def::DeclareFun(_, _, _), _) => (),
            Smt(Def::DefineConst(_, exp), _) => uses_in_exp(uses, exp),
            Smt(Def::DefineEnum(_, _), _) => (),
            Smt(Def::Assert(exp), _) => uses_in_exp(uses, exp),
            ReadReg(_, _, val) => uses_in_value(uses, val),
            WriteReg(_, _, val) => uses_in_value(uses, val),
            ReadMem { value: val, read_kind, address, bytes: _, tag_value, kind: _ } => {
                uses_in_value(uses, val);
                uses_in_value(uses, read_kind);
                uses_in_value(uses, address);
                if let Some(v) = tag_value {
                    uses_in_value(uses, v);
                }
            }
            WriteMem { value: sym, write_kind, address, data, bytes: _, tag_value, kind: _ } => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
                uses_in_value(uses, write_kind);
                uses_in_value(uses, address);
                uses_in_value(uses, data);
                if let Some(v) = tag_value {
                    uses_in_value(uses, v);
                }
            }
            Branch { address } => uses_in_value(uses, address),
            Barrier { barrier_kind } => uses_in_value(uses, barrier_kind),
            CacheOp { cache_op_kind, address, extra_data } => {
                uses_in_value(uses, cache_op_kind);
                uses_in_value(uses, address);
                uses_in_value(uses, extra_data)
            }
            Fork(_, sym, _, _) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            Cycle => (),
            Instr(val) => uses_in_value(uses, val),
            Sleeping(sym) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            MarkReg { .. } => (),
            WakeupRequest => (),
            SleepRequest => (),
            Function { .. } => (),
            Assume(_) => (),
            AssumeReg(_, _, val) => uses_in_value(uses, val),
        }
    }
}

fn calculate_uses<B, E: Borrow<Event<B>>>(events: &[E]) -> HashMap<Sym, u32> {
    let mut uses: HashMap<Sym, u32> = HashMap::new();
    calculate_more_uses(events, &mut uses);
    uses
}

fn calculate_more_tree_uses<B>(event_tree: &EventTree<B>, uses: &mut HashMap<Sym, u32>) {
    calculate_more_uses(&event_tree.prefix, uses);
    for fork in &event_tree.forks {
        calculate_more_tree_uses(fork, uses);
    }
}

fn calculate_tree_uses<B>(event_tree: &EventTree<B>) -> HashMap<Sym, u32> {
    let mut uses: HashMap<Sym, u32> = HashMap::new();
    calculate_more_tree_uses(event_tree, &mut uses);
    uses
}

/// We cannot remove symbols from traces if they appear in a few
/// places, this function returns the set of such symbols.
fn calculate_required_uses<B, E: Borrow<Event<B>>>(events: &[E]) -> HashMap<Sym, u32> {
    let mut uses: HashMap<Sym, u32> = HashMap::new();

    for event in events.iter().rev() {
        use Event::*;
        match event.borrow() {
            Smt(Def::DeclareConst(sym, _), _) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            Smt(Def::DeclareFun(sym, _, _), _) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            Smt(Def::DefineEnum(sym, _), _) => {
                uses.insert(*sym, uses.get(&sym).unwrap_or(&0) + 1);
            }
            Smt(_, _) => (),
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
            CacheOp { cache_op_kind, address, extra_data } => {
                uses_in_value(&mut uses, cache_op_kind);
                uses_in_value(&mut uses, address);
                uses_in_value(&mut uses, extra_data)
            }
            Fork(_, sym, _, _) => {
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
            Assume(_) => (),
            AssumeReg(_, _, val) => uses_in_value(&mut uses, val),
        }
    }

    uses
}

fn remove_unused_pass<B, E: Borrow<Event<B>>>(events: &mut Vec<E>) -> u32 {
    let uses = calculate_uses(&events);
    let mut removed = 0;

    events.retain(|event| match event.borrow() {
        Smt(Def::DeclareConst(v, _), _) => {
            if uses.contains_key(v) {
                true
            } else {
                removed += 1;
                false
            }
        }
        Smt(Def::DefineConst(v, _), _) => {
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

fn remove_unused_pass_tree<B>(event_tree: &mut EventTree<B>, uses: &HashMap<Sym, u32>) -> bool {
    let mut removed = false;

    event_tree.prefix.retain(|event| match event.borrow() {
        Smt(Def::DeclareConst(v, _), _) => {
            if uses.contains_key(v) {
                true
            } else {
                removed = true;
                false
            }
        }
        Smt(Def::DefineConst(v, _), _) => {
            if uses.contains_key(v) {
                true
            } else {
                removed = true;
                false
            }
        }
        _ => true,
    });

    for fork in &mut event_tree.forks {
        removed |= remove_unused_pass_tree(fork, uses);
    }

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

pub fn hide_initialization_tree<B: BV>(event_tree: &mut EventTree<B>) {
    let mut init_cycle = true;
    event_tree.prefix.retain(|event| match event {
        WriteReg { .. } if init_cycle => false,
        ReadReg { .. } if init_cycle => false,
        Cycle => {
            init_cycle = false;
            true
        }
        _ => true,
    });
    if init_cycle {
        for fork in &mut event_tree.forks {
            hide_initialization_tree(fork);
        }
    }
}

fn restrict_to_accessor<B: BV>(val: &mut Val<B>, accessor: &[Accessor]) {
    let mut v = val;
    for acc in accessor {
        match acc {
            Accessor::Field(name) => match v {
                Val::Struct(map) => {
                    map.retain(|k, _| *k == *name);
                    v = map.get_mut(name).expect("missing field");
                }
                _ => panic!("Attempted to access field {:?} of non-struct value {:?}", name, v),
            },
        }
    }
}

/// Reduces the value to just the parts reachable from the accessor.
pub fn remove_extra_register_fields<B: BV>(events: &mut Vec<Event<B>>) {
    for event in events.iter_mut() {
        match event {
            WriteReg(_n, acc, v) => restrict_to_accessor(v, acc),
            ReadReg(_n, acc, v) => restrict_to_accessor(v, acc),
            _ => (),
        }
    }
}

pub fn remove_extra_register_fields_tree<B: BV>(event_tree: &mut EventTree<B>) {
    event_tree.map(&remove_extra_register_fields);
}

fn remove_affected_register_parts<V>(
    register_map: &mut HashMap<Name, HashMap<Vec<Accessor>, V>>,
    name: Name,
    acc: &[Accessor],
) {
    if let Some(regmap) = register_map.get_mut(&name) {
        regmap.retain(|element_acc, _| !(acc.starts_with(element_acc) || element_acc.starts_with(acc)));
    }
}

fn record_affected_register_parts<V: Eq + std::hash::Hash + Copy>(
    register_map: &mut HashMap<Name, HashMap<Vec<Accessor>, V>>,
    record: &mut HashSet<V>,
    name: Name,
    acc: &[Accessor],
) {
    if let Some(regmap) = register_map.get_mut(&name) {
        regmap.retain(|element_acc, v| {
            if acc.starts_with(element_acc) || element_acc.starts_with(acc) {
                record.insert(*v);
                false
            } else {
                true
            }
        });
    }
}

pub fn remove_repeated_register_reads<B: BV>(events: &mut Vec<Event<B>>) {
    let mut recent_reads: HashMap<Name, HashMap<Vec<Accessor>, Val<B>>> = HashMap::new();
    // Some contortions because the trace is in reverse order when simplifications are performed.
    let mut keep = vec![true; events.len()];
    for (i, event) in events.iter().enumerate().rev() {
        match event {
            ReadReg(name, acc, v) => {
                if let Some(regmap) = recent_reads.get(name) {
                    if let Some(last_value) = regmap.get(acc) {
                        if *v == *last_value {
                            keep[i] = false;
                            continue;
                        }
                    }
                };
                remove_affected_register_parts(&mut recent_reads, *name, &acc);
                let regmap = recent_reads.entry(*name).or_insert_with(HashMap::new);
                regmap.insert(acc.clone(), v.clone());
            }
            WriteReg(name, acc, _v) => {
                remove_affected_register_parts(&mut recent_reads, *name, acc);
            }
            _ => (),
        }
    }
    let mut i = 0;
    events.retain(|_| {
        i += 1;
        keep[i - 1]
    })
}

fn remove_repeated_register_reads_core<B: BV>(
    mut recent_reads: &mut HashMap<Name, HashMap<Vec<Accessor>, Val<B>>>,
    events: &mut EventTree<B>,
) {
    events.prefix.retain(|event| match event {
        ReadReg(name, acc, v) => {
            if let Some(regmap) = recent_reads.get(name) {
                if let Some(last_value) = regmap.get(acc) {
                    if *v == *last_value {
                        return false;
                    }
                }
            };
            remove_affected_register_parts(&mut recent_reads, *name, &acc);
            let regmap = recent_reads.entry(*name).or_insert_with(HashMap::new);
            regmap.insert(acc.clone(), v.clone());
            true
        }
        WriteReg(name, acc, _v) => {
            remove_affected_register_parts(&mut recent_reads, *name, acc);
            true
        }
        _ => true,
    });
    for fork in &mut events.forks {
        remove_repeated_register_reads_core(&mut recent_reads.clone(), fork);
    }
}

pub fn remove_repeated_register_reads_tree<B: BV>(event_tree: &mut EventTree<B>) {
    remove_repeated_register_reads_core(&mut HashMap::new(), event_tree);
}

pub fn remove_unused_register_assumptions<B: BV>(events: &mut Vec<Event<B>>) {
    let mut unused_assumptions: HashMap<Name, HashMap<Vec<Accessor>, usize>> = HashMap::new();
    for (i, event) in events.iter().enumerate().rev() {
        match event {
            AssumeReg(name, accessor, _v) => {
                let regmap = unused_assumptions.entry(*name).or_insert_with(HashMap::new);
                regmap.insert(accessor.clone(), i);
            }
            ReadReg(name, accessor, _v) => remove_affected_register_parts(&mut unused_assumptions, *name, &accessor),
            WriteReg(name, accessor, _v) => {
                // Not strictly necessary in all cases, but keeps things simple
                remove_affected_register_parts(&mut unused_assumptions, *name, &accessor)
            }
            _ => (),
        }
    }
    let mut remove: HashSet<usize> = HashSet::new();
    for (_name, m) in unused_assumptions {
        for (_accessor, i) in m {
            remove.insert(i);
        }
    }
    let mut i = 0;
    events.retain(|_| {
        i += 1;
        !remove.contains(&(i - 1))
    })
}

fn unused_register_assumptions<B: BV>(
    depth: usize,
    previous_live_assumptions: &HashMap<Name, HashMap<Vec<Accessor>, (usize, usize)>>,
    used_assumptions: &mut HashSet<(usize, usize)>,
    event_tree: &mut EventTree<B>,
) {
    let mut live_assumptions = previous_live_assumptions.clone();
    for (i, event) in event_tree.prefix.iter().enumerate() {
        match event {
            AssumeReg(name, accessor, _v) => {
                let regmap = live_assumptions.entry(*name).or_insert_with(HashMap::new);
                regmap.insert(accessor.clone(), (depth, i));
            }
            ReadReg(name, accessor, _v) => {
                record_affected_register_parts(&mut live_assumptions, used_assumptions, *name, &accessor)
            }
            WriteReg(name, accessor, _v) => {
                // Not strictly necessary in all cases, but keeps things simple
                record_affected_register_parts(&mut live_assumptions, used_assumptions, *name, &accessor)
            }
            _ => (),
        }
    }
    for fork in &mut event_tree.forks {
        unused_register_assumptions(depth + 1, &live_assumptions, used_assumptions, fork);
    }
    let mut i = 0;
    event_tree.prefix.retain(|event| {
        i += 1;
        match event {
            AssumeReg(_, _, _) => used_assumptions.contains(&(depth, i - 1)),
            _ => true,
        }
    })
}

pub fn remove_unused_register_assumptions_tree<B: BV>(event_tree: &mut EventTree<B>) {
    unused_register_assumptions(0, &mut HashMap::new(), &mut HashSet::new(), event_tree);
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

pub fn remove_unused_tree<B: BV>(event_tree: &mut EventTree<B>) {
    loop {
        let uses = calculate_tree_uses(event_tree);
        if !remove_unused_pass_tree(event_tree, &uses) {
            break;
        }
    }
}

fn propagate_forwards_used_once_core<B: BV, E: BorrowMut<Event<B>>>(
    rev: bool,
    cross_segment: &HashSet<Sym>,
    events: &mut Vec<E>,
) {
    let uses = calculate_uses(&events);
    let required_uses = calculate_required_uses(&events);

    let mut substs: HashMap<Sym, Option<Exp<Sym>>> = HashMap::new();

    for (sym, count) in uses {
        if count == 1 && !cross_segment.contains(&sym) && !required_uses.contains_key(&sym) {
            substs.insert(sym, None);
        }
    }

    let mut keep = vec![true; events.len()];

    let it: Box<dyn Iterator<Item = (usize, &mut E)>> =
        if rev { Box::new(events.iter_mut().enumerate().rev()) } else { Box::new(events.iter_mut().enumerate()) };
    for (i, event) in it {
        match event.borrow_mut() {
            Event::Smt(Def::DefineConst(sym, exp), _) => {
                exp.subst_once_in_place(&mut substs);

                if substs.contains_key(&sym) {
                    let exp = std::mem::replace(exp, Exp::Bool(false));
                    keep[i] = false;
                    substs.insert(*sym, Some(exp));
                }
            }
            Event::Smt(Def::Assert(exp), _) => exp.subst_once_in_place(&mut substs),
            _ => (),
        }
    }

    let mut i = 0;
    events.retain(|_| {
        i += 1;
        keep[i - 1]
    })
}

/// This rewrite looks for events of the form `(define-const v
/// (expression))`, and if `v` is only used exactly once in subsequent
/// events it will replace that use of `v` by the expression.
pub fn propagate_forwards_used_once<B: BV, E: BorrowMut<Event<B>>>(events: &mut Vec<E>) {
    propagate_forwards_used_once_core(true, &HashSet::new(), events);
}

fn find_cross_segment_syms_descend<B: BV>(
    previously_defined: &HashSet<Sym>,
    event_tree: &EventTree<B>,
    cross_syms: &mut HashSet<Sym>,
) {
    let segment_uses = calculate_uses(&event_tree.prefix);
    for (sym, n) in segment_uses {
        if n > 0 && previously_defined.contains(&sym) {
            cross_syms.insert(sym);
        }
    }

    let mut now_defined = previously_defined.clone();
    for event in &event_tree.prefix {
        match event {
            Event::Smt(Def::DefineConst(sym, _exp), _) => {
                now_defined.insert(*sym);
            }
            _ => (),
        };
    }
    for fork in &event_tree.forks {
        find_cross_segment_syms_descend(&now_defined, fork, cross_syms);
    }
}

fn find_cross_segment_syms<B: BV>(event_tree: &EventTree<B>) -> HashSet<Sym> {
    let mut result = HashSet::new();
    find_cross_segment_syms_descend(&HashSet::new(), event_tree, &mut result);
    result
}

fn propagate_forwards_used_once_descent<B: BV>(cross_syms: &HashSet<Sym>, event_tree: &mut EventTree<B>) {
    propagate_forwards_used_once_core(false, cross_syms, &mut event_tree.prefix);
    for fork in &mut event_tree.forks {
        propagate_forwards_used_once_descent(cross_syms, fork);
    }
}

/// This is an event tree version of [propagate_forwards_used_once]
/// which only propagates within individual segments of the tree.
pub fn propagate_forwards_used_once_tree<B: BV>(event_tree: &mut EventTree<B>) {
    let cross_syms = find_cross_segment_syms(event_tree);
    propagate_forwards_used_once_descent(&cross_syms, event_tree);
}

/// Evaluate SMT subexpressions if all their arguments are constant
pub fn eval<B: BV, E: BorrowMut<Event<B>>>(events: &mut Vec<E>) {
    for event in events.iter_mut() {
        match event.borrow_mut() {
            Event::Smt(Def::DefineConst(_, exp), _) | Event::Smt(Def::Assert(exp), _) => {
                let e = std::mem::replace(exp, Exp::Bool(false));
                *exp = e.eval();
            }
            _ => (),
        }
    }
}

pub fn eval_tree<B: BV>(event_tree: &mut EventTree<B>) {
    event_tree.map(&eval);
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
            Event::Smt(Def::DefineConst(_, exp), _) | Event::Smt(Def::Assert(exp), _) => {
                exp.modify_top_down(&Exp::commute_extract)
            }
            _ => (),
        }
    }
}

pub fn commute_extract_tree<B: BV>(event_tree: &mut EventTree<B>) {
    event_tree.map(&commute_extract);
}

fn accessor_to_string(acc: &[Accessor], symtab: &Symtab) -> String {
    acc.iter()
        .map(|elem| elem.to_string(symtab))
        .fold(None, |acc, elem| if let Some(prefix) = acc { Some(format!("{} {}", prefix, elem)) } else { Some(elem) })
        .map_or("nil".to_string(), |acc| format!("({})", acc))
}

pub struct EventTree<B> {
    fork_id: Option<u32>,
    source_loc: SourceLoc,
    prefix: Vec<Event<B>>,
    forks: Vec<EventTree<B>>,
}

/// Each trace is split into sequences of events followed by fork
/// events where control flow splits. This function splits the trace
/// into the event sequences delimited by these forks. Each fork has a
/// number associated with it, which are attached to each event
/// sequence preceeding the fork. The sequence of events after the
/// last fork therefore have no associated number.
fn break_into_forks<B: BV, E: Borrow<Event<B>>>(events: &[E]) -> Vec<(Option<u32>, SourceLoc, &[E])> {
    let mut i = 0;
    let mut result = vec![];
    let mut current: Option<u32> = None;

    for (j, event) in events.iter().enumerate() {
        if let Event::Fork(_fork_no, _, branch_no, info) = event.borrow() {
            result.push((current, *info, &events[i..j]));
            i = j + 1;
            current = Some(*branch_no)
        }
    }
    result.push((current, SourceLoc::unknown(), &events[i..]));

    result
}

impl<B: BV> EventTree<B> {
    fn push<E: Borrow<Event<B>>>(&mut self, fork_id: Option<u32>, source_loc: SourceLoc, events: &[E]) {
        if self.forks.is_empty() {
            self.forks.push(EventTree {
                fork_id,
                source_loc,
                prefix: events.iter().map(|ev| ev.borrow().clone()).collect(),
                forks: vec![],
            })
        } else {
            self.forks[0].push(fork_id, source_loc, events)
        }
    }

    fn get_mut(&mut self, path: &[usize]) -> Option<&mut Self> {
        if path.is_empty() {
            Some(self)
        } else {
            self.forks.get_mut(path[0]).and_then(|child| child.get_mut(&path[1..]))
        }
    }

    fn get(&self, path: &[usize]) -> Option<&Self> {
        if path.is_empty() {
            Some(self)
        } else {
            self.forks.get(path[0]).and_then(|child| child.get(&path[1..]))
        }
    }

    fn from_broken_events<E: Borrow<Event<B>>>(broken: &[(Option<u32>, SourceLoc, &[E])]) -> Self {
        let mut evtree = EventTree {
            fork_id: broken[0].0,
            source_loc: broken[0].1,
            prefix: broken[0].2.iter().map(|ev| ev.borrow().clone()).collect(),
            forks: vec![],
        };

        for (fork_id, source_loc, events) in &broken[1..] {
            evtree.push(*fork_id, *source_loc, events)
        }

        evtree
    }

    pub fn from_events<E: Borrow<Event<B>>>(events: &[E]) -> Self {
        let broken = break_into_forks(events);
        Self::from_broken_events(&broken)
    }

    pub fn add_events<E: Borrow<Event<B>>>(&mut self, events: &[E]) {
        let broken = break_into_forks(events);

        let mut path: Vec<usize> = vec![];
        let mut new: Option<usize> = None;

        for (i, (fork_id, _, _)) in broken[1..].iter().enumerate() {
            if fork_id.is_some() {
                if let Some(pos) = self.get(&path).unwrap().forks.iter().position(|child| child.fork_id == *fork_id) {
                    path.push(pos);
                    continue;
                }
            }

            new = Some(i + 1);
            break;
        }

        if let Some(new) = new {
            self.get_mut(&path).unwrap().forks.push(Self::from_broken_events(&broken[new..]))
        }
    }

    /// Apply f to every section of trace in the event tree
    fn map(&mut self, f: &dyn Fn(&mut Vec<Event<B>>)) {
        f(&mut self.prefix);
        for fork in &mut self.forks {
            fork.map(f);
        }
    }

    pub fn sort(&mut self) {
        self.forks.sort_by_key(|fork| fork.fork_id);
        for fork in &mut self.forks {
            fork.sort();
        }
    }
}

/// Options for writing event traces
#[derive(Clone)]
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
    /// A directory containing the original Sail source code for the
    /// IR.
    pub source_directory: Option<PathBuf>,
    /// Extra indentation level
    pub indent: usize,
    /// Don't print last closing paren
    pub prefix: bool,
}

impl WriteOpts {
    pub fn smtlib() -> Self {
        WriteOpts {
            variable_prefix: "v".to_string(),
            enum_prefix: "e".to_string(),
            types: true,
            just_smt: true,
            define_enum: false,
            source_directory: None,
            indent: 0,
            prefix: false,
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
            source_directory: None,
            indent: 0,
            prefix: false,
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

fn write_ty(buf: &mut dyn Write, ty: &Ty, enums: &[usize]) -> std::io::Result<()> {
    use Ty::*;
    match ty {
        Bool => write!(buf, "Bool"),
        BitVec(sz) => write!(buf, "(_ BitVec {})", sz),
        Enum(e) => write!(buf, "Enum{}", enums[*e]),
        Array(dom, codom) => {
            write!(buf, "(Array ")?;
            write_ty(buf, dom, enums)?;
            write!(buf, " ")?;
            write_ty(buf, codom, enums)?;
            write!(buf, ")")
        }
    }
}

trait WriteVar {
    fn write_var(&self, buf: &mut dyn Write, opts: &WriteOpts) -> std::io::Result<()>;
}

impl WriteVar for Sym {
    fn write_var(&self, buf: &mut dyn Write, opts: &WriteOpts) -> std::io::Result<()> {
        write!(buf, "{}{}", opts.variable_prefix, self)
    }
}

impl WriteVar for Loc<String> {
    fn write_var(&self, buf: &mut dyn Write, _opts: &WriteOpts) -> std::io::Result<()> {
        match self {
            Loc::Id(name) => write!(buf, "(|{}| nil)", zencode::decode(name)),
            _ => {
                write!(buf, "(|{}| (", zencode::decode(&self.id()))?;
                let mut l = self;
                loop {
                    match l {
                        Loc::Id(_) => break,
                        Loc::Field(loc, name) => {
                            write!(buf, "(_ field |{}|) ", zencode::decode(name))?;
                            l = loc
                        }
                        Loc::Addr(loc) => l = loc,
                    }
                }
                write!(buf, "))")
            }
        }
    }
}

fn write_exp<V: WriteVar>(buf: &mut dyn Write, exp: &Exp<V>, opts: &WriteOpts, enums: &[usize]) -> std::io::Result<()> {
    use Exp::*;
    match exp {
        Var(v) => v.write_var(buf, opts),
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
        Distinct(exps) => {
            write!(buf, "(distinct")?;
            for exp in exps {
                write!(buf, " ")?;
                write_exp(buf, exp, opts, enums)?;
            }
            write!(buf, ")")
        }
    }
}

fn write_unop<V: WriteVar>(
    buf: &mut dyn Write,
    op: &str,
    exp: &Exp<V>,
    opts: &WriteOpts,
    enums: &[usize],
) -> std::io::Result<()> {
    write!(buf, "({} ", op)?;
    write_exp(buf, exp, opts, enums)?;
    write!(buf, ")")
}

fn write_binop<V: WriteVar>(
    buf: &mut dyn Write,
    op: &str,
    lhs: &Exp<V>,
    rhs: &Exp<V>,
    opts: &WriteOpts,
    enums: &[usize],
) -> std::io::Result<()> {
    write!(buf, "({} ", op)?;
    write_exp(buf, lhs, opts, enums)?;
    write!(buf, " ")?;
    write_exp(buf, rhs, opts, enums)?;
    write!(buf, ")")
}

pub fn write_events_in_context<B: BV>(
    buf: &mut dyn Write,
    events: &[Event<B>],
    symtab: &Symtab,
    opts: &WriteOpts,
    tcx: &mut Cow<HashMap<Sym, Ty>>,
    ftcx: &mut Cow<HashMap<Sym, (Vec<Ty>, Ty)>>,
    enums: &mut Cow<Vec<usize>>,
) -> std::io::Result<()> {
    let indent = " ".repeat(opts.indent);

    if !opts.just_smt {
        write!(buf, "{}(trace", indent).unwrap();
    }
    for event in events.iter().filter(|ev| !opts.just_smt || ev.is_smt()) {
        (match event {
            // TODO: rename this
            Fork(n, _, _, loc) => write!(buf, "\n{}  (branch {} \"{}\")", indent, n, loc.location_string(symtab.files())),

            Function { name, call } => {
                let name = zencode::decode(symtab.to_str(*name));
                if *call {
                    write!(buf, "\n{}  (call |{}|)", indent, name)
                } else {
                    write!(buf, "\n{}  (return |{}|)", indent, name)
                }
            }

            Smt(Def::DefineEnum(_, size), _) if !opts.define_enum => {
                enums.to_mut().push(*size);
                Ok(())
            }

            Smt(def, loc) => {
                if opts.just_smt {
                    write!(buf, "\n{}", indent)?
                } else {
                    write!(buf, "\n{}  ", indent)?;
                }
                match def {
                    Def::DeclareConst(v, ty) => {
                        tcx.to_mut().insert(*v, ty.clone());
                        write!(buf, "(declare-const {}{} ", opts.variable_prefix, v)?;
                        write_ty(buf, ty, enums)?;
                        write!(buf, ")")?
                    }
                    Def::DeclareFun(v, arg_tys, result_ty) => {
                        ftcx.to_mut().insert(*v, (arg_tys.clone(), result_ty.clone()));
                        write!(buf, "(declare_fun {}{} (", opts.variable_prefix, v)?;
                        for ty in arg_tys {
                            write_ty(buf, ty, enums)?;
                            write!(buf, " ")?
                        }
                        write!(buf, ") ")?;
                        write_ty(buf, result_ty, enums)?;
                        write!(buf, ")")?
                    }
                    Def::DefineConst(v, exp) => {
                        if opts.types {
                            let ty = exp.infer(&tcx, &ftcx).expect("SMT expression was badly-typed");
                            tcx.to_mut().insert(*v, ty.clone());
                            write!(buf, "(define-const v{} ", v)?;
                            write_ty(buf, &ty, enums)?;
                            write!(buf, " ")?;
                            write_exp(buf, exp, opts, &enums)?;
                            write!(buf, ")")?
                        } else {
                            write!(buf, "(define-const v{} ", v)?;
                            write_exp(buf, exp, opts, &enums)?;
                            write!(buf, ")")?;
                        }
                    }
                    Def::DefineEnum(_, size) => {
                        if !opts.just_smt {
                            write!(buf, "(define-enum {})", size)?
                        }
                        enums.to_mut().push(*size);
                    }
                    Def::Assert(exp) => {
                        write!(buf, "(assert ")?;
                        write_exp(buf, exp, opts, &enums)?;
                        write!(buf, ")")?;
                    }
                }
                if let Some(dir) = &opts.source_directory {
                    write!(buf, "\n{}", loc.message(dir, symtab.files(), "", false, true))?;
                }
                Ok(())
            }

            ReadMem { value, read_kind, address, bytes, tag_value, kind: _ } => write!(
                buf,
                "\n{}  (read-mem {} {} {} {} {})",
                indent,
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
                "\n{}  (write-mem v{} {} {} {} {} {})",
                indent,
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

            Branch { address } => write!(buf, "\n{}  (branch-address {})", indent, address.to_string(symtab)),

            Barrier { barrier_kind } => write!(buf, "\n{}  (barrier {})", indent, barrier_kind.to_string(symtab)),

            CacheOp { cache_op_kind, address, extra_data: _ } => write!(
                buf,
                "\n{}  (cache-op {} {})",
                indent,
                cache_op_kind.to_string(symtab),
                address.to_string(symtab)
            ),

            WriteReg(n, acc, v) => write!(
                buf,
                "\n{}  (write-reg |{}| {} {})",
                indent,
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
                        "\n{}  (read-reg |{}| {} {})",
                        indent,
                        zencode::decode(symtab.to_str(*n)),
                        accessor_to_string(acc, symtab),
                        v.to_string(symtab)
                    )
                }
            }

            MarkReg { regs, mark } => {
                for reg in regs {
                    write!(buf, "\n{}  (mark-reg |{}| \"{}\")", indent, zencode::decode(symtab.to_str(*reg)), mark)?
                }
                Ok(())
            }

            Cycle => write!(buf, "\n{}  (cycle)", indent),

            Instr(value) => write!(buf, "\n{}  (instr {})", indent, value.to_string(symtab)),

            Sleeping(sym) => write!(buf, "\n{}  (sleeping v{})", indent, sym),

            SleepRequest => write!(buf, "\n{}  (sleep-request)", indent),

            WakeupRequest => write!(buf, "\n{}  (wake-request)", indent),

            Assume(constraint) => {
                write!(buf, "\n{}  (assume ", indent)?;
                let assume_opts = WriteOpts { variable_prefix: "".to_string(), ..opts.clone() };
                write_exp(buf, constraint, &assume_opts, &enums)?;
                write!(buf, ")")
            }

            AssumeReg(n, acc, v) => {
                write!(
                    buf,
                    "\n{}  (assume-reg |{}| {} {})",
                    indent,
                    zencode::decode(symtab.to_str(*n)),
                    accessor_to_string(acc, symtab),
                    v.to_string(symtab)
                )
            }
        })?
    }
    if !(opts.just_smt || opts.prefix) {
        writeln!(buf, ")")?;
    }
    Ok(())
}

pub fn write_events_with_opts<B: BV>(
    buf: &mut dyn Write,
    events: &[Event<B>],
    symtab: &Symtab,
    opts: &WriteOpts,
) -> std::io::Result<()> {
    let tcx: HashMap<Sym, Ty> = HashMap::new();
    let ftcx: HashMap<Sym, (Vec<Ty>, Ty)> = HashMap::new();
    let enums: Vec<usize> = Vec::new();

    write_events_in_context(
        buf,
        events,
        symtab,
        opts,
        &mut Cow::Owned(tcx),
        &mut Cow::Owned(ftcx),
        &mut Cow::Owned(enums),
    )
}

pub fn write_events<B: BV>(buf: &mut dyn Write, events: &[Event<B>], symtab: &Symtab) {
    write_events_with_opts(buf, events, symtab, &WriteOpts::default()).unwrap()
}

fn write_event_tree_with_opts<B: BV>(
    buf: &mut dyn Write,
    evtree: &EventTree<B>,
    symtab: &Symtab,
    opts: &mut WriteOpts,
    tcx: &mut Cow<HashMap<Sym, Ty>>,
    ftcx: &mut Cow<HashMap<Sym, (Vec<Ty>, Ty)>>,
    enums: &mut Cow<Vec<usize>>,
) -> std::io::Result<()> {
    write_events_in_context(buf, &evtree.prefix, symtab, opts, tcx, ftcx, enums)?;

    if !evtree.forks.is_empty() {
        write!(buf, "\n{}  (forks \"{}\"", " ".repeat(opts.indent), evtree.source_loc.location_string(symtab.files()))?;
        opts.indent += 4;
        for fork in &evtree.forks {
            writeln!(buf)?;
            write_event_tree_with_opts(
                buf,
                fork,
                symtab,
                opts,
                &mut Cow::Borrowed(&tcx),
                &mut Cow::Borrowed(&ftcx),
                &mut Cow::Borrowed(&enums),
            )?
        }
        opts.indent -= 4;
        write!(buf, "))")?;
    } else {
        write!(buf, ")")?;
    }

    Ok(())
}

pub fn write_event_tree<B: BV>(buf: &mut dyn Write, evtree: &EventTree<B>, symtab: &Symtab) {
    let mut opts = WriteOpts { prefix: true, ..WriteOpts::default() };
    let tcx: HashMap<Sym, Ty> = HashMap::new();
    let ftcx: HashMap<Sym, (Vec<Ty>, Ty)> = HashMap::new();
    let enums: Vec<usize> = Vec::new();

    write_event_tree_with_opts(
        buf,
        evtree,
        symtab,
        &mut opts,
        &mut Cow::Owned(tcx),
        &mut Cow::Owned(ftcx),
        &mut Cow::Owned(enums),
    )
    .unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::ir::source_loc::SourceLoc;

    #[test]
    fn break_forks_simple() {
        let events: Vec<Event<B64>> =
            vec![Event::SleepRequest, Event::Fork(0, Sym::from_u32(0), 0, SourceLoc::unknown()), Event::WakeupRequest];

        let broken = break_into_forks(&events);

        assert_eq!(broken.len(), 2);
        assert_eq!(broken[0].0, None);
        assert!(matches!(broken[0].2[0], Event::SleepRequest));
        assert_eq!(broken[0].2.len(), 1);
        assert_eq!(broken[1].0, Some(0));
        assert!(matches!(broken[1].2[0], Event::WakeupRequest));
        assert_eq!(broken[1].2.len(), 1);
    }

    #[test]
    fn break_forks_empty() {
        let events: Vec<Event<B64>> = vec![Event::Fork(0, Sym::from_u32(0), 0, SourceLoc::unknown())];

        let broken = break_into_forks(&events);

        assert_eq!(broken.len(), 2);
        assert_eq!(broken[0].0, None);
        assert_eq!(broken[0].2.len(), 0);
        assert_eq!(broken[1].0, Some(0));
        assert_eq!(broken[1].2.len(), 0);
    }

    #[test]
    fn evtree_add_events() {
        let events1: Vec<Event<B64>> =
            vec![Event::SleepRequest, Event::Fork(0, Sym::from_u32(0), 0, SourceLoc::unknown()), Event::WakeupRequest];
        let events2: Vec<Event<B64>> =
            vec![Event::SleepRequest, Event::Fork(0, Sym::from_u32(0), 0, SourceLoc::unknown()), Event::SleepRequest];

        let mut evtree = EventTree::from_events(&events1);
        evtree.add_events(&events2);
    }

    #[test]
    fn evtree_context() {
        use crate::ir::EnumMember;
        let events1: Vec<Event<B64>> = vec![
            Event::Smt(Def::DefineEnum(Sym::from_u32(0), 2), SourceLoc::unknown()),
            Event::Fork(0, Sym::from_u32(1), 0, SourceLoc::unknown()),
            Event::Smt(
                Def::DefineConst(Sym::from_u32(2), Exp::Enum(EnumMember { enum_id: 0, member: 0 })),
                SourceLoc::unknown(),
            ),
        ];
        let events2: Vec<Event<B64>> = vec![
            Event::Smt(Def::DefineEnum(Sym::from_u32(0), 2), SourceLoc::unknown()),
            Event::Fork(0, Sym::from_u32(1), 0, SourceLoc::unknown()),
            Event::SleepRequest,
        ];

        let mut evtree = EventTree::from_events(&events1);
        evtree.add_events(&events2);
        let stdout = std::io::stdout();
        let mut handle = stdout.lock();
        write_event_tree(&mut handle, &evtree, &Symtab::new());
    }

    #[test]
    fn remove_repeated_regs() {
        let event = Event::ReadReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x123)));
        let mut events: Vec<Event<B64>> = vec![event.clone(), Event::WakeupRequest, event];
        remove_repeated_register_reads(&mut events);
        assert_eq!(events.len(), 2);
        assert!(matches!(events[0], Event::WakeupRequest));

        // We shouldn't see consecutive reads with different values,
        // but we want to keep them if we do.
        let event_1 = Event::ReadReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x123)));
        let event_2 = Event::ReadReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x456)));
        let mut events: Vec<Event<B64>> = vec![event_1, Event::WakeupRequest, event_2];
        remove_repeated_register_reads(&mut events);
        assert_eq!(events.len(), 3);
        assert!(matches!(events[1], Event::WakeupRequest));

        let event_r = Event::ReadReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x123)));
        let event_w = Event::WriteReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x123)));
        let mut events: Vec<Event<B64>> = vec![event_r.clone(), Event::WakeupRequest, event_w, event_r];
        remove_repeated_register_reads(&mut events);
        assert_eq!(events.len(), 4);
        assert!(matches!(events[1], Event::WakeupRequest));

        let field_1 = Accessor::Field(Name::from_u32(1));
        let field_2 = Accessor::Field(Name::from_u32(2));
        let val = Val::Bits(B64::from_u64(0x123));
        let val_2 = Val::Struct([(Name::from_u32(2), val)].iter().cloned().collect());
        let val_1 = Val::Struct([(Name::from_u32(1), val_2.clone())].iter().cloned().collect());
        let event_r = Event::ReadReg(Name::from_u32(0), vec![field_1.clone(), field_2], val_1);
        let event_w = Event::WriteReg(Name::from_u32(0), vec![field_1], val_2);
        let mut events: Vec<Event<B64>> = vec![event_r.clone(), Event::WakeupRequest, event_w, event_r];
        remove_repeated_register_reads(&mut events);
        assert_eq!(events.len(), 4);
        assert!(matches!(events[1], Event::WakeupRequest));
    }

    #[test]
    fn remove_unnecessary_reg_assumptions() {
        let field_1 = Accessor::Field(Name::from_u32(1));
        let field_2 = Accessor::Field(Name::from_u32(2));
        let val = Val::Bits(B64::from_u64(0x123)); // Values don't matter here
        let event_a = Event::AssumeReg(Name::from_u32(0), vec![field_1.clone(), field_2.clone()], val.clone());
        let event_r = Event::ReadReg(Name::from_u32(0), vec![field_1.clone()], val.clone());
        let mut events: Vec<Event<B64>> = vec![event_r.clone(), event_a.clone()];
        remove_unused_register_assumptions(&mut events);
        assert_eq!(events.len(), 2);

        // We could remove the assumption here, but I decided to keep things simple
        let event_w = Event::WriteReg(Name::from_u32(0), vec![], val.clone());
        let mut events: Vec<Event<B64>> = vec![event_r.clone(), event_w.clone(), event_a.clone()];
        remove_unused_register_assumptions(&mut events);
        assert_eq!(events.len(), 3);

        // An earlier write shouldn't stop the assumption being removed
        // (important because a write will appear for each assume)
        let event_w = Event::WriteReg(Name::from_u32(0), vec![], val.clone());
        let mut events: Vec<Event<B64>> = vec![event_r.clone(), event_a.clone(), event_w.clone()];
        remove_unused_register_assumptions(&mut events);
        assert_eq!(events.len(), 3);

        let event_r = Event::ReadReg(Name::from_u32(1), vec![field_1.clone(), field_2.clone()], val);
        let mut events: Vec<Event<B64>> = vec![event_r.clone(), event_a.clone()];
        remove_unused_register_assumptions(&mut events);
        assert_eq!(events.len(), 1);
        assert!(matches!(events[0], Event::ReadReg(_, _, _)));
    }
}
