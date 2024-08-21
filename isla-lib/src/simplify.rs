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
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::io::{Error, ErrorKind, Write};

use crate::bitvector::{write_bits64, BV};
use crate::ir::{BitsSegment, Loc, Name, SharedState, Symtab, Val, HAVE_EXCEPTION};
use crate::smt::smtlib::{self, *};
use crate::smt::Event::*;
use crate::smt::{Accessor, Event, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;

/// `renumber_event` Renumbers all the symbolic variables in an event such that multiple event
/// sequences can have disjoint variable identifiers. It takes two `u32` arguments `i` and `total`,
/// such that `i` is the index of our event sequence in the range `0..(total - 1)` inclusive where
/// `total` is the number of event sequences we want to make disjoint.
#[allow(clippy::unneeded_field_pattern)]
pub fn renumber_event<B, F>(event: &mut Event<B>, f: &mut F)
where
    F: FnMut(u32) -> u32,
{
    use Event::*;
    match event {
        Smt(def, _, _) => renumber_def(def, f),
        Fork(_, v, _, _) => *v = Sym { id: f(v.id) },
        Abstract { name: _, primitive: _, args, return_value } => {
            for arg in args.iter_mut() {
                renumber_val(arg, f)
            }
            renumber_val(return_value, f)
        }
        AssumeFun { name: _, args, return_value } | UseFunAssumption { name: _, args, return_value } => {
            for arg in args.iter_mut() {
                renumber_val(arg, f)
            }
            renumber_val(return_value, f)
        }
        ReadReg(_, _, value) | WriteReg(_, _, value) | Instr(value) | AssumeReg(_, _, value) => renumber_val(value, f),
        AddressAnnounce { address } => renumber_val(address, f),
        Branch { address } => renumber_val(address, f),
        ReadMem { value, read_kind, address, bytes: _, tag_value, opts: _, region: _ } => {
            renumber_val(value, f);
            renumber_val(read_kind, f);
            renumber_val(address, f);
            if let Some(v) = tag_value {
                renumber_val(v, f);
            }
        }
        WriteMem { value: v, write_kind, address, data, bytes: _, tag_value, opts: _, region: _ } => {
            *v = Sym { id: f(v.id) };
            renumber_val(write_kind, f);
            renumber_val(address, f);
            renumber_val(data, f);
            if let Some(v) = tag_value {
                renumber_val(v, f);
            }
        }
        Cycle | MarkReg { .. } | Function { .. } | Assume(_) => (),
    }
}

fn renumber_exp<F>(exp: &mut Exp<Sym>, f: &mut F)
where
    F: FnMut(u32) -> u32,
{
    exp.modify(
        &mut (|exp| {
            if let Exp::Var(v) = exp {
                *v = Sym { id: f(v.id) }
            }
        }),
    )
}

fn renumber_val<B, F>(val: &mut Val<B>, f: &mut F)
where
    F: FnMut(u32) -> u32,
{
    use Val::*;
    match val {
        Symbolic(v) => *v = Sym { id: f(v.id) },
        MixedBits(segments) => segments.iter_mut().for_each(|segment| match segment {
            BitsSegment::Symbolic(v) => *v = Sym { id: f(v.id) },
            BitsSegment::Concrete(_) => (),
        }),
        I64(_) | I128(_) | Bool(_) | Bits(_) | Enum(_) | String(_) | Unit | Ref(_) | Poison => (),
        List(vals) | Vector(vals) => vals.iter_mut().for_each(|val| renumber_val(val, f)),
        Struct(fields) => fields.iter_mut().for_each(|(_, val)| renumber_val(val, f)),
        Ctor(_, val) => renumber_val(val, f),
        SymbolicCtor(v, possibilities) => {
            *v = Sym { id: f(v.id) };
            possibilities.iter_mut().for_each(|(_, val)| renumber_val(val, f))
        }
    }
}

fn renumber_def<F>(def: &mut Def, f: &mut F)
where
    F: FnMut(u32) -> u32,
{
    use Def::*;
    match def {
        DeclareConst(v, _) | DeclareFun(v, _, _) => *v = Sym { id: f(v.id) },
        DefineConst(v, exp) => {
            *v = Sym { id: f(v.id) };
            renumber_exp(exp, f)
        }
        Assert(exp) => renumber_exp(exp, f),
        DefineEnum(..) => (),
    }
}

/// `uses_in_exp` counts the number of occurences of each variable in an SMTLIB expression.
fn uses_in_exp(uses: &mut HashMap<Sym, u32>, exp: &Exp<Sym>) {
    use Exp::*;
    match exp {
        Var(v) => {
            uses.insert(*v, uses.get(v).unwrap_or(&0) + 1);
        }
        Bits(_) | Bits64(_) | Enum(_) | Bool(_) | FPConstant(..) | FPRoundingMode(_) => (),
        Not(exp)
        | Bvnot(exp)
        | Bvneg(exp)
        | Extract(_, _, exp)
        | ZeroExtend(_, exp)
        | SignExtend(_, exp)
        | FPUnary(_, exp) => uses_in_exp(uses, exp),
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
        | Concat(lhs, rhs)
        | FPBinary(_, lhs, rhs) => {
            uses_in_exp(uses, lhs);
            uses_in_exp(uses, rhs)
        }
        Ite(cond, then_exp, else_exp) => {
            uses_in_exp(uses, cond);
            uses_in_exp(uses, then_exp);
            uses_in_exp(uses, else_exp)
        }
        App(f, args) => {
            uses.insert(*f, uses.get(f).unwrap_or(&0) + 1);
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
        FPRoundingUnary(_, rm, exp) => {
            uses_in_exp(uses, rm);
            uses_in_exp(uses, exp);
        }
        FPRoundingBinary(_, rm, lhs, rhs) => {
            uses_in_exp(uses, rm);
            uses_in_exp(uses, lhs);
            uses_in_exp(uses, rhs)
        }
        FPfma(rm, x, y, z) => {
            uses_in_exp(uses, rm);
            uses_in_exp(uses, x);
            uses_in_exp(uses, y);
            uses_in_exp(uses, z)
        }
    }
}

fn uses_in_value<B>(uses: &mut HashMap<Sym, u32>, val: &Val<B>) {
    use Val::*;
    match val {
        Symbolic(v) => {
            uses.insert(*v, uses.get(v).unwrap_or(&0) + 1);
        }
        MixedBits(segments) => segments.iter().for_each(|segment| match segment {
            BitsSegment::Symbolic(v) => {
                uses.insert(*v, uses.get(v).unwrap_or(&0) + 1);
            }
            BitsSegment::Concrete(_) => (),
        }),
        I64(_) | I128(_) | Bool(_) | Bits(_) | Enum(_) | String(_) | Unit | Ref(_) | Poison => (),
        List(vals) | Vector(vals) => vals.iter().for_each(|val| uses_in_value(uses, val)),
        Struct(fields) => fields.iter().for_each(|(_, val)| uses_in_value(uses, val)),
        Ctor(_, val) => uses_in_value(uses, val),
        SymbolicCtor(v, possibilities) => {
            uses.insert(*v, uses.get(v).unwrap_or(&0) + 1);
            possibilities.iter().for_each(|(_, val)| uses_in_value(uses, val))
        }
    }
}

#[derive(Debug, Clone, serde::Deserialize, serde::Serialize)]
pub struct Taints {
    pub registers: HashSet<(Name, Vec<Accessor>)>,
    pub memory: bool,
}

impl Taints {
    pub fn new() -> Self {
        Self { registers: HashSet::new(), memory: false }
    }
}

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
            if let Smt(Def::DefineConst(id, exp), _, _) = event.borrow() {
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
                    let immediate_deps = self.references.get(symbol).unwrap_or(&empty_map);
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
    pub fn taints<B: BV, E: Borrow<Event<B>>>(&self, symbol: Sym, events: &[E]) -> Taints {
        let mut taints = Taints::new();
        self.collect_taints(symbol, events, &mut taints);
        taints
    }

    /// Like `taints` but for all symbolic variables in a value
    pub fn value_taints<B: BV, E: Borrow<Event<B>>>(&self, val: &Val<B>, events: &[E]) -> Taints {
        let mut taints = Taints::new();
        self.collect_value_taints(val, events, &mut taints);
        taints
    }

    pub fn collect_taints<B: BV, E: Borrow<Event<B>>>(&self, symbol: Sym, events: &[E], taints: &mut Taints) {
        let deps = self.dependencies(symbol);

        for event in events.iter() {
            match event.borrow() {
                ReadReg(reg, accessor, value) => {
                    let mut uses = HashMap::new();
                    uses_in_value(&mut uses, value);
                    for (taint, _) in uses.iter() {
                        if deps.contains(taint) {
                            taints.registers.insert((*reg, accessor.clone()));
                            break;
                        }
                    }
                }

                ReadMem { value: Val::Symbolic(taint), .. } if deps.contains(taint) => taints.memory = true,
                ReadMem { tag_value: Some(Val::Symbolic(taint)), .. } if deps.contains(taint) => taints.memory = true,

                _ => (),
            }
        }
    }

    pub fn collect_value_taints<B: BV, E: Borrow<Event<B>>>(&self, val: &Val<B>, events: &[E], taints: &mut Taints) {
        for symbol in val.symbolic_variables() {
            self.collect_taints(symbol, events, taints)
        }
    }
}

#[allow(clippy::unneeded_field_pattern)]
fn calculate_more_uses<B, E: Borrow<Event<B>>>(events: &[E], uses: &mut HashMap<Sym, u32>) {
    for event in events.iter().rev() {
        use Event::*;
        match event.borrow() {
            Smt(Def::DeclareConst(_, _), _, _) => (),
            Smt(Def::DeclareFun(_, _, _), _, _) => (),
            Smt(Def::DefineConst(_, exp), _, _) => uses_in_exp(uses, exp),
            Smt(Def::DefineEnum(..), _, _) => (),
            Smt(Def::Assert(exp), _, _) => uses_in_exp(uses, exp),
            Abstract { name: _, primitive: _, args, return_value } => {
                for arg in args {
                    uses_in_value(uses, arg)
                }
                uses_in_value(uses, return_value)
            }
            AssumeFun { name: _, args, return_value } | UseFunAssumption { name: _, args, return_value } => {
                for arg in args {
                    uses_in_value(uses, arg)
                }
                uses_in_value(uses, return_value)
            }
            ReadReg(_, _, val) => uses_in_value(uses, val),
            WriteReg(_, _, val) => uses_in_value(uses, val),
            ReadMem { value: val, read_kind, address, bytes: _, tag_value, opts: _, region: _ } => {
                uses_in_value(uses, val);
                uses_in_value(uses, read_kind);
                uses_in_value(uses, address);
                if let Some(v) = tag_value {
                    uses_in_value(uses, v);
                }
            }
            WriteMem { value: sym, write_kind, address, data, bytes: _, tag_value, opts: _, region: _ } => {
                uses.insert(*sym, uses.get(sym).unwrap_or(&0) + 1);
                uses_in_value(uses, write_kind);
                uses_in_value(uses, address);
                uses_in_value(uses, data);
                if let Some(v) = tag_value {
                    uses_in_value(uses, v);
                }
            }
            AddressAnnounce { address } => uses_in_value(uses, address),
            Branch { address } => uses_in_value(uses, address),
            Fork(_, sym, _, _) => {
                uses.insert(*sym, uses.get(sym).unwrap_or(&0) + 1);
            }
            Cycle => (),
            Instr(val) => uses_in_value(uses, val),
            MarkReg { .. } => (),
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
            Smt(Def::DeclareConst(sym, _), _, _) => {
                uses.insert(*sym, uses.get(sym).unwrap_or(&0) + 1);
            }
            Smt(Def::DeclareFun(sym, _, _), _, _) => {
                uses.insert(*sym, uses.get(sym).unwrap_or(&0) + 1);
            }
            Smt(..) => (),
            Abstract { name: _, primitive: _, args, return_value } => {
                for arg in args {
                    uses_in_value(&mut uses, arg)
                }
                uses_in_value(&mut uses, return_value)
            }
            AssumeFun { name: _, args, return_value } | UseFunAssumption { name: _, args, return_value } => {
                for arg in args {
                    uses_in_value(&mut uses, arg)
                }
                uses_in_value(&mut uses, return_value)
            }
            ReadReg(_, _, val) => uses_in_value(&mut uses, val),
            WriteReg(_, _, val) => uses_in_value(&mut uses, val),
            ReadMem { value: val, read_kind, address, bytes: _, tag_value, opts: _, region: _ } => {
                uses_in_value(&mut uses, val);
                uses_in_value(&mut uses, read_kind);
                uses_in_value(&mut uses, address);
                if let Some(v) = tag_value {
                    uses_in_value(&mut uses, v);
                }
            }
            WriteMem { value: sym, write_kind, address, data, bytes: _, tag_value, opts: _, region: _ } => {
                uses.insert(*sym, uses.get(sym).unwrap_or(&0) + 1);
                uses_in_value(&mut uses, write_kind);
                uses_in_value(&mut uses, address);
                uses_in_value(&mut uses, data);
                if let Some(v) = tag_value {
                    uses_in_value(&mut uses, v);
                }
            }
            AddressAnnounce { address } => uses_in_value(&mut uses, address),
            Branch { address } => uses_in_value(&mut uses, address),
            Fork(_, sym, _, _) => {
                uses.insert(*sym, uses.get(sym).unwrap_or(&0) + 1);
            }
            Cycle => (),
            Instr(val) => uses_in_value(&mut uses, val),
            MarkReg { .. } => (),
            Function { .. } => (),
            Assume(_) => (),
            AssumeReg(_, _, val) => uses_in_value(&mut uses, val),
        }
    }

    uses
}

fn remove_unused_pass<B, E: Borrow<Event<B>>>(events: &mut Vec<E>) -> u32 {
    let uses = calculate_uses(events);
    let mut removed = 0;

    events.retain(|event| match event.borrow() {
        Smt(Def::DeclareConst(v, _), _, _) => {
            if uses.contains_key(v) {
                true
            } else {
                removed += 1;
                false
            }
        }
        Smt(Def::DefineConst(v, _), _, _) => {
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

    event_tree.prefix.retain(|event| match event {
        Smt(Def::DeclareConst(v, _), _, _) => {
            if uses.contains_key(v) {
                true
            } else {
                removed = true;
                false
            }
        }
        Smt(Def::DefineConst(v, _), _, _) => {
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

fn drop_shadowed_register_parts<V: Eq + std::hash::Hash + Copy>(
    register_map: &mut HashMap<Name, HashMap<Vec<Accessor>, V>>,
    name: Name,
    acc: &[Accessor],
) {
    if let Some(regmap) = register_map.get_mut(&name) {
        regmap.retain(|element_acc, _v| !element_acc.starts_with(acc));
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
                remove_affected_register_parts(&mut recent_reads, *name, acc);
                let regmap = recent_reads.entry(*name).or_default();
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
    recent_reads: &mut HashMap<Name, HashMap<Vec<Accessor>, Val<B>>>,
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
            remove_affected_register_parts(recent_reads, *name, acc);
            let regmap = recent_reads.entry(*name).or_default();
            regmap.insert(acc.clone(), v.clone());
            true
        }
        WriteReg(name, acc, _v) => {
            remove_affected_register_parts(recent_reads, *name, acc);
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
                let regmap = live_assumptions.entry(*name).or_default();
                regmap.insert(accessor.clone(), (depth, i));
            }
            ReadReg(name, accessor, _v) => {
                record_affected_register_parts(&mut live_assumptions, used_assumptions, *name, accessor)
            }
            WriteReg(name, accessor, _v) => {
                // Note that we only remove assumptions when a single write completely shadows them.
                // This doesn't remove assumptions when each subfield has been separately written,
                // even though that would be sound.
                drop_shadowed_register_parts(&mut live_assumptions, *name, accessor)
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
    unused_register_assumptions(0, &HashMap::new(), &mut HashSet::new(), event_tree);
}

pub fn remove_unused_register_assumptions<B: BV>(events: &mut Vec<Event<B>>) {
    let mut tree = EventTree {
        fork_id: None,
        source_loc: SourceLoc::unknown(),
        prefix: events.drain(..).rev().collect(),
        forks: vec![],
    };
    remove_unused_register_assumptions_tree(&mut tree);
    events.extend(tree.prefix.drain(..).rev());
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

/// Removes SMT events that are not used by any observable event (such
/// as a memory read or write).  Note: this doesn't check the scope of
/// variables when deciding what to remove, so renumber the event tree
/// before using this to ensure that all dead definitions are removed.
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
    let uses = calculate_uses(events);
    let required_uses = calculate_required_uses(events);

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
            Event::Smt(Def::DefineConst(sym, exp), _, _) => {
                exp.subst_once_in_place(&mut substs);

                if substs.contains_key(sym) {
                    let exp = std::mem::replace(exp, Exp::Bool(false));
                    keep[i] = false;
                    substs.insert(*sym, Some(exp));
                }
            }
            Event::Smt(Def::Assert(exp), _, _) => exp.subst_once_in_place(&mut substs),
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
            Event::Smt(Def::DeclareConst(sym, _), _, _) | Event::Smt(Def::DefineConst(sym, _), _, _) => {
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
            Event::Smt(Def::DefineConst(_, exp), _, _) | Event::Smt(Def::Assert(exp), _, _) => {
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

// Version that checks the results of eval using Z3

pub fn eval_carefully_part<B: BV, E: BorrowMut<Event<B>>>(
    events: &mut Vec<E>,
    tcx: &mut Cow<HashMap<Sym, Ty>>,
    ftcx: &mut Cow<HashMap<Sym, (Vec<Ty>, Ty)>>,
) {
    use crate::smt::{SmtResult::*, *};
    let cfg = Config::new();
    let ctx = Context::new(cfg);
    let mut solver = Solver::<B>::new(&ctx);
    for (v, ty) in tcx.iter() {
        solver.add(Def::DeclareConst(*v, ty.clone()))
    }

    for event in events.iter_mut() {
        match event.borrow_mut() {
            Event::Smt(Def::DeclareConst(v, ty), _, l) => {
                solver.add_with_location(Def::DeclareConst(*v, ty.clone()), *l);
                tcx.to_mut().insert(*v, ty.clone());
            }
            Event::Smt(Def::DeclareFun(v, arg_tys, result_ty), _, _) => {
                ftcx.to_mut().insert(*v, (arg_tys.clone(), result_ty.clone()));
            }
            Event::Smt(Def::DefineConst(v, exp), _, info) => {
                let e = std::mem::replace(exp, Exp::Bool(false));
                *exp = e.clone().eval();
                match solver.check_sat_with(&Exp::Neq(Box::new(exp.clone()), Box::new(e.clone())), *info) {
                    Sat => panic!("Bad eval {:?} to {:?}", e, exp),
                    Unknown => panic!("Difficult to check eval (!) {:?} to {:?}", e, exp),
                    Unsat => (),
                };
                let ty = exp.infer(&tcx, &ftcx).unwrap();
                solver.add_with_location(Def::DeclareConst(*v, ty.clone()), *info);
                tcx.to_mut().insert(*v, ty);
            }
            Event::Smt(Def::Assert(exp), _, info) => {
                let e = std::mem::replace(exp, Exp::Bool(false));
                *exp = e.clone().eval();
                match solver.check_sat_with(&Exp::Neq(Box::new(exp.clone()), Box::new(e.clone())), *info) {
                    Sat => panic!("Bad eval {:?} to {:?}", e, exp),
                    Unknown => panic!("Difficult to check eval (!) {:?} to {:?}", e, exp),
                    Unsat => (),
                }
            }
            _ => (),
        }
    }
}

pub fn eval_carefully<B: BV, E: BorrowMut<Event<B>>>(events: &mut Vec<E>) {
    let tcx: HashMap<Sym, Ty> = HashMap::new();
    let ftcx: HashMap<Sym, (Vec<Ty>, Ty)> = HashMap::new();
    eval_carefully_part(events, &mut Cow::Owned(tcx), &mut Cow::Owned(ftcx))
}

fn eval_carefully_descend<B: BV>(
    tcx: &mut Cow<HashMap<Sym, Ty>>,
    ftcx: &mut Cow<HashMap<Sym, (Vec<Ty>, Ty)>>,
    event_tree: &mut EventTree<B>,
) {
    eval_carefully_part(&mut event_tree.prefix, tcx, ftcx);
    for fork in &mut event_tree.forks {
        eval_carefully_descend(&mut Cow::Borrowed(tcx), &mut Cow::Borrowed(ftcx), fork);
    }
}

pub fn eval_carefully_tree<B: BV>(event_tree: &mut EventTree<B>) {
    let tcx: HashMap<Sym, Ty> = HashMap::new();
    let ftcx: HashMap<Sym, (Vec<Ty>, Ty)> = HashMap::new();
    eval_carefully_descend(&mut Cow::Owned(tcx), &mut Cow::Owned(ftcx), event_tree);
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
            Event::Smt(Def::DefineConst(_, exp), _, _) | Event::Smt(Def::Assert(exp), _, _) => {
                exp.modify_top_down(&mut Exp::commute_extract)
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
    pub prefix: Vec<Event<B>>,
    pub forks: Vec<EventTree<B>>,
}

/// When used with a stable sort, will push declare-const events
/// downwards as far as possible within a sequence of events.
fn declare_const_down_ordering<B: BV>(ev1: &Event<B>, ev2: &Event<B>) -> Ordering {
    let uses = calculate_uses(std::slice::from_ref(ev2));

    if let Event::Smt(Def::DeclareConst(v, _), _, _) = ev1 {
        if uses.contains_key(v) {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    } else {
        Ordering::Equal
    }
}

/// When used with a stable sort, will push read-mem and read-reg
/// events upwards as far as possible within a sequence of events.
fn read_up_ordering<B: BV>(ev1: &Event<B>, ev2: &Event<B>) -> Ordering {
    if (ev2.is_read_reg() || ev2.is_memory_read()) && ev1.is_smt() {
        let uses = calculate_uses(std::slice::from_ref(ev2));
        if let Some(v) = ev1.defines() {
            if uses.contains_key(&v) {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        } else {
            Ordering::Greater
        }
    } else {
        Ordering::Equal
    }
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

    pub fn make_executable(&mut self) {
        self.map(&|events| {
            events.sort_by(declare_const_down_ordering);
            events.sort_by(read_up_ordering)
        })
    }

    pub fn sort(&mut self) {
        self.forks.sort_by_key(|fork| fork.fork_id);
        for fork in &mut self.forks {
            fork.sort();
        }
    }

    fn renumber_rec(&mut self, renaming: &mut HashMap<u32, u32>, next: &mut u32) {
        for event in self.prefix.iter_mut() {
            renumber_event(event, &mut |id| {
                *renaming.entry(id).or_insert_with(|| {
                    *next += 1;
                    *next - 1
                })
            });
        }
        for fork in self.forks.iter_mut() {
            fork.renumber_rec(&mut renaming.clone(), next);
        }
    }

    pub fn renumber(&mut self) {
        self.renumber_rec(&mut HashMap::new(), &mut 0);
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
    /// Extra indentation level
    pub indent: usize,
    /// Don't print last closing paren
    pub prefix: bool,
    /// Hide uninteresting parts of the trace
    pub hide_uninteresting: bool,
    /// Append SAIL source location comments
    pub locations: bool,
}

impl WriteOpts {
    pub fn smtlib() -> Self {
        WriteOpts {
            variable_prefix: "v".to_string(),
            enum_prefix: "e".to_string(),
            types: true,
            just_smt: true,
            define_enum: false,
            indent: 0,
            prefix: false,
            hide_uninteresting: false,
            locations: false,
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
            indent: 0,
            prefix: false,
            hide_uninteresting: false,
            locations: true,
        }
    }
}

#[allow(clippy::bool_to_int_with_if)]
pub fn write_bits_prefix(buf: &mut dyn Write, prefix: &str, upper_case: bool, bits: &[bool]) -> std::io::Result<()> {
    write!(buf, "{}", prefix)?;
    if bits.len() % 4 == 0 {
        write!(buf, "x")?;
        for i in (0..(bits.len() / 4)).rev() {
            let j = i * 4;
            let hex = (if bits[j] { 0b0001 } else { 0 })
                | (if bits[j + 1] { 0b0010 } else { 0 })
                | (if bits[j + 2] { 0b0100 } else { 0 })
                | (if bits[j + 3] { 0b1000 } else { 0 });
            if upper_case {
                write!(buf, "{:X}", hex)?
            } else {
                write!(buf, "{:x}", hex)?
            }
        }
    } else {
        write!(buf, "b")?;
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

pub fn write_bits(buf: &mut dyn Write, bits: &[bool]) -> std::io::Result<()> {
    write_bits_prefix(buf, "#", false, bits)
}

fn write_ty(buf: &mut dyn Write, ty: &Ty, symtab: &Symtab) -> std::io::Result<()> {
    use Ty::*;
    match ty {
        Bool => write!(buf, "Bool"),
        BitVec(sz) => write!(buf, "(_ BitVec {})", sz),
        Enum(e) => {
            let name = zencode::decode(symtab.to_str(e.to_name()));
            write!(buf, "|{}|", name)
        }
        Array(dom, codom) => {
            write!(buf, "(Array ")?;
            write_ty(buf, dom, symtab)?;
            write!(buf, " ")?;
            write_ty(buf, codom, symtab)?;
            write!(buf, ")")
        }
        Float(ebits, sbits) => write!(buf, "(_ FloatingPoint {} {})", ebits, sbits),
        RoundingMode => write!(buf, "RoundingMode"),
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

fn write_exp<B: BV, V: WriteVar>(
    buf: &mut dyn Write,
    exp: &Exp<V>,
    shared_state: &SharedState<B>,
    opts: &WriteOpts,
) -> std::io::Result<()> {
    use Exp::*;
    match exp {
        Var(v) => v.write_var(buf, opts),
        Bits(bv) => write_bits(buf, bv),
        Bits64(bv) => write_bits64(buf, bv.lower_u64(), bv.len()),
        Enum(e) => {
            let members = shared_state.type_info.enums.get(&e.enum_id.to_name()).ok_or_else(|| {
                Error::new(ErrorKind::Other, format!("Failed to get enumeration '{}'", e.enum_id.to_name()))
            })?;
            let name = zencode::decode(shared_state.symtab.to_str(members[e.member]));
            write!(buf, "|{}|", name)
        }
        Bool(b) => write!(buf, "{}", b),
        Eq(lhs, rhs) => write_binop(buf, "=", lhs, rhs, shared_state, opts),
        Neq(lhs, rhs) => {
            write!(buf, "(not ")?;
            write_binop(buf, "=", lhs, rhs, shared_state, opts)?;
            write!(buf, ")")
        }
        And(lhs, rhs) => write_binop(buf, "and", lhs, rhs, shared_state, opts),
        Or(lhs, rhs) => write_binop(buf, "or", lhs, rhs, shared_state, opts),
        Not(exp) => write_unop(buf, "not", exp, shared_state, opts),
        Bvnot(exp) => write_unop(buf, "bvnot", exp, shared_state, opts),
        Bvand(lhs, rhs) => write_binop(buf, "bvand", lhs, rhs, shared_state, opts),
        Bvor(lhs, rhs) => write_binop(buf, "bvor", lhs, rhs, shared_state, opts),
        Bvxor(lhs, rhs) => write_binop(buf, "bvxor", lhs, rhs, shared_state, opts),
        Bvnand(lhs, rhs) => write_binop(buf, "bvnand", lhs, rhs, shared_state, opts),
        Bvnor(lhs, rhs) => write_binop(buf, "bvnor", lhs, rhs, shared_state, opts),
        Bvxnor(lhs, rhs) => write_binop(buf, "bvxnor", lhs, rhs, shared_state, opts),
        Bvneg(exp) => write_unop(buf, "bvneg", exp, shared_state, opts),
        Bvadd(lhs, rhs) => write_binop(buf, "bvadd", lhs, rhs, shared_state, opts),
        Bvsub(lhs, rhs) => write_binop(buf, "bvsub", lhs, rhs, shared_state, opts),
        Bvmul(lhs, rhs) => write_binop(buf, "bvmul", lhs, rhs, shared_state, opts),
        Bvudiv(lhs, rhs) => write_binop(buf, "bvudiv", lhs, rhs, shared_state, opts),
        Bvsdiv(lhs, rhs) => write_binop(buf, "bvsdiv", lhs, rhs, shared_state, opts),
        Bvurem(lhs, rhs) => write_binop(buf, "bvurem", lhs, rhs, shared_state, opts),
        Bvsrem(lhs, rhs) => write_binop(buf, "bvsrem", lhs, rhs, shared_state, opts),
        Bvsmod(lhs, rhs) => write_binop(buf, "bvsmod", lhs, rhs, shared_state, opts),
        Bvult(lhs, rhs) => write_binop(buf, "bvult", lhs, rhs, shared_state, opts),
        Bvslt(lhs, rhs) => write_binop(buf, "bvslt", lhs, rhs, shared_state, opts),
        Bvule(lhs, rhs) => write_binop(buf, "bvule", lhs, rhs, shared_state, opts),
        Bvsle(lhs, rhs) => write_binop(buf, "bvsle", lhs, rhs, shared_state, opts),
        Bvuge(lhs, rhs) => write_binop(buf, "bvuge", lhs, rhs, shared_state, opts),
        Bvsge(lhs, rhs) => write_binop(buf, "bvsge", lhs, rhs, shared_state, opts),
        Bvugt(lhs, rhs) => write_binop(buf, "bvugt", lhs, rhs, shared_state, opts),
        Bvsgt(lhs, rhs) => write_binop(buf, "bvsgt", lhs, rhs, shared_state, opts),
        Extract(i, j, exp) => {
            write!(buf, "((_ extract {} {}) ", i, j)?;
            write_exp(buf, exp, shared_state, opts)?;
            write!(buf, ")")
        }
        ZeroExtend(n, exp) => {
            write!(buf, "((_ zero_extend {}) ", n)?;
            write_exp(buf, exp, shared_state, opts)?;
            write!(buf, ")")
        }
        SignExtend(n, exp) => {
            write!(buf, "((_ sign_extend {}) ", n)?;
            write_exp(buf, exp, shared_state, opts)?;
            write!(buf, ")")
        }
        Bvshl(lhs, rhs) => write_binop(buf, "bvshl", lhs, rhs, shared_state, opts),
        Bvlshr(lhs, rhs) => write_binop(buf, "bvlshr", lhs, rhs, shared_state, opts),
        Bvashr(lhs, rhs) => write_binop(buf, "bvashr", lhs, rhs, shared_state, opts),
        Concat(lhs, rhs) => write_binop(buf, "concat", lhs, rhs, shared_state, opts),
        Ite(cond, then_exp, else_exp) => {
            write!(buf, "(ite ")?;
            write_exp(buf, cond, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, then_exp, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, else_exp, shared_state, opts)?;
            write!(buf, ")")
        }
        App(f, args) => {
            write!(buf, "({}{}", opts.variable_prefix, f)?;
            for arg in args {
                write!(buf, " ")?;
                write_exp(buf, arg, shared_state, opts)?;
            }
            write!(buf, ")")
        }
        Select(array, index) => write_binop(buf, "select", array, index, shared_state, opts),
        Store(array, index, val) => {
            write!(buf, "(store ")?;
            write_exp(buf, array, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, index, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, val, shared_state, opts)?;
            write!(buf, ")")
        }
        Distinct(exps) => {
            write!(buf, "(distinct")?;
            for exp in exps {
                write!(buf, " ")?;
                write_exp(buf, exp, shared_state, opts)?;
            }
            write!(buf, ")")
        }
        FPConstant(c, ebits, sbits) => {
            use smtlib::FPConstant::*;
            write!(buf, "(_ ")?;
            match c {
                NaN => write!(buf, "NaN")?,
                Inf { negative: false } => write!(buf, "+oo")?,
                Inf { negative: true } => write!(buf, "-oo")?,
                Zero { negative: false } => write!(buf, "+zero")?,
                Zero { negative: true } => write!(buf, "-zero")?,
            }
            write!(buf, " {} {})", ebits, sbits)
        }
        FPRoundingMode(rm) => {
            use smtlib::FPRoundingMode::*;
            match rm {
                RoundNearestTiesToEven => write!(buf, "roundNearestTiesToEven"),
                RoundNearestTiesToAway => write!(buf, "roundNearestTiesToAway"),
                RoundTowardPositive => write!(buf, "roundTowardPositive"),
                RoundTowardNegative => write!(buf, "roundTowardNegative"),
                RoundTowardZero => write!(buf, "roundTowardZero"),
            }
        }
        FPUnary(op, exp) => {
            use smtlib::FPUnary::*;
            write!(buf, "(")?;
            match op {
                Abs => write!(buf, "fp.abs ")?,
                Neg => write!(buf, "fp.neg ")?,
                IsNormal => write!(buf, "fp.isNormal ")?,
                IsSubnormal => write!(buf, "fp.isSubnormal ")?,
                IsZero => write!(buf, "fp.isZero ")?,
                IsInfinite => write!(buf, "fp.isInfinite ")?,
                IsNaN => write!(buf, "fp.isNaN ")?,
                IsNegative => write!(buf, "fp.isNegative ")?,
                IsPositive => write!(buf, "fp.isPositive ")?,
                FromIEEE(ebits, sbits) => write!(buf, "(_ to_fp {} {}) ", ebits, sbits)?,
            }
            write_exp(buf, exp, shared_state, opts)?;
            write!(buf, ")")
        }
        FPRoundingUnary(op, rm, exp) => {
            use smtlib::FPRoundingUnary::*;
            write!(buf, "(")?;
            match op {
                Sqrt => write!(buf, "fp.sqrt ")?,
                RoundToIntegral => write!(buf, "fp.roundToIntegral ")?,
                Convert(ebits, sbits) => write!(buf, "(_ to_fp {} {}) ", ebits, sbits)?,
                FromSigned(ebits, sbits) => write!(buf, "(_ to_fp {} {}) ", ebits, sbits)?,
                FromUnsigned(ebits, sbits) => write!(buf, "(_ to_fp_unsigned {} {}) ", ebits, sbits)?,
                ToSigned(sz) => write!(buf, "(_ fp.to_sbv {}) ", sz)?,
                ToUnsigned(sz) => write!(buf, "(_ fp.to_ubv {}) ", sz)?,
            }
            write_exp(buf, rm, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, exp, shared_state, opts)?;
            write!(buf, ")")
        }
        FPBinary(op, lhs, rhs) => {
            use smtlib::FPBinary::*;
            write!(buf, "(")?;
            match op {
                Rem => write!(buf, "fp.rem ")?,
                Min => write!(buf, "fp.min ")?,
                Max => write!(buf, "fp.max ")?,
                Leq => write!(buf, "fp.leq ")?,
                Lt => write!(buf, "fp.lt ")?,
                Geq => write!(buf, "fp.geq ")?,
                Gt => write!(buf, "fp.gt ")?,
                Eq => write!(buf, "fp.eq ")?,
            }
            write_exp(buf, lhs, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, rhs, shared_state, opts)?;
            write!(buf, ")")
        }
        FPRoundingBinary(op, rm, lhs, rhs) => {
            use smtlib::FPRoundingBinary::*;
            write!(buf, "(")?;
            match op {
                Add => write!(buf, "fp.add ")?,
                Sub => write!(buf, "fp.sub ")?,
                Mul => write!(buf, "fp.mul ")?,
                Div => write!(buf, "fp.div ")?,
            }
            write_exp(buf, rm, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, lhs, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, rhs, shared_state, opts)?;
            write!(buf, ")")
        }
        FPfma(rm, x, y, z) => {
            write!(buf, "(fp.fma ")?;
            write_exp(buf, rm, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, x, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, y, shared_state, opts)?;
            write!(buf, " ")?;
            write_exp(buf, z, shared_state, opts)?;
            write!(buf, ")")
        }
    }
}

fn write_unop<B: BV, V: WriteVar>(
    buf: &mut dyn Write,
    op: &str,
    exp: &Exp<V>,
    shared_state: &SharedState<B>,
    opts: &WriteOpts,
) -> std::io::Result<()> {
    write!(buf, "({} ", op)?;
    write_exp(buf, exp, shared_state, opts)?;
    write!(buf, ")")
}

fn write_binop<B: BV, V: WriteVar>(
    buf: &mut dyn Write,
    op: &str,
    lhs: &Exp<V>,
    rhs: &Exp<V>,
    shared_state: &SharedState<B>,
    opts: &WriteOpts,
) -> std::io::Result<()> {
    write!(buf, "({} ", op)?;
    write_exp(buf, lhs, shared_state, opts)?;
    write!(buf, " ")?;
    write_exp(buf, rhs, shared_state, opts)?;
    write!(buf, ")")
}

pub fn write_events_in_context<B: BV>(
    buf: &mut dyn Write,
    events: &[Event<B>],
    shared_state: &SharedState<B>,
    opts: &WriteOpts,
    tcx: &mut Cow<HashMap<Sym, Ty>>,
    ftcx: &mut Cow<HashMap<Sym, (Vec<Ty>, Ty)>>,
) -> std::io::Result<()> {
    let symtab = &shared_state.symtab;
    let indent = " ".repeat(opts.indent);
    let mut require_newline = false;

    if !opts.just_smt {
        write!(buf, "{}(trace", indent).unwrap();
    }
    for event in events.iter().filter(|ev| !opts.just_smt || ev.is_smt()) {
        require_newline = false;
        (match event {
            Fork(n, _, _, loc) => {
                write!(buf, "\n{}  (branch {} \"{}\")", indent, n, loc.location_string(symtab.files()))
            }

            Function { name, call } => {
                let name = zencode::decode(symtab.to_str(*name));
                if *call {
                    write!(buf, "\n{}  (call |{}|)", indent, name)
                } else {
                    write!(buf, "\n{}  (return |{}|)", indent, name)
                }
            }

            Abstract { name, primitive, args, return_value } => {
                let name = zencode::decode(symtab.to_str(*name));
                if *primitive {
                    write!(buf, "\n{}  (abstract-primop |{}| ", indent, name)?;
                } else {
                    write!(buf, "\n{}  (abstract-call |{}| ", indent, name)?;
                }
                return_value.write(buf, shared_state)?;
                write!(buf, " ")?;
                if let Some((last, elems)) = args.split_last() {
                    for elem in elems {
                        elem.write(buf, shared_state)?;
                        write!(buf, " ")?
                    }
                    last.write(buf, shared_state)?;
                } else {
                    write!(buf, "nil")?
                }
                write!(buf, ")")
            }

            AssumeFun { name, args, return_value } => {
                let name = zencode::decode(symtab.to_str(*name));
                write!(buf, "\n{}  (function-assumption |{}| ", indent, name)?;
                return_value.write(buf, shared_state)?;
                write!(buf, " ")?;
                if let Some((last, elems)) = args.split_last() {
                    for elem in elems {
                        elem.write(buf, shared_state)?;
                        write!(buf, " ")?
                    }
                    last.write(buf, shared_state)?;
                } else {
                    write!(buf, "nil")?
                }
                write!(buf, ")")
            }

            UseFunAssumption { name, args, return_value } => {
                let name = zencode::decode(symtab.to_str(*name));
                write!(buf, "\n{}  (use-function-assumption |{}| ", indent, name)?;
                return_value.write(buf, shared_state)?;
                write!(buf, " ")?;
                if let Some((last, elems)) = args.split_last() {
                    for elem in elems {
                        elem.write(buf, shared_state)?;
                        write!(buf, " ")?
                    }
                    last.write(buf, shared_state)?;
                } else {
                    write!(buf, "nil")?
                }
                write!(buf, ")")
            }

            Smt(def, attrs, loc) if !(opts.hide_uninteresting && attrs.is_uninteresting()) => {
                if opts.just_smt {
                    write!(buf, "\n{}", indent)?
                } else {
                    write!(buf, "\n{}  ", indent)?;
                }
                match def {
                    Def::DeclareConst(v, ty) => {
                        tcx.to_mut().insert(*v, ty.clone());
                        write!(buf, "(declare-const {}{} ", opts.variable_prefix, v)?;
                        write_ty(buf, ty, symtab)?;
                        require_newline = true;
                        write!(buf, ")")?
                    }
                    Def::DeclareFun(v, arg_tys, result_ty) => {
                        ftcx.to_mut().insert(*v, (arg_tys.clone(), result_ty.clone()));
                        write!(buf, "(declare_fun {}{} (", opts.variable_prefix, v)?;
                        for ty in arg_tys {
                            write_ty(buf, ty, symtab)?;
                            write!(buf, " ")?
                        }
                        write!(buf, ") ")?;
                        write_ty(buf, result_ty, symtab)?;
                        write!(buf, ")")?
                    }
                    Def::DefineConst(v, exp) => {
                        if opts.types {
                            let ty = exp.infer(tcx, ftcx).expect("SMT expression was badly-typed");
                            tcx.to_mut().insert(*v, ty.clone());
                            write!(buf, "(define-const v{} ", v)?;
                            write_ty(buf, &ty, symtab)?;
                            write!(buf, " ")?;
                            write_exp(buf, exp, shared_state, opts)?;
                            write!(buf, ")")?
                        } else {
                            write!(buf, "(define-const v{} ", v)?;
                            write_exp(buf, exp, shared_state, opts)?;
                            write!(buf, ")")?;
                        }
                    }
                    Def::DefineEnum(name, size) => {
                        if !opts.just_smt {
                            let members = shared_state.type_info.enums.get(name).ok_or_else(|| {
                                Error::new(ErrorKind::Other, format!("Failed to get enumeration '{}'", name))
                            })?;
                            let members = members
                                .iter()
                                .map(|constr| zencode::decode(shared_state.symtab.to_str(*constr)))
                                .fold(None, |acc, elem| {
                                    if let Some(prefix) = acc {
                                        Some(format!("{} |{}|", prefix, elem))
                                    } else {
                                        Some(format!("|{}|", elem))
                                    }
                                })
                                .map_or("nil".to_string(), |acc| format!("({})", acc));
                            let name = zencode::decode(symtab.to_str(*name));
                            write!(buf, "(define-enum |{}| {} {})", name, size, members)?;
                        }
                    }
                    Def::Assert(exp) => {
                        write!(buf, "(assert ")?;
                        write_exp(buf, exp, shared_state, opts)?;
                        write!(buf, ")")?;
                    }
                }
                if opts.locations {
                    write!(buf, " ; {}", loc.location_string(symtab.files()))?;
                }
                Ok(())
            }

            Smt(..) => Ok(()),

            ReadMem { value, read_kind, address, bytes, tag_value, opts: _, region: _ } => {
                write!(buf, "\n{}  (read-mem ", indent)?;
                value.write(buf, shared_state)?;
                write!(buf, " ")?;
                read_kind.write(buf, shared_state)?;
                write!(buf, " ")?;
                address.write(buf, shared_state)?;
                write!(buf, " {}", bytes)?;
                match tag_value {
                    None => (),
                    Some(v) => {
                        write!(buf, " ")?;
                        v.write(buf, shared_state)?
                    }
                }
                write!(buf, ")")
            }

            WriteMem { value, write_kind, address, data, bytes, tag_value, opts: _, region: _ } => {
                write!(
                    buf,
                    "\n{}  (write-mem v{} {} {} {} {}",
                    indent,
                    value,
                    write_kind.to_string(shared_state),
                    address.to_string(shared_state),
                    data.to_string(shared_state),
                    bytes
                )?;
                match tag_value {
                    None => (),
                    Some(v) => {
                        write!(buf, " ")?;
                        v.write(buf, shared_state)?
                    }
                }
                write!(buf, ")")
            }

            AddressAnnounce { address } => {
                write!(buf, "\n{} (address-announce {})", indent, address.to_string(shared_state))
            }

            Branch { address } => write!(buf, "\n{}  (branch-address {})", indent, address.to_string(shared_state)),

            WriteReg(n, acc, v) => {
                write!(
                    buf,
                    "\n{}  (write-reg |{}| {} ",
                    indent,
                    zencode::decode(symtab.to_str(*n)),
                    accessor_to_string(acc, symtab)
                )?;
                v.write(buf, shared_state)?;
                write!(buf, ")")
            }

            ReadReg(n, acc, v) => {
                if *n == HAVE_EXCEPTION {
                    Ok(())
                } else {
                    write!(
                        buf,
                        "\n{}  (read-reg |{}| {} ",
                        indent,
                        zencode::decode(symtab.to_str(*n)),
                        accessor_to_string(acc, symtab)
                    )?;
                    v.write(buf, shared_state)?;
                    write!(buf, ")")
                }
            }

            MarkReg { regs, mark } => {
                for reg in regs {
                    write!(buf, "\n{}  (mark-reg |{}| \"{}\")", indent, zencode::decode(symtab.to_str(*reg)), mark)?
                }
                Ok(())
            }

            Cycle => write!(buf, "\n{}  (cycle)", indent),

            Instr(value) => write!(buf, "\n{}  (instr {})", indent, value.to_string(shared_state)),

            Assume(constraint) => {
                write!(buf, "\n{}  (assume ", indent)?;
                let assume_opts = WriteOpts { variable_prefix: "".to_string(), ..opts.clone() };
                write_exp(buf, constraint, shared_state, &assume_opts)?;
                write!(buf, ")")
            }

            AssumeReg(n, acc, v) => {
                write!(
                    buf,
                    "\n{}  (assume-reg |{}| {} {})",
                    indent,
                    zencode::decode(symtab.to_str(*n)),
                    accessor_to_string(acc, symtab),
                    v.to_string(shared_state)
                )
            }
        })?
    }
    if require_newline {
        write!(buf, "\n{}", indent)?;
    }
    if !(opts.just_smt || opts.prefix) {
        writeln!(buf, ")")?;
    }
    Ok(())
}

pub fn write_events_with_opts<B: BV>(
    buf: &mut dyn Write,
    events: &[Event<B>],
    shared_state: &SharedState<B>,
    opts: &WriteOpts,
) -> std::io::Result<()> {
    let tcx: HashMap<Sym, Ty> = HashMap::new();
    let ftcx: HashMap<Sym, (Vec<Ty>, Ty)> = HashMap::new();

    write_events_in_context(buf, events, shared_state, opts, &mut Cow::Owned(tcx), &mut Cow::Owned(ftcx))
}

pub fn write_events<B: BV>(buf: &mut dyn Write, events: &[Event<B>], shared_state: &SharedState<B>) {
    write_events_with_opts(buf, events, shared_state, &WriteOpts::default()).unwrap()
}

fn write_event_tree_with_opts<B: BV>(
    buf: &mut dyn Write,
    evtree: &EventTree<B>,
    shared_state: &SharedState<B>,
    opts: &mut WriteOpts,
    tcx: &mut Cow<HashMap<Sym, Ty>>,
    ftcx: &mut Cow<HashMap<Sym, (Vec<Ty>, Ty)>>,
) -> std::io::Result<()> {
    write_events_in_context(buf, &evtree.prefix, shared_state, opts, tcx, ftcx)?;

    if !evtree.forks.is_empty() {
        write!(
            buf,
            "\n{}  (cases \"{}\"",
            " ".repeat(opts.indent),
            evtree.source_loc.location_string(shared_state.symtab.files())
        )?;
        opts.indent += 4;
        for fork in &evtree.forks {
            writeln!(buf)?;
            write_event_tree_with_opts(
                buf,
                fork,
                shared_state,
                opts,
                &mut Cow::Borrowed(tcx),
                &mut Cow::Borrowed(ftcx),
            )?
        }
        opts.indent -= 4;
        write!(buf, "))")?;
    } else {
        write!(buf, ")")?;
    }

    Ok(())
}

pub fn write_event_tree<B: BV>(
    buf: &mut dyn Write,
    evtree: &EventTree<B>,
    shared_state: &SharedState<B>,
    opts: &WriteOpts,
) {
    let mut opts = WriteOpts { prefix: true, ..opts.clone() };
    let tcx: HashMap<Sym, Ty> = HashMap::new();
    let ftcx: HashMap<Sym, (Vec<Ty>, Ty)> = HashMap::new();

    write_event_tree_with_opts(buf, evtree, shared_state, &mut opts, &mut Cow::Owned(tcx), &mut Cow::Owned(ftcx))
        .unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::source_loc::SourceLoc;

    #[test]
    fn break_forks_simple() {
        let events: Vec<Event<B64>> = vec![
            Event::Cycle,
            Event::Fork(0, Sym::from_u32(0), 0, SourceLoc::unknown()),
            Event::MarkReg { regs: vec![], mark: "foo".to_string() },
        ];

        let broken = break_into_forks(&events);

        assert_eq!(broken.len(), 2);
        assert_eq!(broken[0].0, None);
        assert!(matches!(broken[0].2[0], Event::Cycle));
        assert_eq!(broken[0].2.len(), 1);
        assert_eq!(broken[1].0, Some(0));
        assert!(matches!(broken[1].2[0], Event::MarkReg { .. }));
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
        let events1: Vec<Event<B64>> = vec![
            Event::Cycle,
            Event::Fork(0, Sym::from_u32(0), 0, SourceLoc::unknown()),
            Event::MarkReg { regs: vec![], mark: "foo".to_string() },
        ];
        let events2: Vec<Event<B64>> =
            vec![Event::Cycle, Event::Fork(0, Sym::from_u32(0), 0, SourceLoc::unknown()), Event::Cycle];

        let mut evtree = EventTree::from_events(&events1);
        evtree.add_events(&events2);
    }

    #[test]
    fn remove_unused_in_one_branch() {
        use crate::smt::DefAttrs;
        let events1: Vec<Event<B64>> = vec![
            Event::Smt(
                Def::DefineConst(Sym::from_u32(1), Exp::Bits64(B64::from_u64(0x123))),
                DefAttrs::default(),
                SourceLoc::unknown(),
            ),
            Event::Fork(0, Sym::from_u32(2), 0, SourceLoc::unknown()),
            Event::Smt(
                Def::DefineConst(Sym::from_u32(3), Exp::Bits64(B64::from_u64(0x456))),
                DefAttrs::default(),
                SourceLoc::unknown(),
            ),
            Event::Cycle,
        ];
        let events2: Vec<Event<B64>> = vec![
            Event::Smt(
                Def::DefineConst(Sym::from_u32(1), Exp::Bits64(B64::from_u64(0x123))),
                DefAttrs::default(),
                SourceLoc::unknown(),
            ),
            Event::Fork(0, Sym::from_u32(2), 1, SourceLoc::unknown()),
            Event::Smt(
                Def::DefineConst(Sym::from_u32(3), Exp::Bits64(B64::from_u64(0x789))),
                DefAttrs::default(),
                SourceLoc::unknown(),
            ),
            Event::Smt(
                Def::DefineConst(
                    Sym::from_u32(4),
                    Exp::Bvadd(Box::new(Exp::Var(Sym::from_u32(1))), Box::new(Exp::Var(Sym::from_u32(3)))),
                ),
                DefAttrs::default(),
                SourceLoc::unknown(),
            ),
            Event::WriteReg(Name::from_u32(0), vec![], Val::Symbolic(Sym::from_u32(4))),
        ];
        let mut evtree = EventTree::from_events(&events1);
        evtree.add_events(&events2);
        evtree.renumber();

        remove_unused_tree(&mut evtree);

        assert_eq!(evtree.prefix.len(), 1);
        assert_eq!(evtree.forks.len(), 2);
        assert_eq!(evtree.forks[0].prefix.len(), 1);
        assert_eq!(evtree.forks[1].prefix.len(), 3);
    }

    #[test]
    fn remove_repeated_regs() {
        let event = Event::ReadReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x123)));
        let mut events: Vec<Event<B64>> = vec![event.clone(), Event::Cycle, event];
        remove_repeated_register_reads(&mut events);
        assert_eq!(events.len(), 2);
        assert!(matches!(events[0], Event::Cycle));

        // We shouldn't see consecutive reads with different values,
        // but we want to keep them if we do.
        let event_1 = Event::ReadReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x123)));
        let event_2 = Event::ReadReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x456)));
        let mut events: Vec<Event<B64>> = vec![event_1, Event::Cycle, event_2];
        remove_repeated_register_reads(&mut events);
        assert_eq!(events.len(), 3);
        assert!(matches!(events[1], Event::Cycle));

        let event_r = Event::ReadReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x123)));
        let event_w = Event::WriteReg(Name::from_u32(0), vec![], Val::Bits(B64::from_u64(0x123)));
        let mut events: Vec<Event<B64>> = vec![event_r.clone(), Event::Cycle, event_w, event_r];
        remove_repeated_register_reads(&mut events);
        assert_eq!(events.len(), 4);
        assert!(matches!(events[1], Event::Cycle));

        let field_1 = Accessor::Field(Name::from_u32(1));
        let field_2 = Accessor::Field(Name::from_u32(2));
        let val = Val::Bits(B64::from_u64(0x123));
        let val_2 = Val::Struct([(Name::from_u32(2), val)].iter().cloned().collect());
        let val_1 = Val::Struct([(Name::from_u32(1), val_2.clone())].iter().cloned().collect());
        let event_r = Event::ReadReg(Name::from_u32(0), vec![field_1.clone(), field_2], val_1);
        let event_w = Event::WriteReg(Name::from_u32(0), vec![field_1], val_2);
        let mut events: Vec<Event<B64>> = vec![event_r.clone(), Event::Cycle, event_w, event_r];
        remove_repeated_register_reads(&mut events);
        assert_eq!(events.len(), 4);
        assert!(matches!(events[1], Event::Cycle));
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

        // The assumption is shadowed by the write, so we remove it
        let event_w = Event::WriteReg(Name::from_u32(0), vec![], val.clone());
        let mut events: Vec<Event<B64>> = vec![event_r.clone(), event_w.clone(), event_a.clone()];
        remove_unused_register_assumptions(&mut events);
        assert_eq!(events.len(), 2);

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
