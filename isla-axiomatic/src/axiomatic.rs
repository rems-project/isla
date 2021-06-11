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

//! This module implements utilities for working with axiomatic memory
//! models.

use std::collections::HashMap;
use std::error::Error;
use std::fmt;

use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::ir::{Name, SharedState, Val};
use isla_lib::smt::{EvPath, Event};

use crate::page_table::VirtualAddress;

pub type ThreadId = usize;

pub type TranslationId = usize;

/// An iterator over candidate executions
pub struct Candidates<'ev, B> {
    index: Vec<usize>,
    max_index: Vec<usize>,
    threads: &'ev [Vec<EvPath<B>>],
    out_of_bounds: bool,
}

impl<'ev, B: BV> Candidates<'ev, B> {
    /// Create a candidate exeuction iterator from a slice containing
    /// vectors for each path through a thread.
    pub fn new(threads: &'ev [Vec<EvPath<B>>]) -> Self {
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

impl<'ev, B: BV> Iterator for Candidates<'ev, B> {
    type Item = Vec<&'ev [Event<B>]>;

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
    pub fn from_slice(slice: &'a [A]) -> Self {
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

/// An AxEvent (axiomatic event) is an event combined with metadata
/// about where and when it was executed in a candidate
/// execution. This can be combined with the footprint analysis to
/// determine various dependency orders on events.
#[derive(Debug)]
pub struct AxEvent<'a, B> {
    /// The opcode for the instruction that contained the underlying event
    pub opcode: B,
    /// The place of the event in po-order for it's thread
    pub po: usize,
    /// If a single instruction contains multiple events, this will
    /// order them
    pub intra_instruction_order: usize,
    /// The thread id for the event
    pub thread_id: ThreadId,
    /// A generated unique name for the event
    pub name: String,
    /// The underlying event(s) in the SMT trace
    pub base: Vec<&'a Event<B>>,
    /// Is the event an instruction fetch (i.e. base is ReadMem with an ifetch read_kind)
    pub is_ifetch: bool,
    /// Is the event associated with an address translation function?
    pub translate: Option<TranslationId>,
}

impl<'a, B: BV> AxEvent<'a, B> {
    pub fn base(&self) -> Option<&'a Event<B>> {
        if self.base.len() == 1 {
            Some(self.base[0])
        } else {
            None
        }
    }

    pub fn address(&self) -> Option<&'a Val<B>> {
        match self.base()? {
            Event::ReadMem { address, .. } | Event::WriteMem { address, .. } | Event::CacheOp { address, .. } => {
                Some(address)
            }
            _ => None,
        }
    }

    pub fn read_value(&self) -> Option<(&'a Val<B>, u32)> {
        match self.base()? {
            Event::ReadMem { value, bytes, .. } => Some((value, *bytes)),
            _ => None,
        }
    }

    pub fn write_data(&self) -> Option<(&'a Val<B>, u32)> {
        match self.base()? {
            Event::WriteMem { data, bytes, .. } => Some((data, *bytes)),
            _ => None,
        }
    }
}

pub struct Translations<'a, 'ev, B> {
    translations: HashMap<TranslationId, Vec<&'a AxEvent<'ev, B>>>,
}

impl<'a, 'ev, B: BV> Translations<'a, 'ev, B> {
    fn from_events(events: &'a [AxEvent<'ev, B>]) -> Self {
        let mut translations = HashMap::new();

        for ev in events {
            if let Some(trans_id) = ev.translate {
                let translate_events = translations.entry(trans_id).or_insert(Vec::new());
                translate_events.push(ev)
            }
        }

        for same_translation in translations.values_mut() {
            same_translation.sort_by_key(|ev| (ev.po, ev.intra_instruction_order));
        }

        Translations { translations }
    }

    fn va_page(&self, trans_id: TranslationId) -> Option<VirtualAddress> {
        let events = if let Some(events) = self.translations.get(&trans_id) {
            events.as_slice()
        } else {
            return None;
        };

        let table_offset_mask: u64 = 0xFFF;
        let mut indices: [usize; 4] = [0; 4];
        let mut level = 0;

        for ax_event in events {
            for ev in ax_event.base.iter().filter(|ev| ev.has_memory_kind("stage 1") && ev.is_memory_read()) {
                if let Event::ReadMem { address: Val::Bits(bv), .. } = ev {
                    indices[level] = ((bv.lower_u64() & table_offset_mask) >> 3) as usize;
                    level += 1
                } else {
                    return None;
                }
            }
        }

        // As we assume a 4 level (levels 0-3) table with 4k pages, a
        // translation event must have exactly 4 stage 1 reads to
        // define a VA.
        if level != 4 {
            return None;
        }

        // The VA 4k page is determined by the indices used in the translation
        return Some(VirtualAddress::from_indices(indices[0], indices[1], indices[2], indices[3], 0));
    }

    fn ipa_page(&self, trans_id: TranslationId) -> Option<VirtualAddress> {
        let events = if let Some(events) = self.translations.get(&trans_id) {
            events.as_slice()
        } else {
            return None;
        };

        let table_offset_mask: u64 = 0xFFF;
        let mut indices: Vec<usize> = Vec::new();

        for ax_event in events {
            for ev in ax_event.base.iter().filter(|ev| ev.has_memory_kind("stage 2") && ev.is_memory_read()) {
                if let Event::ReadMem { address: Val::Bits(bv), .. } = ev {
                    indices.push(((bv.lower_u64() & table_offset_mask) >> 3) as usize);
                } else {
                    return None;
                }
            }
        }

        let l = indices.len();
        if l < 4 {
            return None;
        }

        // The IPA 4k page is determined by the final s2 indices
        return Some(VirtualAddress::from_indices(indices[l - 4], indices[l - 3], indices[l - 2], indices[l - 1], 0));
    }
}

pub mod relations {
    use std::collections::HashMap;

    use isla_lib::bitvector::BV;
    use isla_lib::smt::Event;

    use super::AxEvent;
    use super::Translations;
    use crate::footprint_analysis::{addr_dep, ctrl_dep, data_dep, rmw_dep, Footprint};

    pub fn is_write<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base().filter(|b| b.is_memory_write()).is_some()
    }

    pub fn is_translate<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.translate.is_some()
    }

    pub fn is_ifetch<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.is_ifetch
    }

    pub fn is_in_s1_table<B: BV>(ev: &AxEvent<B>) -> bool {
        if let Some(Event::ReadMem { kind, .. }) = ev.base() {
            kind == &"stage 1"
        } else {
            false
        }
    }

    pub fn is_in_s2_table<B: BV>(ev: &AxEvent<B>) -> bool {
        if let Some(Event::ReadMem { kind, .. }) = ev.base() {
            kind == &"stage 2"
        } else {
            false
        }
    }

    pub fn is_read<B: BV>(ev: &AxEvent<B>) -> bool {
        !is_translate(ev) && !ev.is_ifetch && ev.base().filter(|b| b.is_memory_read()).is_some()
    }

    pub fn is_barrier<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base().filter(|b| b.is_barrier()).is_some()
    }

    pub fn is_cache_op<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base().filter(|b| b.is_cache_op()).is_some()
    }

    pub fn amo<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        intra_instruction_ordered(ev1, ev2) && rmw_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn univ<B: BV>(_: &AxEvent<B>, _: &AxEvent<B>) -> bool {
        true
    }

    pub fn disjoint<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po != ev2.po || ev1.thread_id != ev2.thread_id
    }

    pub fn po<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po < ev2.po && ev1.thread_id == ev2.thread_id
    }

    pub fn intra_instruction_ordered<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po == ev2.po && ev1.thread_id == ev2.thread_id && ev1.intra_instruction_order < ev2.intra_instruction_order
    }

    pub fn internal<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po != ev2.po && ev1.thread_id == ev2.thread_id
    }

    pub fn external<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po != ev2.po && ev1.thread_id != ev2.thread_id
    }

    pub type DepRel<B> = fn(&AxEvent<B>, &AxEvent<B>, &[Vec<B>], &HashMap<B, Footprint>) -> bool;

    pub fn addr<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        !ev1.is_ifetch && po(ev1, ev2) && addr_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn data<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        po(ev1, ev2) && data_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn ctrl<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        !ev1.is_ifetch && po(ev1, ev2) && ctrl_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn rmw<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        (po(ev1, ev2) || intra_instruction_ordered(ev1, ev2))
            && rmw_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn translation_walk_order<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        intra_instruction_ordered(ev1, ev2) && is_translate(ev1) && is_translate(ev2)
    }

    pub fn same_va_page<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>, translations: &Translations<B>) -> bool {
        if ev1.name == ev2.name || ev1.translate.is_none() || ev2.translate.is_none() {
            return false;
        };

        match (translations.va_page(ev1.translate.unwrap()), translations.va_page(ev2.translate.unwrap())) {
            (Some(va1), Some(va2)) => va1 == va2,
            (_, _) => false,
        }
    }

    pub fn same_ipa_page<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>, translations: &Translations<B>) -> bool {
        if ev1.name == ev2.name || ev1.translate.is_none() || ev2.translate.is_none() {
            return false;
        };

        match (translations.ipa_page(ev1.translate.unwrap()), translations.ipa_page(ev2.translate.unwrap())) {
            (Some(va1), Some(va2)) => va1 == va2,
            (_, _) => false,
        }
    }
}

pub struct ExecutionInfo<'ev, B> {
    /// A vector containing all the events in a candidate execution
    pub events: Vec<AxEvent<'ev, B>>,
    /// A vector of po-ordered instruction opcodes for each thread
    pub thread_opcodes: Vec<Vec<B>>,
    /// The final write for each register in each thread (if written at all)
    pub final_writes: HashMap<(Name, ThreadId), &'ev Val<B>>,
}

/// An iterator over the base events in a candidate execution
pub struct BaseEvents<'a, 'ev, B> {
    ax: usize,
    base: usize,
    execution_info: &'a ExecutionInfo<'ev, B>,
}

impl<'a, 'ev, B> Iterator for BaseEvents<'a, 'ev, B> {
    type Item = (&'a AxEvent<'ev, B>, &'ev Event<B>);

    fn next(&mut self) -> Option<Self::Item> {
        let ax_event = self.execution_info.events.get(self.ax)?;

        if let Some(base_event) = ax_event.base.get(self.base) {
            self.base += 1;
            Some((&ax_event, base_event))
        } else {
            self.ax += 1;
            self.base = 0;
            self.next()
        }
    }
}

#[derive(Debug)]
pub enum CandidateError<B> {
    MultipleInstructionsInCycle { opcode1: B, opcode2: B },
    NoInstructionsInCycle,
}

impl<B: BV> fmt::Display for CandidateError<B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use CandidateError::*;
        match self {
            MultipleInstructionsInCycle { opcode1, opcode2 } => write!(
                f,
                "A single fetch-execute-decode cycle in this candidate execution was associated with multiple instructions: {} and {}",
                opcode1,
                opcode2
            ),
            NoInstructionsInCycle => write!(
                f,
                "A fetch-execute-decode cycle was encountered that had no associated instructions"
            ),
        }
    }
}

impl<B: BV> Error for CandidateError<B> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

// We want a unique identifier for each call in the execution trace,
// so we use a stack with a counter that gets incremented each time
// the stack is pushed
struct CallStack {
    count: usize,
    stack: Vec<(Name, usize)>,
}

impl CallStack {
    fn new() -> Self {
        CallStack { count: 0, stack: Vec::new() }
    }

    fn push(&mut self, f: Name) {
        self.stack.push((f, self.count));
        self.count += 1
    }

    fn pop(&mut self) -> Option<Name> {
        self.stack.pop().map(|(f, _)| f)
    }

    fn contains(&self, f: Name) -> Option<usize> {
        for (g, n) in &self.stack {
            if f == *g {
                return Some(*n);
            }
        }
        None
    }

    fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }
}

struct MergedTranslation<'ev, B> {
    opcode: B,
    po: usize,
    thread_id: usize,
    intra_instruction_order: usize,
    events: Vec<(usize, &'ev Event<B>)>,
}

impl<'ev, B: BV> ExecutionInfo<'ev, B> {
    pub fn base_events<'a>(&'a self) -> BaseEvents<'a, 'ev, B> {
        BaseEvents { ax: 0, base: 0, execution_info: self }
    }

    pub fn translations<'a>(&'a self) -> Translations<'a, 'ev, B> {
        Translations::from_events(&self.events)
    }

    /// This function merges translate events (typically memory reads
    /// to page table entries) with the same translation id into
    /// larger whole translation events each containing a sequence of
    /// base events
    pub fn merge_translations(&mut self) {
        let mut all_translations: HashMap<TranslationId, MergedTranslation<'ev, B>> = HashMap::new();

        // For each instruction (identified by a opcode, po, and
        // thread_id triple), we extract the translate events,
        // grouping them into possibly multiple translations
        // consisting of sequences of consecutive translate events
        self.events.retain(|ev| {
            if let Some(trans_id) = ev.translate {
                let merged = all_translations.entry(trans_id).or_insert_with(|| MergedTranslation {
                    opcode: ev.opcode,
                    po: ev.po,
                    thread_id: ev.thread_id,
                    intra_instruction_order: ev.intra_instruction_order,
                    events: Vec::new(),
                });

                // Each translate event we encounter with a specific
                // translation id should be from the same instruction
                assert_eq!(ev.opcode, merged.opcode);
                assert_eq!(ev.po, merged.po);
                assert_eq!(ev.thread_id, merged.thread_id);

                for base in &ev.base {
                    merged.events.push((ev.intra_instruction_order, base))
                }
                merged.intra_instruction_order =
                    std::cmp::min(merged.intra_instruction_order, ev.intra_instruction_order);

                false
            } else {
                true
            }
        });

        for merged in all_translations.values_mut() {
            merged.events.sort_by_key(|(iio, _)| *iio)
        }

        // Now we create a new axiomatic event for each translation sequence
        for (trans_id, merged) in all_translations {
            self.events.push(AxEvent {
                opcode: merged.opcode,
                po: merged.po,
                intra_instruction_order: merged.intra_instruction_order,
                thread_id: merged.thread_id,
                name: format!("TRANS_{}", trans_id),
                base: merged.events.iter().map(|(_, base)| *base).collect(),
                is_ifetch: false,
                translate: Some(trans_id),
            })
        }
    }

    pub fn from(
        candidate: &'ev [&[Event<B>]],
        shared_state: &SharedState<B>,
        isa_config: &ISAConfig<B>,
    ) -> Result<Self, CandidateError<B>> {
        use CandidateError::*;
        let mut exec = ExecutionInfo {
            events: Vec::new(),
            thread_opcodes: vec![Vec::new(); candidate.len()],
            final_writes: HashMap::new(),
        };

        let rk_ifetch = shared_state.enum_member(isa_config.ifetch_read_kind).expect("Invalid ifetch read kind");

        let mut call_stack = CallStack::new();

        for (tid, thread) in candidate.iter().enumerate() {
            for (po, cycle) in thread.split(|ev| ev.is_cycle()).skip(1).enumerate() {
                let mut cycle_events: Vec<(usize, String, &Event<B>, bool, Option<usize>)> = Vec::new();
                let mut cycle_instr: Option<B> = None;

                for (eid, event) in cycle.iter().enumerate() {
                    let translate = if let Some(translation_function) = isa_config.translation_function {
                        call_stack.contains(translation_function)
                    } else {
                        None
                    };
                    match event {
                        Event::Instr(Val::Bits(bv)) => {
                            if let Some(opcode) = cycle_instr {
                                return Err(MultipleInstructionsInCycle { opcode1: *bv, opcode2: opcode });
                            } else {
                                exec.thread_opcodes[tid].push(*bv);
                                cycle_instr = Some(*bv)
                            }
                        }
                        Event::ReadMem { read_kind: Val::Enum(e), .. } => {
                            if e.member == rk_ifetch {
                                cycle_events.push((tid, format!("R{}_{}_{}", po, eid, tid), event, true, translate))
                            } else {
                                cycle_events.push((tid, format!("R{}_{}_{}", po, eid, tid), event, false, translate))
                            }
                        }
                        Event::ReadMem { .. } => panic!("ReadMem event with non-concrete enum read_kind"),
                        Event::WriteMem { .. } => {
                            cycle_events.push((tid, format!("W{}_{}_{}", po, eid, tid), event, false, None))
                        }
                        Event::Barrier { .. } => {
                            cycle_events.push((tid, format!("F{}_{}_{}", po, eid, tid), event, false, None))
                        }
                        Event::CacheOp { .. } => {
                            cycle_events.push((tid, format!("C{}_{}_{}", po, eid, tid), event, false, None))
                        }
                        Event::WriteReg(reg, _, val) => {
                            exec.final_writes.insert((*reg, tid), val);
                        }
                        Event::Function { name, call } => {
                            if *call {
                                call_stack.push(*name);
                            } else if let Some(stack_name) = call_stack.pop() {
                                assert_eq!(stack_name, *name)
                            } else {
                                panic!("unbalanced call stack when processing trace")
                            }
                        }
                        _ => (),
                    }
                }

                for (iio, (tid, name, ev, is_ifetch, translate)) in cycle_events.drain(..).enumerate() {
                    // Events must be associated with an instruction
                    if let Some(opcode) = cycle_instr {
                        // An event is a translate event if it was
                        // created by the translation function
                        exec.events.push(AxEvent {
                            opcode,
                            po,
                            intra_instruction_order: iio,
                            thread_id: tid,
                            name,
                            base: vec![ev],
                            is_ifetch,
                            translate,
                        })
                    } else if !ev.has_read_kind(rk_ifetch) {
                        // Unless we have a single failing ifetch
                        return Err(NoInstructionsInCycle);
                    }
                }
            }

            assert!(call_stack.is_empty())
        }

        Ok(exec)
    }
}

/// This module defines utilites for parsing and interpreting the
/// models returned by Z3 when invoked on the command line.
pub mod model {
    use std::collections::HashMap;

    use isla_lib::bitvector::BV;
    use isla_lib::ir::Val;

    use super::Pairs;
    use crate::sexp::{DefineFun, InterpretEnv, InterpretError, SexpFn, SexpVal};
    use crate::sexp_lexer::SexpLexer;
    use crate::sexp_parser::SexpParser;

    /// A model, as parsed from the SMT solver output, contains a list
    /// of function declarations (which can have arity 0 for
    /// constants) for each declare-const and declare-fun in the
    /// model. A model can also be parameterised by a set of
    /// events. The two lifetime parameters correspond to the
    /// underlying smtlib model `'s` and the events `'ev`.
    pub struct Model<'s, 'ev, B> {
        env: InterpretEnv<'s, 'ev, B>,
        functions: HashMap<&'s str, SexpFn<'s>>,
    }

    impl<'s, 'ev, B: BV> Model<'s, 'ev, B> {
        /// Parse a model from a string of the form (model (define-fun ...) (define-fun ...) ...)
        pub fn parse(events: &[&'ev str], model: &'s str) -> Option<Self> {
            let mut env = InterpretEnv::new();
            for event in events {
                env.add_event(event)
            }

            let lexer = SexpLexer::new(model);
            match SexpParser::new().parse(lexer) {
                Ok(sexp) => match sexp.dest_fn_or_list("model") {
                    Some(function_sexps) => {
                        let mut functions = HashMap::new();
                        for f in function_sexps {
                            if let Some(DefineFun { name, params, body, .. }) = f.dest_define_fun() {
                                let params = params.iter().map(|(a, _)| *a).collect();
                                functions.insert(name, SexpFn { params, body });
                            } else {
                                return None;
                            }
                        }
                        Some(Model { env, functions })
                    }
                    None => None,
                },
                Err(_) => None,
            }
        }

        /// Interprets a function in the model
        pub fn interpret(&mut self, f: &str, args: &[SexpVal<'ev, B>]) -> Result<SexpVal<'ev, B>, InterpretError> {
            let function = self.functions.get(f).ok_or_else(|| InterpretError::UnknownFunction(f.to_string()))?;

            self.env.add_args(&function.params, args)?;
            let result = function.body.interpret(&mut self.env, &self.functions)?;
            self.env.clear_args(&function.params);

            Ok(result)
        }

        /// Inteprets a relation (an Event * Event -> Bool function)
        /// over a set of events. Note that all events in this set
        /// must have been used to parameterise the model in
        /// Model::parse.
        pub fn interpret_rel(
            &mut self,
            rel: &str,
            events: &[&'ev str],
        ) -> Result<Vec<(&'ev str, &'ev str)>, InterpretError> {
            let mut pairs = Vec::new();

            for (ev1, ev2) in Pairs::from_slice(events) {
                match self.interpret(rel, &[SexpVal::Event(*ev1), SexpVal::Event(ev2)])? {
                    SexpVal::Bool(true) => pairs.push((*ev1, *ev2)),
                    SexpVal::Bool(false) => (),
                    _ => return Err(InterpretError::Type(rel.to_string())),
                }
            }

            Ok(pairs)
        }

        /// Interpret either a bitvector symbol in the model, or just
        /// return the bitvector directory if the val is concrete
        pub fn interpret_bits(&mut self, val: &Val<B>) -> Result<B, InterpretError> {
            match val {
                Val::Symbolic(v) => {
                    let smt_name = format!("v{}", v);
                    let sexp = self.interpret(&smt_name, &[])?;
                    sexp.into_bits().ok_or_else(|| InterpretError::NotFound(smt_name))
                }
                Val::Bits(bv) => Ok(*bv),
                _ => Err(InterpretError::Type("interpret_bv".to_string())),
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        use isla_lib::bitvector::b64::B64;

        #[test]
        fn test_parse() {
            let smtlib = "(model (define-fun v12331 () (_ BitVec 32) #x00000001))";
            Model::<B64>::parse(&[], smtlib).unwrap();
        }

        #[test]
        fn test_interpret_1() {
            let smtlib = "(model (define-fun dmb ((x!0 Event)) Bool false))";
            let ev = "R0";
            let mut model = Model::<B64>::parse(&[ev], smtlib).unwrap();
            let result = model.interpret("dmb", &[SexpVal::Event(ev)]).unwrap();
            assert_eq!(result, SexpVal::Bool(false));
        }

        #[test]
        fn test_interpret_2() {
            let smtlib = "(model (define-fun |0xdmb%| ((x!0 Event)) Bool false))";
            let ev = "R0";
            let mut model = Model::<B64>::parse(&[ev], smtlib).unwrap();
            let result = model.interpret("0xdmb%", &[SexpVal::Event(ev)]).unwrap();
            assert_eq!(result, SexpVal::Bool(false));
        }

        #[test]
        fn test_interpret_3() {
            let smtlib =
                "(model (define-fun |foo| ((x!0 Event)) Bool (let ((a!0 true)) (let ((a!0 false)) (and a!0)))))";
            let ev = "R0";
            let mut model = Model::<B64>::parse(&[ev], smtlib).unwrap();
            let result = model.interpret("foo", &[SexpVal::Event(ev)]).unwrap();
            assert_eq!(result, SexpVal::Bool(false));
        }

        #[test]
        fn test_interpret_4() {
            let smtlib = "(model (define-fun |foo| ((x!0 Event)) Bool (ite false true (not (= x!0 R0)))))";
            let ev = "R0";
            let mut model = Model::<B64>::parse(&[ev], smtlib).unwrap();
            let result = model.interpret("foo", &[SexpVal::Event(ev)]).unwrap();
            assert_eq!(result, SexpVal::Bool(false));
        }

        #[test]
        fn test_interpret_rel() {
            let smtlib = "(model (define-fun obs ((x!0 Event) (x!1 Event)) Bool
                            (or (and (= x!0 W0) (= x!1 R1))
                                (and (= x!0 IW) (= x!1 W0))
                                (and (= x!0 W1) (= x!1 R0))
                                (and (= x!0 IW) (= x!1 W1)))))";
            let evs = ["IW", "W0", "W1", "R0", "R1"];
            let mut model = Model::<B64>::parse(&evs, smtlib).unwrap();
            let result = model.interpret_rel("obs", &evs).unwrap();
            assert!(result.contains(&("W0", "R1")));
            assert!(result.contains(&("IW", "W0")));
            assert!(result.contains(&("W1", "R0")));
            assert!(result.contains(&("IW", "W1")));
            assert!(result.len() == 4);
        }
    }
}
