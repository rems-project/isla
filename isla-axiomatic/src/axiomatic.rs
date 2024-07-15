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

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;

use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::error::IslaError;
use isla_lib::ir::{Name, SharedState, Val};
use isla_lib::memory::Memory;
use isla_lib::smt::{smtlib::Def, smtlib::Ty, EvPath, Event, Sym};
use isla_lib::source_loc::SourceLoc;

use isla_mml::accessor::ModelEvent;
use isla_mml::memory_model;

use crate::graph::GraphOpts;
use crate::litmus::exp::Loc as LitmusLoc;
use crate::litmus::Litmus;
use crate::page_table::VirtualAddress;
use crate::sexp::SexpVal;
use crate::smt_model::Model;

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

/// An AxEvent (axiomatic event) is a set of base events from an Isla
/// trace combined with metadata about where and when it was executed
/// in a candidate execution. This can be combined with the footprint
/// analysis to determine various dependency orders on events.
#[derive(Debug)]
pub struct AxEvent<'ev, B> {
    /// The opcode for the instruction that contained the underlying event
    /// An axiomatic event may have no opcode if it occurred in a cycle that
    /// ended prior to ifetch.
    pub opcode: Option<B>,
    /// The place of the event in the instruction-order (the sequence
    /// of instructions as they appear in the trace) for it's thread
    pub instruction_index: usize,
    /// If a single instruction contains multiple events, this is the
    /// index in that sequence of events
    pub intra_instruction_index: usize,
    /// This event appears in program order
    pub in_program_order: bool,
    /// The thread id for the event
    pub thread_id: ThreadId,
    /// A generated unique name for the event
    pub name: String,
    pub mm_name: memory_model::Name,
    /// The underlying event(s) in the SMT trace
    pub base: Vec<&'ev Event<B>>,
    /// If base contains multiple events, we can generate a SMT type
    /// to index them for some subset of events (such as all the
    /// translate events).
    pub index_set: Option<memory_model::Name>,
    /// Extra related events
    /// these aren't "merged" as part of the same Axiomatic event, but are informational only
    /// e.g. events from the trace (register read/writes) that are useful in debugging and graphing
    pub extra: Vec<&'ev Event<B>>,
    /// Is the event an instruction fetch (i.e. base is ReadMem with an ifetch read_kind)
    pub is_ifetch: bool,
    /// Is the event associated with an address translation function?
    pub translate: Option<TranslationId>,
}

impl<'ev, B: BV> ModelEvent<'ev, B> for AxEvent<'ev, B> {
    fn name(&self) -> memory_model::Name {
        self.mm_name
    }

    fn base_events(&self) -> &[&'ev Event<B>] {
        self.base.as_slice()
    }

    fn index_set(&self) -> Option<memory_model::Name> {
        self.index_set
    }

    fn opcode(&self) -> Option<B> {
        self.opcode
    }
}

/// An iterator overall all the addresses used by an axiomatic event
pub struct AxEventAddresses<'a, 'ev, B> {
    index: usize,
    event: &'a AxEvent<'ev, B>,
}

impl<'a, 'ev, B: BV> Iterator for AxEventAddresses<'a, 'ev, B> {
    type Item = &'ev Val<B>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(base) = self.event.base.get(self.index) {
                self.index += 1;
                match base {
                    Event::ReadMem { address, .. } | Event::WriteMem { address, .. } => return Some(address),
                    _ => continue,
                }
            } else {
                return None;
            }
        }
    }
}

impl<'ev, B: BV> AxEvent<'ev, B> {
    pub fn base(&self) -> Option<&'ev Event<B>> {
        match self.base_events() {
            &[ev] => Some(ev),
            _ => None,
        }
    }

    pub fn address(&self) -> Option<&'ev Val<B>> {
        match self.base()? {
            Event::ReadMem { address, .. } | Event::WriteMem { address, .. } => Some(address),
            _ => None,
        }
    }

    pub fn has_read_reg_of(&self, reg: Name) -> bool {
        self.base.iter().any(|b| b.is_read_reg_of(reg))
    }

    pub fn addresses<'a>(&'a self) -> AxEventAddresses<'a, 'ev, B> {
        AxEventAddresses { index: 0, event: self }
    }

    pub fn read_value(&self) -> Option<(&'ev Val<B>, u32)> {
        match self.base()? {
            Event::ReadMem { value, bytes, .. } => Some((value, *bytes)),
            _ => None,
        }
    }

    pub fn write_data(&self) -> Option<(&'ev Val<B>, u32)> {
        match self.base()? {
            Event::WriteMem { data, bytes, .. } => Some((data, *bytes)),
            _ => None,
        }
    }
}

/// Translations is a map from TranslationId's to axiomatic events
/// that belong to the address translations assocated with each
/// TranslationId
///
/// A note on terminology: In this code we generally refer to
/// individual events as being *translate* events if they were
/// generated by the address translation function specified by the ISA
/// configuration. A *translation* is a set of translate events that
/// logically correspond to an entire address translation
/// operation/page table walk. If translate events are merged into
/// single events, then these coincide.
pub struct Translations<'exec, 'ev, B> {
    translations: HashMap<TranslationId, Vec<&'exec AxEvent<'ev, B>>>,
}

impl<'exec, 'ev, B: BV> Translations<'exec, 'ev, B> {
    fn from_events<I>(events: I) -> Self
    where
        I: Iterator<Item = &'exec AxEvent<'ev, B>>,
    {
        let mut translations = HashMap::new();

        for ev in events {
            if let Some(trans_id) = ev.translate {
                let translate_events = translations.entry(trans_id).or_insert_with(Vec::new);
                translate_events.push(ev)
            }
        }

        for same_translation in translations.values_mut() {
            same_translation.sort_by_key(|ev| (ev.instruction_index, ev.intra_instruction_index));
        }

        Translations { translations }
    }

    /// va_page returns the virtual address associated with an address
    /// translation, provided the TranslateId refers to a set of
    /// translate events that correspond to a page table walk that we
    /// can interpret correctly.
    pub fn va_page(&self, trans_id: TranslationId) -> Option<VirtualAddress> {
        let events = if let Some(events) = self.translations.get(&trans_id) {
            events.as_slice()
        } else {
            return None;
        };

        let table_offset_mask: u64 = 0xFFF;
        let mut indices: [usize; 4] = [0; 4];
        let mut level = 0;

        for ax_event in events {
            for ev in ax_event.base.iter().filter(|ev| ev.in_region("stage 1") && ev.is_memory_read()) {
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
        Some(VirtualAddress::from_indices(indices[0], indices[1], indices[2], indices[3], 0))
    }

    /// ipa_page returns the intermediate physical address associated with an address translation
    pub fn ipa_page(&self, trans_id: TranslationId) -> Option<VirtualAddress> {
        let events = if let Some(events) = self.translations.get(&trans_id) {
            events.as_slice()
        } else {
            return None;
        };

        let table_offset_mask: u64 = 0xFFF;
        let mut indices: Vec<usize> = Vec::new();

        for ax_event in events {
            for ev in ax_event.base.iter().filter(|ev| ev.in_region("stage 2") && ev.is_memory_read()) {
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
        Some(VirtualAddress::from_indices(indices[l - 4], indices[l - 3], indices[l - 2], indices[l - 1], 0))
    }
}

pub mod relations {
    use std::collections::HashMap;

    use isla_lib::bitvector::BV;

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
        ev.base.iter().any(|b| b.in_region("stage 1"))
    }

    pub fn is_in_s2_table<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base.iter().any(|b| b.in_region("stage 2"))
    }

    pub fn is_read<B: BV>(ev: &AxEvent<B>) -> bool {
        !is_translate(ev) && !is_ifetch(ev) && ev.base().filter(|b| b.is_memory_read()).is_some()
    }

    /// \[M\] aka R|W
    pub fn is_memory<B: BV>(ev: &AxEvent<B>) -> bool {
        is_read(ev) || is_write(ev)
    }

    pub fn same_translation<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        match (ev1.translate, ev2.translate) {
            (Some(trans_id1), Some(trans_id2)) => trans_id1 == trans_id2,
            (_, _) => false,
        }
    }

    pub fn amo<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<Option<B>>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        is_read(ev1)
            && is_write(ev2)
            && intra_instruction_ordered(ev1, ev2)
            && rmw_dep(ev1.instruction_index, ev2.instruction_index, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn univ<B: BV>(_: &AxEvent<B>, _: &AxEvent<B>) -> bool {
        true
    }

    pub fn disjoint<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.instruction_index != ev2.instruction_index || ev1.thread_id != ev2.thread_id
    }

    pub fn instruction_order<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.instruction_index < ev2.instruction_index && ev1.thread_id == ev2.thread_id
    }

    /// po is a subset of instruction-order
    /// restricted to a subset of events
    pub fn po<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        instruction_order(ev1, ev2)
            && (is_memory(ev1) || ev1.in_program_order)
            && (is_memory(ev2) || ev2.in_program_order)
    }

    pub fn intra_instruction_ordered<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.instruction_index == ev2.instruction_index
            && ev1.thread_id == ev2.thread_id
            && ev1.intra_instruction_index < ev2.intra_instruction_index
    }

    pub fn internal<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.instruction_index != ev2.instruction_index && ev1.thread_id == ev2.thread_id
    }

    pub fn external<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.thread_id != ev2.thread_id
    }

    pub type DepRel<B> = fn(&AxEvent<B>, &AxEvent<B>, &[Vec<Option<B>>], &HashMap<B, Footprint>) -> bool;

    pub fn addr<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<Option<B>>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        !ev1.is_ifetch
            && !ev2.is_ifetch
            && instruction_order(ev1, ev2)
            && addr_dep(ev1.instruction_index, ev2.instruction_index, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn data<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<Option<B>>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        !ev1.is_ifetch
            && !ev2.is_ifetch
            && instruction_order(ev1, ev2)
            && data_dep(ev1.instruction_index, ev2.instruction_index, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn ctrl<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<Option<B>>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        !ev1.is_ifetch
            && !ev2.is_ifetch
            && po(ev1, ev2)
            && ctrl_dep(ev1.instruction_index, ev2.instruction_index, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn rmw<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<Option<B>>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        (po(ev1, ev2) || intra_instruction_ordered(ev1, ev2))
            && is_read(ev1)
            && is_write(ev2)
            && rmw_dep(ev1.instruction_index, ev2.instruction_index, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn translation_walk_order<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        intra_instruction_ordered(ev1, ev2) && is_translate(ev1) && is_translate(ev2)
    }

    pub fn ifetch_to_execute<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.is_ifetch
            && !ev2.is_ifetch
            && ev1.instruction_index == ev2.instruction_index
            && ev1.thread_id == ev2.thread_id
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

#[derive(Debug)]
pub struct ExecutionInfo<'ev, B> {
    /// A vector containing all the events in a candidate execution to be passed to the smt solver
    pub smt_events: Vec<AxEvent<'ev, B>>,
    /// A vector of other informational events (e.g. reg read/writes) that are not part of the relaxed-memory candidate
    /// but are useful for display purposes
    pub other_events: Vec<AxEvent<'ev, B>>,
    /// A vector of po-ordered instruction opcodes for each thread
    pub thread_opcodes: Vec<Vec<Option<B>>>,
    /// The final write (or initial value if unwritten) for each register in each thread
    pub final_writes: HashMap<(Name, ThreadId), &'ev Val<B>>,
    /// A mapping from SMT symbols to their types
    pub types: HashMap<Sym, Ty>,
    pub function_types: HashMap<Sym, (Vec<Ty>, Ty)>,
}

/// An iterator over the base events in a candidate execution
pub struct BaseEvents<'exec, 'ev, B> {
    ax: usize,
    base: usize,
    execution_info: &'exec ExecutionInfo<'ev, B>,
}

impl<'exec, 'ev, B> Iterator for BaseEvents<'exec, 'ev, B> {
    type Item = (&'exec AxEvent<'ev, B>, usize, &'ev Event<B>);

    fn next(&mut self) -> Option<Self::Item> {
        let ax_event = self.execution_info.smt_events.get(self.ax)?;

        if let Some(base_event) = ax_event.base.get(self.base) {
            self.base += 1;
            Some((ax_event, self.base - 1, base_event))
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
    IllTypedSMT,
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
            IllTypedSMT => write!(
                f,
                "Found ill-typed SMT when processing candidate execution. This is probably a bug",
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
    instruction_index: usize,
    intra_instruction_index: usize,
    thread_id: usize,
    events: Vec<(usize, &'ev Event<B>)>,
}

impl<'ev, B: BV> ExecutionInfo<'ev, B> {
    pub fn base_events<'exec>(&'exec self) -> BaseEvents<'exec, 'ev, B> {
        BaseEvents { ax: 0, base: 0, execution_info: self }
    }

    pub fn translations<'exec>(&'exec self) -> Translations<'exec, 'ev, B> {
        Translations::from_events(self.smt_events.iter().chain(self.other_events.iter()))
    }

    /// A transate event is uninteresting if it is guaranteed to read
    /// from the initial state. There are two modes for this function,
    /// if keep_entire_translation is true we will keep all the events
    /// with the same translation_id as any interesting event,
    /// otherwise we will keep only the interesting events themselves.
    pub fn remove_uninteresting_translates(
        &mut self,
        updated: &HashSet<u64>,
        memory: &Memory<B>,
        keep_entire_translation: bool,
    ) {
        // First, collect all the write addresses for writes to page table memory
        let mut write_addrs = HashSet::new();
        for (_, _, ev) in self.base_events() {
            if let Event::WriteMem { address, region, .. } = ev {
                if *region == "stage 1" || *region == "stage 2" {
                    if let Val::Bits(bv) = address {
                        write_addrs.insert(bv);
                    } else {
                        panic!("Non concrete write address to page table memory")
                    }
                }
            }
        }

        // any `x ?-> _` means translations of x are interesting
        // TODO: do we need this _and_ checking for writes?
        let mut write_addr_pgtable_setup: HashSet<u64> = HashSet::new();
        write_addr_pgtable_setup.extend(updated);

        let mut interesting = Vec::new();
        let mut uninteresting = Vec::new();

        if keep_entire_translation {
            let mut interesting_translation = HashSet::new();
            for ax_event in self.smt_events.iter().filter(|ev| ev.translate.is_some()) {
                match ax_event.base() {
                    Some(Event::ReadMem { address: Val::Bits(bv), .. }) => {
                        if write_addrs.contains(bv)
                            || write_addr_pgtable_setup.contains(&bv.lower_u64())
                            || memory.read_initial(bv.lower_u64(), 8).unwrap_or_else(|_| Val::Bits(B::from_u64(0)))
                                == Val::Bits(B::from_u64(0))
                        {
                            interesting_translation.insert(ax_event.translate.unwrap());
                        }
                    }
                    Some(Event::ReadMem { address: _, .. }) => panic!("Non concrete read from page table memory"),
                    _ => (),
                }
            }
            for ax_event in self.smt_events.drain(..) {
                if ax_event.translate.is_none() || interesting_translation.contains(&ax_event.translate.unwrap()) {
                    interesting.push(ax_event)
                } else {
                    uninteresting.push(ax_event)
                }
            }
        } else {
            for ax_event in self.smt_events.drain(..) {
                if ax_event.translate.is_none() {
                    interesting.push(ax_event)
                } else {
                    match ax_event.base() {
                        Some(Event::ReadMem { address: Val::Bits(bv), .. }) => {
                            if write_addrs.contains(bv)
                                || write_addr_pgtable_setup.contains(&bv.lower_u64())
                                || memory.read_initial(bv.lower_u64(), 8).unwrap_or_else(|_| Val::Bits(B::from_u64(0)))
                                    == Val::Bits(B::from_u64(0))
                            {
                                interesting.push(ax_event)
                            } else {
                                uninteresting.push(ax_event)
                            }
                        }
                        Some(Event::ReadMem { address: _, .. }) => panic!("Non concrete read from page table memory"),
                        _ => interesting.push(ax_event),
                    }
                }
            }
        }

        self.smt_events = interesting;
        self.other_events.append(&mut uninteresting);
    }

    /// This function merges translate events (typically memory reads
    /// to page table entries) with the same translation id into
    /// larger whole translation events each containing a sequence of
    /// base events
    pub fn merge_translations(&mut self, split_stages: bool, symtab: &mut memory_model::Symtab) {
        let mut all_translations: HashMap<TranslationId, MergedTranslation<'ev, B>> = HashMap::new();

        let index_set = symtab.lookup("T");

        // For each instruction (identified by a opcode, po, and
        // thread_id triple), we extract the translate events,
        // grouping them into possibly multiple translations
        // consisting of sequences of consecutive translate events
        self.smt_events.retain(|ev| {
            if let Some(trans_id) = ev.translate {
                let merged = all_translations.entry(trans_id).or_insert_with(|| MergedTranslation {
                    opcode: ev.opcode.unwrap(),
                    instruction_index: ev.instruction_index,
                    intra_instruction_index: ev.intra_instruction_index,
                    thread_id: ev.thread_id,
                    events: Vec::new(),
                });

                // Each translate event we encounter with a specific
                // translation id should be from the same instruction
                assert_eq!(ev.opcode.unwrap(), merged.opcode);
                assert_eq!(ev.instruction_index, merged.instruction_index);
                assert_eq!(ev.thread_id, merged.thread_id);

                for base in &ev.base {
                    merged.events.push((ev.intra_instruction_index, base))
                }
                merged.intra_instruction_index =
                    std::cmp::min(merged.intra_instruction_index, ev.intra_instruction_index);

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
            if split_stages {
                let s1_name = format!("TRANS_S1_{}", trans_id);
                let s2_name = format!("TRANS_S2_{}", trans_id);
                self.smt_events.push(AxEvent {
                    opcode: Some(merged.opcode),
                    instruction_index: merged.instruction_index,
                    intra_instruction_index: merged.intra_instruction_index,
                    in_program_order: false,
                    thread_id: merged.thread_id,
                    name: s1_name.clone(),
                    mm_name: symtab.intern_owned(s1_name),
                    base: merged.events[0..20].iter().map(|(_, base)| *base).collect(),
                    index_set,
                    extra: Vec::new(),
                    is_ifetch: false,
                    translate: Some(trans_id),
                });
                self.smt_events.push(AxEvent {
                    opcode: Some(merged.opcode),
                    instruction_index: merged.instruction_index,
                    intra_instruction_index: merged.intra_instruction_index,
                    in_program_order: false,
                    thread_id: merged.thread_id,
                    name: s2_name.clone(),
                    mm_name: symtab.intern_owned(s2_name),
                    base: merged.events[20..].iter().map(|(_, base)| *base).collect(),
                    index_set,
                    extra: Vec::new(),
                    is_ifetch: false,
                    translate: Some(trans_id),
                })
            } else {
                let name = format!("TRANS_{}", trans_id);
                self.smt_events.push(AxEvent {
                    opcode: Some(merged.opcode),
                    instruction_index: merged.instruction_index,
                    intra_instruction_index: merged.intra_instruction_index,
                    in_program_order: false,
                    thread_id: merged.thread_id,
                    name: name.clone(),
                    mm_name: symtab.intern_owned(name),
                    base: merged.events.iter().map(|(_, base)| *base).collect(),
                    index_set,
                    extra: Vec::new(),
                    is_ifetch: false,
                    translate: Some(trans_id),
                })
            }
        }
    }

    pub fn from(
        candidate: &'ev [&[Event<B>]],
        shared_state: &SharedState<B>,
        isa_config: &ISAConfig<B>,
        graph_opts: &GraphOpts,
        ignore_ifetch: bool,
        symtab: &mut memory_model::Symtab,
    ) -> Result<Self, CandidateError<B>> {
        use CandidateError::*;

        struct CycleEvent<'a, B> {
            tid: usize,
            name: String,
            event: &'a Event<B>,
            in_program_order: bool,
            is_ifetch: bool,
            translate: Option<usize>,
            include_in_smt: bool,
        }

        macro_rules! cycle_constructor {
            ($f: ident, $in_program_order: expr, $is_ifetch: expr, $include_in_smt: expr, $a: lifetime, $ty: ty) => {
                fn $f(prefix: &str, po: usize, eid: usize, tid: usize, event: &$a Event<$ty>, translate: Option<usize>) -> Self {
                    CycleEvent {
                        tid,
                        name: format!("{}{}_{}_{}", prefix, po, eid, tid),
                        event,
                        in_program_order: $in_program_order,
                        is_ifetch: $is_ifetch,
                        translate,
                        include_in_smt: $include_in_smt
                    }
                }
            }
        }

        impl<'a, B> CycleEvent<'a, B> {
            cycle_constructor!(new, false, false, true, 'a, B);
            cycle_constructor!(new_in_program_order, true, false, true, 'a, B);
            cycle_constructor!(new_ifetch, false, true, true, 'a, B);
            cycle_constructor!(new_graph, false, false, false, 'a, B);
        }

        let mut exec = ExecutionInfo {
            smt_events: Vec::new(),
            other_events: Vec::new(),
            thread_opcodes: vec![Vec::new(); candidate.len()],
            final_writes: HashMap::new(),
            types: HashMap::new(),
            function_types: HashMap::new(),
        };

        let read_event_registers = isa_config.read_event_registers();
        let write_event_registers = isa_config.write_event_registers();

        let mut call_stack = CallStack::new();

        for (tid, thread) in candidate.iter().enumerate() {
            for (po, cycle) in thread.split(|ev| ev.is_cycle()).enumerate() {
                let mut cycle_events: Vec<CycleEvent<'_, B>> = Vec::new();
                let mut cycle_instr: Option<B> = None;

                'event_loop: for (eid, event) in cycle.iter().enumerate() {
                    let translate = if let Some(translation_function) = isa_config.translation_function {
                        call_stack.contains(translation_function)
                    } else {
                        None
                    };
                    match event {
                        Event::Smt(Def::DeclareConst(v, ty), _, _) => {
                            exec.types.insert(*v, ty.clone());
                        }

                        Event::Smt(Def::DeclareFun(v, arg_tys, result_ty), _, _) => {
                            exec.function_types.insert(*v, (arg_tys.clone(), result_ty.clone()));
                        }

                        Event::Smt(Def::DefineConst(v, exp), _, _) => {
                            let ty = exp.infer(&exec.types, &exec.function_types).ok_or(CandidateError::IllTypedSMT)?;
                            exec.types.insert(*v, ty);
                        }

                        Event::WriteReg(reg, _, val) => {
                            // Only include read/write register events after the instruction fetch
                            if cycle_instr.is_some() {
                                if write_event_registers.contains(reg) {
                                    cycle_events.push(CycleEvent::new("Wreg", po, eid, tid, event, translate));
                                } else {
                                    // Add all other Wreg events so they can be displayed or hidden as needed in graph.rs
                                    cycle_events.push(CycleEvent::new_graph("Wreg", po, eid, tid, event, None))
                                }
                            }
                            exec.final_writes.insert((*reg, tid), val);
                        }

                        Event::ReadReg(reg, _, _) => {
                            if cycle_instr.is_some() {
                                if read_event_registers.contains(reg) {
                                    cycle_events.push(CycleEvent::new("Rreg", po, eid, tid, event, translate));
                                } else {
                                    cycle_events.push(CycleEvent::new_graph("Rreg", po, eid, tid, event, None))
                                }
                            }
                        }

                        // The first event is only for initialisation, so we don't want to process any actual events
                        _ if po == 0 => continue 'event_loop,

                        Event::Instr(Val::Bits(bv)) => {
                            if let Some(opcode) = cycle_instr {
                                return Err(MultipleInstructionsInCycle { opcode1: *bv, opcode2: opcode });
                            } else {
                                exec.thread_opcodes[tid].push(Some(*bv));
                                cycle_instr = Some(*bv)
                            }
                        }

                        Event::ReadMem { .. } => {
                            if cycle_instr.is_none() {
                                cycle_events.push(CycleEvent::new_ifetch("R", po, eid, tid, event, translate))
                            } else {
                                cycle_events.push(CycleEvent::new("R", po, eid, tid, event, translate))
                            }
                        }

                        Event::WriteMem { .. } => cycle_events.push(CycleEvent::new("W", po, eid, tid, event, None)),

                        Event::Function { name, call } => {
                            if *call {
                                call_stack.push(*name);
                            } else if let Some(stack_name) = call_stack.pop() {
                                assert_eq!(stack_name, *name)
                            } else {
                                panic!("unbalanced call stack when processing trace")
                            };

                            if graph_opts.debug && cycle_instr.is_some() {
                                cycle_events.push(CycleEvent::new_graph("E", po, eid, tid, event, None))
                            }
                        }

                        Event::Abstract { name, primitive, .. } => {
                            if *primitive {
                                let str_name = shared_state.symtab.to_str(*name);
                                if isa_config.in_program_order.contains(name) {
                                    cycle_events
                                        .push(CycleEvent::new_in_program_order(str_name, po, eid, tid, event, None))
                                } else {
                                    cycle_events.push(CycleEvent::new(str_name, po, eid, tid, event, None))
                                }
                            }
                        }

                        Event::Branch { .. } => {
                            if graph_opts.debug && cycle_instr.is_some() {
                                cycle_events.push(CycleEvent::new_graph("E", po, eid, tid, event, None))
                            }
                        }

                        _ => (),
                    }
                }

                if po != 0 {
                    if cycle_instr.is_none() {
                        exec.thread_opcodes[tid].push(None)
                    }

                    for (
                        iio,
                        CycleEvent { tid, name, event, in_program_order, is_ifetch, translate, include_in_smt },
                    ) in cycle_events.drain(..).enumerate()
                    {
                        let evs = if include_in_smt && !(ignore_ifetch && is_ifetch) {
                            &mut exec.smt_events
                        } else {
                            &mut exec.other_events
                        };

                        // An event is a translate event if it was
                        // created by the translation function
                        evs.push(AxEvent {
                            opcode: cycle_instr,
                            instruction_index: po - 1,
                            intra_instruction_index: iio,
                            in_program_order,
                            thread_id: tid,
                            name: name.clone(),
                            mm_name: symtab.intern_owned(name),
                            base: vec![event],
                            index_set: None,
                            extra: vec![],
                            is_ifetch,
                            translate,
                        })
                    }
                }
            }

            assert!(call_stack.is_empty())
        }

        Ok(exec)
    }
}

// === final_loc_values ===

#[derive(Debug)]
pub enum FinalLocValuesError<'l> {
    ReadModelError(String),
    LocInterpretError,
    BadAddressWidth(&'l String, u32),
    BadLastWriteTo(&'l String),
    BadRegisterName(&'l Name, usize),
    BadAddress(&'l String),
}

impl<'l> IslaError for FinalLocValuesError<'l> {
    fn source_loc(&self) -> SourceLoc {
        SourceLoc::unknown()
    }
}

impl<'l> fmt::Display for FinalLocValuesError<'l> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use FinalLocValuesError::*;
        write!(f, "Failed to get final register state: ")?;
        match self {
            ReadModelError(s) => {
                write!(f, "Failed to parse smt model: {}", s)
            }
            LocInterpretError => {
                write!(f, "Failed to read from smt model")
            }
            BadAddressWidth(addr, width) => {
                write!(f, "Bad address width, {} has width {}, but should be one of [4, 8]", addr, width)
            }
            BadLastWriteTo(val) => {
                write!(f, "Bad last_write_to({}), should return Bits", val)
            }
            BadRegisterName(reg, thread_id) => {
                write!(f, "Could not find register {}:{:?}", thread_id, reg)
            }
            BadAddress(addr) => {
                write!(f, "Could not find address {}", addr)
            }
        }
    }
}

impl<'l> Error for FinalLocValuesError<'l> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

pub fn final_state_from_z3_output<'exec, 'ev, 'litmus, 'model, B: BV>(
    litmus: &'litmus Litmus<B>,
    exec: &'ev ExecutionInfo<'ev, B>,
    final_assertion_locs: &'litmus HashSet<&'litmus LitmusLoc<String>>,
    z3_output: &'model str,
) -> Result<HashMap<LitmusLoc<String>, Val<B>>, FinalLocValuesError<'litmus>> {
    // parse the Z3 output to produce a Model
    // that allows us to lookup the values z3 produced
    // later in the code
    let model_buf: &str = &z3_output[3..];
    let mut event_names: Vec<&'ev str> = exec.smt_events.iter().map(|ev| ev.name.as_ref()).collect();
    event_names.push("IW");
    let mut model = Model::<B>::parse(&event_names, model_buf)
        .map_err(|mpe| FinalLocValuesError::ReadModelError(format!("{}", mpe)))?;

    let mut calc = |loc: &'litmus LitmusLoc<String>| match loc {
        LitmusLoc::Register { reg, thread_id } => exec
            .final_writes
            .get(&(*reg, *thread_id))
            .cloned()
            .cloned()
            .ok_or_else(|| FinalLocValuesError::BadRegisterName(reg, *thread_id)),
        LitmusLoc::LastWriteTo { address, bytes } => {
            let symbolic_addr =
                litmus.symbolic_addrs.get(address).ok_or_else(|| FinalLocValuesError::BadAddress(address))?;
            let addr_bv = B::from_u64(*symbolic_addr);

            let r = if *bytes == 4 {
                model
                    .interpret("last_write_to_32", &[SexpVal::Bits(addr_bv)])
                    .map_err(|_ie| FinalLocValuesError::LocInterpretError)
            } else if *bytes == 8 {
                model
                    .interpret("last_write_to_64", &[SexpVal::Bits(addr_bv)])
                    .map_err(|_ie| FinalLocValuesError::LocInterpretError)
            } else {
                Err(FinalLocValuesError::BadAddressWidth(address, *bytes))
            }?;

            match r {
                SexpVal::Bits(b) => Ok(Val::Bits(b)),
                _ => Err(FinalLocValuesError::BadLastWriteTo(address)),
            }
        }
    };

    let mut values: HashMap<LitmusLoc<String>, Val<B>> = HashMap::new();

    for loc in final_assertion_locs {
        let v = calc(loc)?;
        values.insert((*loc).clone(), v);
    }

    Ok(values)
}
