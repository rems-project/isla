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
use isla_lib::ir::{Name, SharedState, Val};
use isla_lib::memory::Memory;
use isla_lib::smt::{register_name_string, EvPath, Event};

use crate::graph::GraphOpts;
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

/// An AxEvent (axiomatic event) is a set of base events from an Isla
/// trace combined with metadata about where and when it was executed
/// in a candidate execution. This can be combined with the footprint
/// analysis to determine various dependency orders on events.
#[derive(Debug)]
pub struct AxEvent<'ev, B> {
    /// The opcode for the instruction that contained the underlying event
    pub opcode: B,
    /// The place of the event in the instruction-order (the sequence
    /// of instructions as they appear in the trace) for it's thread
    pub instruction_index: usize,
    /// If a single instruction contains multiple events, this is the
    /// index in that sequence of events
    pub intra_instruction_index: usize,
    /// The thread id for the event
    pub thread_id: ThreadId,
    /// A generated unique name for the event
    pub name: String,
    /// The underlying event(s) in the SMT trace
    pub base: Vec<&'ev Event<B>>,
    /// Extra related events
    /// these aren't "merged" as part of the same Axiomatic event, but are informational only
    /// e.g. events from the trace (register read/writes) that are useful in debugging and graphing
    pub extra: Vec<&'ev Event<B>>,
    /// Is the event an instruction fetch (i.e. base is ReadMem with an ifetch read_kind)
    pub is_ifetch: bool,
    /// Is the event associated with an address translation function?
    pub translate: Option<TranslationId>,
}

/// An iterator overall all the addresses used by an axiomatic event
pub struct AxEventAddresses<'a, 'ev, B> {
    index: usize,
    event: &'a AxEvent<'ev, B>,
}

#[derive(PartialEq)]
pub enum ArmInstr {
    LDR,
    STR,
    STLR,
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
        if self.base.len() == 1 {
            Some(self.base[0])
        } else {
            None
        }
    }

    pub fn address(&self) -> Option<&'ev Val<B>> {
        match self.base()? {
            Event::ReadMem { address, .. } | Event::WriteMem { address, .. } | Event::CacheOp { address, .. } => {
                Some(address)
            }
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

    /// guesses which Arm instruction this event originated from
    /// based on the opcode
    ///
    /// when the interface is fully implemented and we have cat language to read from its data
    /// then this function can be eliminated entirely
    pub fn arm_instr(&self) -> Option<ArmInstr> {
        let op = self.opcode;
        let top = op.slice(29, 21)?;
        let top_u64 = top.lower_u64();
        if top_u64 == 0b111_0_00_00_0 {
            Some(ArmInstr::STR)
        } else if top_u64 == 0b111_0_00_01_0 {
            Some(ArmInstr::LDR)
        } else if top_u64 == 0b001000_1_0_0 {
            Some(ArmInstr::STLR)
        } else {
            None
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
        Some(VirtualAddress::from_indices(indices[l - 4], indices[l - 3], indices[l - 2], indices[l - 1], 0))
    }
}

pub mod relations {
    use std::collections::HashMap;

    use isla_lib::bitvector::BV;

    use super::ArmInstr;
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
        ev.base.iter().any(|b| b.has_memory_kind("stage 1"))
    }

    pub fn is_in_s2_table<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base.iter().any(|b| b.has_memory_kind("stage 2"))
    }

    pub fn is_read<B: BV>(ev: &AxEvent<B>) -> bool {
        !is_translate(ev) && !is_ifetch(ev) && ev.base().filter(|b| b.is_memory_read()).is_some()
    }

    /// [M] aka R|W
    pub fn is_memory<B: BV>(ev: &AxEvent<B>) -> bool {
        is_read(ev) || is_write(ev)
    }

    pub fn is_barrier<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base().filter(|b| b.is_barrier()).is_some()
    }

    pub fn is_cache_op<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base().filter(|b| b.is_cache_op()).is_some()
    }

    pub fn is_from_instr<B: BV>(ev: &AxEvent<B>, i: ArmInstr) -> bool {
        match ev.arm_instr() {
            Some(instr) if instr == i => true,
            _ => false,
        }
    }

    pub fn is_from_str_instr<B: BV>(ev: &AxEvent<B>) -> bool {
        is_from_instr(ev, ArmInstr::STR) || is_from_instr(ev, ArmInstr::STLR)
    }

    pub fn is_from_ldr_instr<B: BV>(ev: &AxEvent<B>) -> bool {
        is_from_instr(ev, ArmInstr::LDR)
    }

    pub fn is_ghost_fault_event<B: BV>(ev: &AxEvent<B>) -> bool {
        // ghost "fault" events are barriers not from a barrier instruction
        ev.base().filter(|b| b.is_barrier()).is_some() && (is_from_str_instr(ev) || is_from_ldr_instr(ev))
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
        thread_opcodes: &[Vec<B>],
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
    /// restricted to read|write|fence|cache-op events
    pub fn po<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        instruction_order(ev1, ev2)
            && (is_memory(ev1) || is_barrier(ev1) || is_cache_op(ev1))
            && (is_memory(ev2) || is_barrier(ev2) || is_cache_op(ev2))
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

    pub type DepRel<B> = fn(&AxEvent<B>, &AxEvent<B>, &[Vec<B>], &HashMap<B, Footprint>) -> bool;

    pub fn addr<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
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
        thread_opcodes: &[Vec<B>],
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
        thread_opcodes: &[Vec<B>],
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
        thread_opcodes: &[Vec<B>],
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
    pub thread_opcodes: Vec<Vec<B>>,
    /// The final write (or initial value if unwritten) for each register in each thread
    pub final_writes: HashMap<(Name, ThreadId), &'ev Val<B>>,
}

/// An iterator over the base events in a candidate execution
pub struct BaseEvents<'exec, 'ev, B> {
    ax: usize,
    base: usize,
    execution_info: &'exec ExecutionInfo<'ev, B>,
}

impl<'exec, 'ev, B> Iterator for BaseEvents<'exec, 'ev, B> {
    type Item = (&'exec AxEvent<'ev, B>, &'ev Event<B>);

    fn next(&mut self) -> Option<Self::Item> {
        let ax_event = self.execution_info.smt_events.get(self.ax)?;

        if let Some(base_event) = ax_event.base.get(self.base) {
            self.base += 1;
            Some((ax_event, base_event))
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
    pub fn remove_uninteresting_translates(&mut self, memory: &Memory<B>, keep_entire_translation: bool) {
        // First, collect all the write addresses for writes to page table memory
        let mut write_addrs = HashSet::new();
        for (_, ev) in self.base_events() {
            if let Event::WriteMem { address, kind, .. } = ev {
                if *kind == "stage 1" || *kind == "stage 2" {
                    if let Val::Bits(bv) = address {
                        write_addrs.insert(bv);
                    } else {
                        panic!("Non concrete write address to page table memory")
                    }
                }
            }
        }

        let mut interesting = Vec::new();
        let mut uninteresting = Vec::new();

        if keep_entire_translation {
            let mut interesting_translation = HashSet::new();
            for ax_event in self.smt_events.iter().filter(|ev| ev.translate.is_some()) {
                match ax_event.base() {
                    Some(Event::ReadMem { address: Val::Bits(bv), .. }) => {
                        if write_addrs.contains(bv)
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
    pub fn merge_translations(&mut self, split_stages: bool) {
        let mut all_translations: HashMap<TranslationId, MergedTranslation<'ev, B>> = HashMap::new();

        // For each instruction (identified by a opcode, po, and
        // thread_id triple), we extract the translate events,
        // grouping them into possibly multiple translations
        // consisting of sequences of consecutive translate events
        self.smt_events.retain(|ev| {
            if let Some(trans_id) = ev.translate {
                let merged = all_translations.entry(trans_id).or_insert_with(|| MergedTranslation {
                    opcode: ev.opcode,
                    instruction_index: ev.instruction_index,
                    intra_instruction_index: ev.intra_instruction_index,
                    thread_id: ev.thread_id,
                    events: Vec::new(),
                });

                // Each translate event we encounter with a specific
                // translation id should be from the same instruction
                assert_eq!(ev.opcode, merged.opcode);
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
                self.smt_events.push(AxEvent {
                    opcode: merged.opcode,
                    instruction_index: merged.instruction_index,
                    intra_instruction_index: merged.intra_instruction_index,
                    thread_id: merged.thread_id,
                    name: format!("TRANS_S1_{}", trans_id),
                    base: merged.events[0..20].iter().map(|(_, base)| *base).collect(),
                    extra: Vec::new(),
                    is_ifetch: false,
                    translate: Some(trans_id),
                });
                self.smt_events.push(AxEvent {
                    opcode: merged.opcode,
                    instruction_index: merged.instruction_index,
                    intra_instruction_index: merged.intra_instruction_index,
                    thread_id: merged.thread_id,
                    name: format!("TRANS_S2_{}", trans_id),
                    base: merged.events[20..].iter().map(|(_, base)| *base).collect(),
                    extra: Vec::new(),
                    is_ifetch: false,
                    translate: Some(trans_id),
                })
            } else {
                self.smt_events.push(AxEvent {
                    opcode: merged.opcode,
                    instruction_index: merged.instruction_index,
                    intra_instruction_index: merged.intra_instruction_index,
                    thread_id: merged.thread_id,
                    name: format!("TRANS_{}", trans_id),
                    base: merged.events.iter().map(|(_, base)| *base).collect(),
                    extra: Vec::new(),
                    is_ifetch: false,
                    translate: Some(trans_id),
                })
            }
        }
    }

    /// This function merges TTBR write barrier events with
    /// their respective WriteReg event
    pub fn attach_ttbr_extras(&mut self, shared_state: &SharedState<B>) {
        let mut last_write_reg = None;

        let mut events: Vec<_> = self.smt_events.iter_mut().chain(self.other_events.iter_mut()).collect();
        events.sort_by_key(|ev| (ev.thread_id, ev.instruction_index, ev.intra_instruction_index));

        for ev in events {
            match ev.base() {
                Some(Event::WriteReg(_, _, _)) => {
                    let regname =
                        register_name_string(ev.base().unwrap(), &shared_state.symtab).unwrap().to_uppercase();
                    if regname == "VTTBR_EL2" || regname == "TTBR0_EL1" || regname == "TTBR0_EL2" {
                        last_write_reg = Some(ev);
                    }
                }

                Some(Event::Barrier { .. }) => {
                    if let Some(ev_prev) = &last_write_reg {
                        if ev_prev.instruction_index == ev.instruction_index {
                            ev.extra.insert(0, ev_prev.base().unwrap());
                        } else {
                            last_write_reg = None;
                        }
                    }
                }

                _ => (),
            }
        }
    }

    pub fn from(
        candidate: &'ev [&[Event<B>]],
        shared_state: &SharedState<B>,
        isa_config: &ISAConfig<B>,
        graph_opts: &GraphOpts,
    ) -> Result<Self, CandidateError<B>> {
        use CandidateError::*;

        struct CycleEvent<'a, B> {
            tid: usize,
            name: String,
            event: &'a Event<B>,
            is_ifetch: bool,
            translate: Option<usize>,
            include_in_smt: bool,
        }

        macro_rules! cycle_constructor {
            ($f: ident, $is_ifetch: expr, $include_in_smt: expr, $a: lifetime, $ty: ty) => {
                fn $f(prefix: &str, po: usize, eid: usize, tid: usize, event: &$a Event<$ty>, translate: Option<usize>) -> Self {
                    CycleEvent {
                        tid,
                        name: format!("{}{}_{}_{}", prefix, po, eid, tid),
                        event,
                        is_ifetch: $is_ifetch,
                        translate,
                        include_in_smt: $include_in_smt
                    }
                }
            }
        }

        impl<'a, B> CycleEvent<'a, B> {
            cycle_constructor!(new, false, true, 'a, B);
            cycle_constructor!(new_ifetch, true, true, 'a, B);
            cycle_constructor!(new_graph, false, false, 'a, B);
        }

        let mut exec = ExecutionInfo {
            smt_events: Vec::new(),
            other_events: Vec::new(),
            thread_opcodes: vec![Vec::new(); candidate.len()],
            final_writes: HashMap::new(),
        };

        let rk_ifetch = shared_state.enum_member(isa_config.ifetch_read_kind).expect("Invalid ifetch read kind");

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
                                exec.thread_opcodes[tid].push(*bv);
                                cycle_instr = Some(*bv)
                            }
                        }
                        Event::ReadMem { read_kind: Val::Enum(e), .. } => {
                            if e.member == rk_ifetch {
                                cycle_events.push(CycleEvent::new_ifetch("R", po, eid, tid, event, translate))
                            } else {
                                cycle_events.push(CycleEvent::new("R", po, eid, tid, event, translate))
                            }
                        }
                        Event::ReadMem { .. } => panic!("ReadMem event with non-concrete enum read_kind"),
                        Event::WriteMem { .. } => cycle_events.push(CycleEvent::new("W", po, eid, tid, event, None)),
                        Event::Barrier { .. } => cycle_events.push(CycleEvent::new("F", po, eid, tid, event, None)),
                        Event::CacheOp { .. } => cycle_events.push(CycleEvent::new("C", po, eid, tid, event, None)),
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
                        Event::Branch { .. } | Event::Instr(_) => {
                            if graph_opts.debug && cycle_instr.is_some() {
                                cycle_events.push(CycleEvent::new_graph("E", po, eid, tid, event, None))
                            }
                        }
                        _ => (),
                    }
                }

                if po != 0 {
                    for (iio, CycleEvent { tid, name, event, is_ifetch, translate, include_in_smt }) in
                        cycle_events.drain(..).enumerate()
                    {
                        // Events must be associated with an instruction
                        if let Some(opcode) = cycle_instr {
                            let evs = if include_in_smt { &mut exec.smt_events } else { &mut exec.other_events };

                            // An event is a translate event if it was
                            // created by the translation function
                            evs.push(AxEvent {
                                opcode,
                                instruction_index: po - 1,
                                intra_instruction_index: iio,
                                thread_id: tid,
                                name,
                                base: vec![event],
                                extra: vec![],
                                is_ifetch,
                                translate,
                            })
                        } else if !event.has_read_kind(rk_ifetch) {
                            // Unless we have a single failing ifetch
                            return Err(NoInstructionsInCycle);
                        }
                    }
                }
            }

            assert!(call_stack.is_empty())
        }

        exec.attach_ttbr_extras(shared_state);
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
                    sexp.into_bits().ok_or(InterpretError::NotFound(smt_name))
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
