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

//! This module implements utilities for working with axiomatic memory
//! models.

use std::collections::HashMap;
use std::error::Error;
use std::fmt;

use crate::concrete::BV;
use crate::ir::Val;
use crate::smt::{EvPath, Event};

pub type ThreadId = usize;

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
    opcode: B,
    /// The place of the event in po-order for it's thread
    po: usize,
    /// The thread id for the event
    thread_id: ThreadId,
    /// A generated unique name for the event
    pub name: String,
    /// The underlying event in the SMT trace
    base: &'a Event<B>,
}

impl<'a, B: BV> AxEvent<'a, B> {
    pub fn address(&self) -> Option<&'a Val<B>> {
        match self.base {
            Event::ReadMem { address, .. } | Event::WriteMem { address, .. } => Some(address),
            _ => None,
        }
    }

    pub fn read_value(&self) -> Option<(&'a Val<B>, u32)> {
        match self.base {
            Event::ReadMem { value, bytes, .. } => Some((value, *bytes)),
            _ => None,
        }
    }

    pub fn write_data(&self) -> Option<&'a Val<B>> {
        match self.base {
            Event::WriteMem { data, .. } => Some(data),
            _ => None,
        }
    }
}

pub mod relations {
    use std::collections::HashMap;

    use super::AxEvent;
    use crate::concrete::BV;
    use crate::footprint_analysis::{addr_dep, ctrl_dep, data_dep, Footprint};

    pub fn is_write<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base.is_memory_write()
    }

    pub fn is_read<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base.is_memory_read()
    }

    // TODO:
    pub fn rmw<B: BV>(_ev1: &AxEvent<B>, _ev2: &AxEvent<B>) -> bool {
        false
    }

    // TODO:
    pub fn amo<B: BV>(_ev1: &AxEvent<B>, _ev2: &AxEvent<B>) -> bool {
        false
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

    pub fn internal<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po != ev2.po && ev1.thread_id == ev2.thread_id
    }

    pub fn external<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po != ev2.po && ev1.thread_id != ev2.thread_id
    }

    pub fn addr<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        po(ev1, ev2) && addr_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
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
        po(ev1, ev2) && ctrl_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }
}

pub struct ExecutionInfo<'ev, B> {
    /// A vector containing all the events in a candidate execution
    pub events: Vec<AxEvent<'ev, B>>,
    /// A vector of po-ordered instruction opcodes for each thread
    pub thread_opcodes: Vec<Vec<B>>,
    /// The final write for each register in each thread (if written at all)
    pub final_writes: HashMap<(u32, ThreadId), &'ev Val<B>>,
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

impl<'ev, B: BV> ExecutionInfo<'ev, B> {
    pub fn from(candidate: &'ev [&[Event<B>]]) -> Result<Self, CandidateError<B>> {
        use CandidateError::*;
        let mut exec = ExecutionInfo {
            events: Vec::new(),
            thread_opcodes: vec![Vec::new(); candidate.len()],
            final_writes: HashMap::new(),
        };

        for (tid, thread) in candidate.iter().enumerate() {
            for (po, cycle) in thread.split(|ev| ev.is_cycle()).skip(1).enumerate() {
                let mut cycle_events: Vec<(usize, String, &Event<B>)> = Vec::new();
                let mut cycle_instr: Option<B> = None;

                for (eid, event) in cycle.iter().enumerate() {
                    match event {
                        Event::Instr(Val::Bits(bv)) => {
                            if let Some(opcode) = cycle_instr {
                                return Err(MultipleInstructionsInCycle { opcode1: *bv, opcode2: opcode });
                            } else {
                                exec.thread_opcodes[tid].push(*bv);
                                cycle_instr = Some(*bv)
                            }
                        }
                        Event::ReadMem { .. } => cycle_events.push((tid, format!("R{}_{}_{}", po, eid, tid), event)),
                        Event::WriteMem { .. } => cycle_events.push((tid, format!("W{}_{}_{}", po, eid, tid), event)),
                        Event::WriteReg(reg, _, val) => {
                            exec.final_writes.insert((*reg, tid), val);
                        }
                        _ => (),
                    }
                }

                for (tid, evid, ev) in cycle_events {
                    if let Some(opcode) = cycle_instr {
                        exec.events.push(AxEvent { opcode, po, thread_id: tid, name: evid, base: ev })
                    } else {
                        return Err(NoInstructionsInCycle);
                    }
                }
            }
        }

        Ok(exec)
    }
}

pub mod run_litmus {
    use crossbeam::queue::{ArrayQueue, SegQueue};
    use crossbeam::thread;
    use std::collections::HashMap;
    use std::error::Error;
    use std::fmt;
    use std::path::Path;
    use std::sync::Arc;
    use std::time::Instant;

    use crate::concrete::BV;
    use crate::config::ISAConfig;
    use crate::executor;
    use crate::executor::LocalFrame;
    use crate::footprint_analysis::{footprint_analysis, Footprint, FootprintError};
    use crate::ir::*;
    use crate::litmus::Litmus;
    use crate::log;
    use crate::memory::Memory;
    use crate::simplify;
    use crate::smt::{EvPath, Event};

    use super::{Candidates, ThreadId};

    #[derive(Debug)]
    pub enum LitmusRunError {
        NoReadIFetch,
        NoMain,
        Execution(String),
        Footprint(FootprintError),
    }

    impl fmt::Display for LitmusRunError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            use LitmusRunError::*;
            match self {
                NoMain => write!(
                    f,
                    "There is no `main` function in the specified architecture.\
                     This function is used as the entry point for each thread in a litmus test."
                ),
                NoReadIFetch => write!(f, "No `Read_ifetch' read kind found in specified architecture!"),
                Execution(msg) => write!(f, "Error during symbolic execution: {}", msg),
                Footprint(e) => write!(f, "{}", e),
            }
        }
    }

    impl Error for LitmusRunError {
        fn source(&self) -> Option<&(dyn Error + 'static)> {
            None
        }
    }

    pub fn litmus_per_candidate<B, P, F>(
        num_threads: usize,
        litmus: &Litmus,
        regs: Bindings<B>,
        mut lets: Bindings<B>,
        shared_state: &SharedState<B>,
        isa_config: &ISAConfig<B>,
        cache: P,
        callback: &F,
    ) -> Result<(), LitmusRunError>
    where
        B: BV,
        P: AsRef<Path>,
        F: Sync + Send + Fn(ThreadId, &[&[Event<B>]], &HashMap<B, Footprint>) -> (),
    {
        use LitmusRunError::*;

        let mut memory = Memory::new();
        memory.add_concrete_region(isa_config.thread_base..isa_config.thread_top, HashMap::new());

        let mut current_base = isa_config.thread_base;
        for (thread, _, code) in litmus.assembled.iter() {
            log!(log::VERBOSE, &format!("Thread {} @ 0x{:x}", thread, current_base));
            for (i, byte) in code.iter().enumerate() {
                memory.write_byte(current_base + i as u64, *byte)
            }
            current_base += isa_config.thread_stride
        }
        memory.log();

        let function_id = match shared_state.symtab.get("zmain") {
            Some(id) => id,
            None => return Err(NoMain),
        };

        let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
        let tasks: Vec<_> = litmus
            .assembled
            .iter()
            .enumerate()
            .map(|(i, (_, inits, _))| {
                let address = isa_config.thread_base + (isa_config.thread_stride * i as u64);
                lets.insert(ELF_ENTRY, UVal::Init(Val::I128(address as i128)));
                let mut regs = regs.clone();
                for (reg, value) in inits {
                    regs.insert(*reg, UVal::Init(Val::Bits(B::from_u64(*value))));
                }
                LocalFrame::new(args, Some(&[Val::Unit]), instrs)
                    .add_lets(&lets)
                    .add_regs(&regs)
                    .set_memory(memory.clone())
                    .task(i)
            })
            .collect();

        let mut thread_buckets: Vec<Vec<EvPath<B>>> = vec![Vec::new(); tasks.len()];
        let queue = Arc::new(SegQueue::new());

        let now = Instant::now();
        executor::start_multi(num_threads, tasks, &shared_state, queue.clone(), &executor::trace_collector);
        log!(log::VERBOSE, &format!("Symbolic execution took: {}ms", now.elapsed().as_millis()));

        let rk_ifetch = match shared_state.enum_member("Read_ifetch") {
            Some(rk) => rk,
            None => return Err(NoReadIFetch),
        };

        loop {
            match queue.pop() {
                Ok(Ok((task_id, mut events))) => {
                    let mut events: EvPath<B> = events
                        .drain(..)
                        .rev()
                        .filter(|ev| {
                            (ev.is_memory() && !ev.has_read_kind(rk_ifetch))
                                || ev.is_smt()
                                || ev.is_instr()
                                || ev.is_cycle()
                                || ev.is_write_reg()
                        })
                        .collect();
                    let mut events = simplify::remove_unused(events);
                    for event in events.iter_mut() {
                        simplify::renumber_event(event, task_id as u32, thread_buckets.len() as u32)
                    }

                    thread_buckets[task_id].push(events)
                }
                // Error during execution
                Ok(Err(msg)) => return Err(Execution(msg)),
                // Empty queue
                Err(_) => break,
            }
        }

        let footprints =
            footprint_analysis(num_threads, &thread_buckets, &lets, &regs, &shared_state, &isa_config, cache)
                .map_err(Footprint)?;

        let candidates = Candidates::new(&thread_buckets);
        log!(log::VERBOSE, &format!("There are {} candidate executions", candidates.total()));

        let cqueue = ArrayQueue::new(candidates.total());
        for (i, candidate) in candidates.enumerate() {
            cqueue.push((i, candidate)).unwrap();
        }

        thread::scope(|scope| {
            for _ in 0..num_threads {
                scope.spawn(|_| {
                    while let Ok((i, candidate)) = cqueue.pop() {
                        callback(i, &candidate, &footprints)
                    }
                });
            }
        })
        .unwrap();

        Ok(())
    }
}
