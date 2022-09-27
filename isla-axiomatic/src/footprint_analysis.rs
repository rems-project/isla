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

//! This module implements footprint analysis for the concurrency tool
//!
//! The axiomatic memory model requires deriving (syntactic) address,
//! data, and control dependencies. As such, we need to know what
//! registers could be touched by each instruction based purely on its
//! concrete opcode. For this we analyse all the traces from a litmus
//! test run, and use symbolic execution on each opcode again.

use crossbeam::queue::SegQueue;
use serde::{Deserialize, Serialize};

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::io::Write;
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use isla_lib::bitvector::BV;
use isla_lib::cache::{Cacheable, Cachekey};
use isla_lib::config::ISAConfig;
use isla_lib::executor;
use isla_lib::executor::{LocalFrame, TaskState, TraceError};
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::register::RegisterBindings;
use isla_lib::simplify::{EventReferences, Taints};
use isla_lib::smt::{Accessor, EvPath, Event, Sym};
use isla_lib::zencode;

#[derive(Debug, Serialize, Deserialize)]
pub struct Footprint {
    /// Tracks which (symbolic) registers / memory reads can feed into
    /// a memory write within an instruction
    write_data_taints: (Taints, bool),
    /// Tracks with (symbolic) registers / memory reads can feed into
    /// a memory operator (read/write) address within an instruction
    mem_addr_taints: (Taints, bool),
    /// Tracks which (symbolic) registers / memory reads can feed into
    /// the address of a branch
    branch_addr_taints: (Taints, bool),
    /// The set of register reads (with subfield granularity)
    register_reads: HashSet<(Name, Vec<Accessor>)>,
    /// The set of register writes (also with subfield granularity)
    register_writes: HashSet<(Name, Vec<Accessor>)>,
    /// The set of register writes where the value was tainted by a memory read
    register_writes_tainted: HashSet<(Name, Vec<Accessor>)>,
    /// All register read-write pairs to the following registers are
    /// ignored for tracking dependencies within an instruction. If
    /// the first element of the tuple is None then all writes are
    /// ignored
    register_writes_ignored: HashSet<(Option<Name>, Name)>,
    /// A store is any instruction with a WriteMem event
    is_store: bool,
    /// A load is any instruction with a ReadMem event
    is_load: bool,
    /// A branch is any instruction with a Branch event
    is_branch: bool,
    /// An exclusive is any event with an exclusive read or write kind.
    is_exclusive: bool,
}

pub struct Footprintkey {
    opcode: String,
}

impl Cachekey for Footprintkey {
    fn key(&self) -> String {
        format!("opcode_{}", self.opcode)
    }
}

impl Cacheable for Footprint {
    type Key = Footprintkey;
}

impl Footprint {
    fn new() -> Self {
        Footprint {
            write_data_taints: (HashSet::new(), false),
            mem_addr_taints: (HashSet::new(), false),
            branch_addr_taints: (HashSet::new(), false),
            register_reads: HashSet::new(),
            register_writes: HashSet::new(),
            register_writes_tainted: HashSet::new(),
            register_writes_ignored: HashSet::new(),
            is_store: false,
            is_load: false,
            is_branch: false,
            is_exclusive: false,
        }
    }

    /// This just prints the footprint information in a human-readable
    /// form for debugging.
    pub fn pretty(&self, buf: &mut dyn Write, symtab: &Symtab) -> Result<(), Box<dyn Error>> {
        write!(buf, "Footprint:\n  Memory write:")?;
        for (reg, accessor) in &self.write_data_taints.0 {
            write!(buf, " {}", zencode::decode(symtab.to_str(*reg)))?;
            for component in accessor {
                component.pretty(buf, symtab)?
            }
        }
        write!(buf, "\n  Memory read:")?;
        for (reg, accessor) in &self.register_writes_tainted {
            write!(buf, " {}", zencode::decode(symtab.to_str(*reg)))?;
            for component in accessor {
                component.pretty(buf, symtab)?
            }
        }
        write!(buf, "\n  Memory address:")?;
        for (reg, accessor) in &self.mem_addr_taints.0 {
            write!(buf, " {}", zencode::decode(symtab.to_str(*reg)))?;
            for component in accessor {
                component.pretty(buf, symtab)?
            }
        }
        write!(buf, "\n  Branch address:")?;
        for (reg, accessor) in &self.branch_addr_taints.0 {
            write!(buf, " {}", zencode::decode(symtab.to_str(*reg)))?;
            for component in accessor {
                component.pretty(buf, symtab)?
            }
        }
        write!(buf, "\n  Register reads:")?;
        for (reg, accessor) in &self.register_reads {
            write!(buf, " {}", zencode::decode(symtab.to_str(*reg)))?;
            for component in accessor {
                component.pretty(buf, symtab)?
            }
        }
        write!(buf, "\n  Register writes:")?;
        for (reg, accessor) in &self.register_writes {
            write!(buf, " {}", zencode::decode(symtab.to_str(*reg)))?;
            for component in accessor {
                component.pretty(buf, symtab)?
            }
        }
        write!(buf, "\n  Register writes (ignore):")?;
        for (from_reg, to_reg) in &self.register_writes_ignored {
            if let Some(from_reg) = from_reg {
                write!(
                    buf,
                    " {}->{}",
                    zencode::decode(symtab.to_str(*from_reg)),
                    zencode::decode(symtab.to_str(*to_reg))
                )?
            } else {
                write!(buf, " {}", zencode::decode(symtab.to_str(*to_reg)))?
            }
        }
        write!(buf, "\n  Is store: {}", self.is_store)?;
        write!(buf, "\n  Is load: {}", self.is_load)?;
        write!(buf, "\n  Is exclusive: {}", self.is_exclusive)?;
        write!(buf, "\n  Is branch: {}", self.is_branch)?;
        writeln!(buf)?;
        Ok(())
    }
}

// There is an rmw dependency from `from` to `to` if `from` is a
// load-exclusive and `to` is a store-exclusive and there are no
// intervening exclusives.
#[allow(clippy::needless_range_loop)]
pub fn rmw_dep<B: BV>(from: usize, to: usize, instrs: &[B], footprints: &HashMap<B, Footprint>) -> bool {
    if from > to {
        return false;
    }

    let from_footprint = footprints.get(&instrs[from]).unwrap();
    if !(from_footprint.is_exclusive && from_footprint.is_load) {
        return false;
    }

    for i in (from + 1)..to {
        if footprints.get(&instrs[i]).unwrap().is_exclusive {
            return false;
        }
    }

    let to_footprint = footprints.get(&instrs[to]).unwrap();
    to_footprint.is_exclusive && to_footprint.is_store
}

/// The set of registers that could be (syntactically) touched by the
/// first instruction before reaching the second.
#[allow(clippy::needless_range_loop)]
fn touched_by<B: BV>(
    from: usize,
    to: usize,
    instrs: &[B],
    footprints: &HashMap<B, Footprint>,
) -> HashSet<(Name, Vec<Accessor>)> {
    let mut touched = footprints.get(&instrs[from]).unwrap().register_writes_tainted.clone();
    let mut new_touched = HashSet::new();
    for i in (from + 1)..to {
        let footprint = footprints.get(&instrs[i]).unwrap();

        for rreg in &touched {
            if footprint.register_reads.contains(rreg) {
                for wreg in &footprint.register_writes {
                    if footprint.register_writes_ignored.contains(&(None, wreg.0)) {
                        continue;
                    }
                    if footprint.register_writes_ignored.contains(&(Some(rreg.0), wreg.0)) {
                        continue;
                    }
                    new_touched.insert(wreg.clone());
                }
            }
        }

        if new_touched.is_empty() {
            for wreg in &footprint.register_writes {
                touched.remove(wreg);
            }
        } else {
            new_touched.drain().for_each(|wreg| {
                touched.insert(wreg);
            })
        }
    }
    touched
}

/// Returns true if there exists an RR or RW address dependency from `instrs[from]` to `instrs[to]`.
///
/// # Panics
///
/// Panics if either `from` or `to` are out-of-bounds in `instrs`, or
/// if an instruction does not have a footprint.
pub fn addr_dep<B: BV>(from: usize, to: usize, instrs: &[B], footprints: &HashMap<B, Footprint>) -> bool {
    // `to` must be po-order-later than `from` for the dependency to exist.
    if from >= to {
        return false;
    }

    let touched = touched_by(from, to, instrs, footprints);

    // If any of the registers transitively touched by the first
    // instruction's register writes can feed into a memory address
    // used by the last we have an address dependency.
    for reg in &footprints.get(&instrs[to]).unwrap().mem_addr_taints.0 {
        if touched.contains(reg) {
            return true;
        }
    }
    false
}

/// Returns true if there exists an RW data dependency from `instrs[from]` to `instrs[to]`.
///
/// # Panics
///
/// See `addr_dep`
pub fn data_dep<B: BV>(from: usize, to: usize, instrs: &[B], footprints: &HashMap<B, Footprint>) -> bool {
    if from >= to {
        return false;
    }

    let touched = touched_by(from, to, instrs, footprints);

    for reg in &footprints.get(&instrs[to]).unwrap().write_data_taints.0 {
        if touched.contains(reg) {
            return true;
        }
    }
    false
}

/// Returns true if there exists an RW or RR control dependency from `instrs[from]` to `instrs[to]`.
///
/// # Panics
///
/// See `addr_dep`
#[allow(clippy::needless_range_loop)]
pub fn ctrl_dep<B: BV>(from: usize, to: usize, instrs: &[B], footprints: &HashMap<B, Footprint>) -> bool {
    // `to` must be a program-order later load or store
    let to_footprint = footprints.get(&instrs[from]).unwrap();
    if !(to_footprint.is_load || to_footprint.is_store) || (from >= to) {
        return false;
    }

    let mut touched = footprints.get(&instrs[from]).unwrap().register_writes_tainted.clone();
    let mut new_touched = Vec::new();

    for i in (from + 1)..to {
        let footprint = footprints.get(&instrs[i]).unwrap();

        if footprint.is_branch {
            for reg in &footprint.branch_addr_taints.0 {
                if touched.contains(reg) {
                    return true;
                }
            }
        }

        for rreg in &touched {
            if footprint.register_reads.contains(rreg) {
                for wreg in &footprint.register_writes {
                    if footprint.register_writes_ignored.contains(&(None, wreg.0)) {
                        continue;
                    }
                    if footprint.register_writes_ignored.contains(&(Some(rreg.0), wreg.0)) {
                        continue;
                    }
                    new_touched.push(wreg.clone());
                }
            }
        }
        new_touched.drain(..).for_each(|wreg| {
            touched.insert(wreg);
        })
    }
    false
}

#[derive(Debug)]
pub enum FootprintError {
    NoIslaFootprintFn,
    SymbolicInstruction,
    Trace(TraceError),
}

impl fmt::Display for FootprintError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use FootprintError::*;
        match self {
            NoIslaFootprintFn => write!(
                f,
                "Footprint analysis failed. To calculate the syntactic\n\
                 register footprint, isla expects a sail function\n\
                 `isla_footprint' to be available in the model, which\n\
                 can be used to decode and execute an instruction"
            ),
            SymbolicInstruction => write!(f, "Instruction opcode found during footprint analysis was symbolic"),
            Trace(msg) => write!(f, "{}", msg),
        }
    }
}

impl Error for FootprintError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// # Arguments
///
/// * `num_threads` - How many threads to use for analysing footprints
/// * `thread_buckets` - A vector of paths (event vectors) for each thread in the litmus test
/// * `lets` - The initial state of all top-level letbindings in the Sail specification
/// * `regs` - The initial register state
/// * `shared_state` - The state shared between all symbolic execution runs
/// * `isa_config` - The architecture specific configuration information
/// * `cache_dir` - A directory to cache footprint results
pub fn footprint_analysis<'ir, B>(
    num_threads: usize,
    thread_buckets: &[Vec<EvPath<B>>],
    lets: &Bindings<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    shared_state: &SharedState<B>,
    isa_config: &ISAConfig<B>,
    cache: Option<&Path>,
) -> Result<HashMap<B, Footprint>, FootprintError>
where
    B: BV,
{
    let mut concrete_opcodes: HashSet<B> = HashSet::new();
    let mut footprints = HashMap::new();

    for thread in thread_buckets {
        for path in thread {
            for event in path {
                match event {
                    Event::Instr(Val::Bits(bv)) => {
                        if let Some(cache_dir) = &cache {
                            if let Some(footprint) =
                                Footprint::from_cache(Footprintkey { opcode: bv.to_string() }, cache_dir)
                            {
                                footprints.insert(*bv, footprint);
                            } else {
                                concrete_opcodes.insert(*bv);
                            }
                        } else {
                            concrete_opcodes.insert(*bv);
                        }
                    }
                    Event::Instr(_) => return Err(FootprintError::SymbolicInstruction),
                    _ => (),
                }
            }
        }
    }

    log!(log::VERBOSE, &format!("Got {} uncached concrete opcodes for footprint analysis", concrete_opcodes.len()));

    let function_id = match shared_state.symtab.get("zisla_footprint") {
        Some(id) => id,
        None => return Err(FootprintError::NoIslaFootprintFn),
    };
    let (args, ret_ty, instrs) =
        shared_state.functions.get(&function_id).expect("isla_footprint function not in shared state!");

    let task_state = TaskState::new();
    let (task_opcodes, tasks): (Vec<B>, Vec<_>) = concrete_opcodes
        .iter()
        .enumerate()
        .map(|(i, opcode)| {
            (
                opcode,
                LocalFrame::new(function_id, args, ret_ty, Some(&[Val::Bits(*opcode)]), instrs)
                    .add_lets(lets)
                    .add_regs(regs)
                    .task(i, &task_state),
            )
        })
        .unzip();

    let mut footprint_buckets: Vec<Vec<EvPath<B>>> = vec![Vec::new(); tasks.len()];
    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(num_threads, None, tasks, shared_state, queue.clone(), &executor::footprint_collector);
    log!(log::VERBOSE, &format!("Footprint analysis symbolic execution took: {}ms", now.elapsed().as_millis()));

    loop {
        match queue.pop() {
            Some(Ok((task_id, mut events))) => {
                let mut events: Vec<Event<B>> = events
                    .drain(..)
                    .rev()
                    // The first cycle is reserved for initialization
                    .skip_while(|ev| !ev.is_cycle())
                    .filter(|ev| {
                        ev.is_reg() || ev.is_memory_read_or_write() || ev.is_branch() || ev.is_smt() || ev.is_fork()
                    })
                    .collect();
                isla_lib::simplify::remove_unused(&mut events);

                footprint_buckets[task_id].push(events)
            }
            // Error during execution
            Some(Err(err)) => return Err(FootprintError::Trace(err)),
            // Empty queue
            None => break,
        }
    }

    let num_footprints: usize = footprint_buckets.iter().map(|instr_paths| instr_paths.len()).sum();
    log!(log::VERBOSE, &format!("There are {} footprints", num_footprints));

    for (i, paths) in footprint_buckets.iter().enumerate() {
        let opcode = task_opcodes[i];
        log!(log::VERBOSE, &format!("{:?}", opcode));

        let mut footprint = Footprint::new();

        for events in paths {
            let evrefs = EventReferences::from_events(events);
            let mut forks: Vec<Sym> = Vec::new();
            for event in events {
                match event {
                    Event::Fork(_, v, _, _) => forks.push(*v),
                    Event::ReadReg(reg, accessor, _) if !isa_config.ignored_registers.contains(reg) => {
                        footprint.register_reads.insert((*reg, accessor.clone()));
                    }
                    Event::WriteReg(reg, accessor, data) if !isa_config.ignored_registers.contains(reg) => {
                        footprint.register_writes.insert((*reg, accessor.clone()));
                        // If the data written to the register is tainted by a value read
                        // from memory record this fact.
                        if evrefs.value_taints(data, events).1 {
                            footprint.register_writes_tainted.insert((*reg, accessor.clone()));
                        }
                    }
                    Event::MarkReg { regs, mark } => {
                        if mark == "ignore_write" && regs.len() == 1 {
                            footprint.register_writes_ignored.insert((None, regs[0]));
                        }
                        if mark == "ignore_edge" && regs.len() == 2 {
                            footprint.register_writes_ignored.insert((Some(regs[0]), regs[1]));
                        }
                    }
                    Event::ReadMem { address, .. } => {
                        footprint.is_load = true;
                        if event.is_exclusive() {
                            footprint.is_exclusive = true;
                        }
                        evrefs.collect_value_taints(
                            address,
                            events,
                            &mut footprint.mem_addr_taints.0,
                            &mut footprint.mem_addr_taints.1,
                        )
                    }
                    Event::WriteMem { address, data, .. } => {
                        footprint.is_store = true;
                        if event.is_exclusive() {
                            footprint.is_exclusive = true;
                        }
                        evrefs.collect_value_taints(
                            address,
                            events,
                            &mut footprint.mem_addr_taints.0,
                            &mut footprint.mem_addr_taints.1,
                        );
                        evrefs.collect_value_taints(
                            data,
                            events,
                            &mut footprint.write_data_taints.0,
                            &mut footprint.write_data_taints.1,
                        );
                    }
                    Event::Branch { address } => {
                        footprint.is_branch = true;
                        evrefs.collect_value_taints(
                            address,
                            events,
                            &mut footprint.branch_addr_taints.0,
                            &mut footprint.branch_addr_taints.1,
                        );
                        for v in &forks {
                            evrefs.collect_taints(
                                *v,
                                events,
                                &mut footprint.branch_addr_taints.0,
                                &mut footprint.branch_addr_taints.1,
                            )
                        }
                    }
                    _ => (),
                }
            }
        }

        if let Some(cache_dir) = &cache {
            footprint.cache(Footprintkey { opcode: opcode.to_string() }, cache_dir);
        }
        footprints.insert(opcode, footprint);
    }

    Ok(footprints)
}
