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

//! This module implements footprint analysis for the concurrency tool
//!
//! The axiomatic memory model requires deriving (syntactic) address,
//! data, and control dependencies. As such, we need to know what
//! registers could be touched by each instruction based purely on its
//! concrate opcode. For this we analyse all the traces from a litmus
//! test run, and use symbolic execution on each opcode again.

use crossbeam::queue::SegQueue;
use serde::{Deserialize, Serialize};

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::io;
use std::io::Write;
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use isla_lib::cache::{Cacheable, Cachekey};
use isla_lib::concrete::Sbits;
use isla_lib::config::ISAConfig;
use isla_lib::executor;
use isla_lib::executor::LocalFrame;
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::simplify::{EventReferences, Taints};
use isla_lib::smt::{Accessor, Event};
use isla_lib::zencode;

#[derive(Debug, Serialize, Deserialize)]
pub struct Footprint {
    /// Tracks which (symbolic) registers / memory reads can feed into
    /// a memory write within an instruction
    write_data_taints: (Taints, bool),
    /// Tracks with (symbolic) registers / memory reads can feed into
    /// a memory operator (read/write) address within an instruction
    mem_addr_taints: (Taints, bool),
    /// The set of register reads (with subfield granularity)
    register_reads: HashSet<(u32, Vec<Accessor>)>,
    /// The set of register writes (also with subfield granularity)
    register_writes: HashSet<(u32, Vec<Accessor>)>,
    /// A store is any instruction with a WriteMem event
    is_store: bool,
    /// A load is any instruction with a ReadMem event
    is_load: bool,
}

pub struct Footprintkey {
    opcode: Sbits,
}

impl Cachekey for Footprintkey {
    fn key(&self) -> String {
        format!("opcode{}_{}", self.opcode.length, self.opcode.bits)
    }
}

impl Cacheable for Footprint {
    type Key = Footprintkey;
}

impl Footprint {
    pub fn new() -> Self {
        Footprint {
            write_data_taints: (HashSet::new(), false),
            mem_addr_taints: (HashSet::new(), false),
            register_reads: HashSet::new(),
            register_writes: HashSet::new(),
            is_store: false,
            is_load: false,
        }
    }

    fn pretty(&self, buf: &mut dyn Write, symtab: &Symtab) -> Result<(), Box<dyn Error>> {
        write!(buf, "Footprint:\n  Memory write data:")?;
        for (reg, accessor) in &self.write_data_taints.0 {
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
        write!(buf, "\n  Is store: {}", self.is_store)?;
        write!(buf, "\n  Is load: {}", self.is_load)?;
        writeln!(buf)?;
        Ok(())
    }
}

/// Returns true if there exists an RR or RW address dependency from `instrs[from]` to `instrs[to]`.
///
/// # Panics
///
/// Panics if either `from` or `to` are out-of-bounds in `instrs`, or
/// if an instruction does not have a footprint.
pub fn addr_dep(from: usize, to: usize, instrs: &[Sbits], footprints: &HashMap<Sbits, Footprint>) -> bool {
    // `to` must be po-order-later than `from` for the dependency to exist.
    if from >= to {
        return false;
    }

    // The set of registers that could be (syntactically) touched by
    // the first instruction before reaching the second.
    let mut touched = footprints.get(&instrs[from]).unwrap().register_writes.clone();
    for i in (from + 1)..to {
        let mut new_touched = Vec::new();
        for rreg in &touched {
            if footprints.get(&instrs[i]).unwrap().register_reads.contains(rreg) {
                for wreg in &footprints.get(&instrs[i]).unwrap().register_writes {
                    new_touched.push(wreg.clone());
                }
            }
        }
        new_touched.drain(..).for_each(|wreg| {
            touched.insert(wreg);
        })
    }

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

// TODO:
pub fn data_dep(from: usize, to: usize, instrs: &[Sbits], footprints: &HashMap<Sbits, Footprint>) -> bool {
    false
}

pub fn ctrl_dep(from: usize, to: usize, instrs: &[Sbits], footprints: &HashMap<Sbits, Footprint>) -> bool {
    false
}

#[derive(Debug)]
pub enum FootprintError {
    NoIslaFootprintFn,
    SymbolicInstruction,
    ExecutionError(String),
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
            ExecutionError(msg) => write!(f, "{}", msg),
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
pub fn footprint_analysis<'ir, P>(
    num_threads: usize,
    thread_buckets: &[Vec<Vec<Event>>],
    lets: &Bindings<'ir>,
    regs: &Bindings<'ir>,
    shared_state: &SharedState,
    isa_config: &ISAConfig,
    cache_dir: P,
) -> Result<HashMap<Sbits, Footprint>, FootprintError>
where
    P: AsRef<Path>,
{
    use FootprintError::*;
    let mut concrete_opcodes: HashSet<Sbits> = HashSet::new();
    let mut footprints = HashMap::new();

    for thread in thread_buckets {
        for path in thread {
            for event in path {
                match event {
                    Event::Instr(Val::Bits(bv)) => {
                        if let Some(footprint) = Footprint::from_cache(Footprintkey { opcode: *bv }, cache_dir.as_ref())
                        {
                            footprints.insert(*bv, footprint);
                        } else {
                            concrete_opcodes.insert(bv.clone());
                        }
                    }
                    Event::Instr(_) => return Err(SymbolicInstruction),
                    _ => (),
                }
            }
        }
    }

    log!(log::VERBOSE, &format!("Got {} uncached concrete opcodes for footprint analysis", concrete_opcodes.len()));

    let function_id = match shared_state.symtab.get("zisla_footprint") {
        Some(id) => id,
        None => return Err(NoIslaFootprintFn),
    };
    let (args, _, instrs) =
        shared_state.functions.get(&function_id).expect("isla_footprint function not in shared state!");

    let (task_opcodes, tasks): (Vec<Sbits>, Vec<_>) = concrete_opcodes
        .iter()
        .enumerate()
        .map(|(i, opcode)| {
            (
                opcode,
                LocalFrame::new(args, Some(&[Val::Bits(opcode.clone())]), instrs).add_lets(lets).add_regs(regs).task(i),
            )
        })
        .unzip();

    let mut footprint_buckets: Vec<Vec<Vec<Event>>> = vec![Vec::new(); tasks.len()];
    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(num_threads, tasks, &shared_state, queue.clone(), &executor::footprint_collector);
    log!(log::VERBOSE, &format!("Footprint analysis symbolic execution took: {}ms", now.elapsed().as_millis()));

    loop {
        match queue.pop() {
            Ok(Ok((task_id, mut events))) => {
                let events: Vec<Event> = events
                    .drain(..)
                    .rev()
                    // The first cycle is reserved for initialization
                    .skip_while(|ev| !ev.is_cycle())
                    .filter(|ev| ev.is_reg() || ev.is_memory() || ev.is_smt())
                    .collect();
                let events = isla_lib::simplify::remove_unused(events);
                footprint_buckets[task_id].push(events)
            }
            // Error during execution
            Ok(Err(msg)) => return Err(ExecutionError(msg)),
            // Empty queue
            Err(_) => break,
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
            for event in events {
                match event {
                    Event::ReadReg(reg, accessor, _) if !isa_config.ignored_registers.contains(reg) => {
                        footprint.register_reads.insert((*reg, accessor.clone()));
                    }
                    Event::WriteReg(reg, accessor, _) if !isa_config.ignored_registers.contains(reg) => {
                        footprint.register_writes.insert((*reg, accessor.clone()));
                    }
                    Event::ReadMem { address, .. } => {
                        footprint.is_load = true;
                        evrefs.collect_value_taints(
                            address,
                            events,
                            &mut footprint.mem_addr_taints.0,
                            &mut footprint.mem_addr_taints.1,
                        )
                    }
                    Event::WriteMem { address, data, .. } => {
                        footprint.is_store = true;
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
                        )
                    }
                    _ => (),
                }
            }
        }

        {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            footprint.pretty(&mut handle, &shared_state.symtab).unwrap();
        }

        footprint.cache(Footprintkey { opcode }, cache_dir.as_ref());
        footprints.insert(opcode, footprint);
    }

    Ok(footprints)
}
