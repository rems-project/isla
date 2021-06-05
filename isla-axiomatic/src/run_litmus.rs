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

use crossbeam::queue::{ArrayQueue, SegQueue};
use crossbeam::thread;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::process::Command;
use std::sync::Arc;
use std::time::Instant;

use isla_cat::cat;
use isla_cat::cat::Cat;

use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::executor;
use isla_lib::executor::{LocalFrame, TaskState};
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::memory::{Memory, Region};
use isla_lib::simplify;
use isla_lib::simplify::{write_events_with_opts, WriteOpts};
use isla_lib::smt::smtlib;
use isla_lib::smt::{checkpoint, Checkpoint, EvPath, Event, Solver, Config, Context};

use crate::axiomatic::model::Model;
use crate::axiomatic::{Candidates, ExecutionInfo, ThreadId};
use crate::footprint_analysis::{footprint_analysis, Footprint, FootprintError};
use crate::litmus::Litmus;
use crate::page_table::{PageTables, S1PageAttrs, S2PageAttrs};
use crate::smt_events::smt_of_candidate;

#[derive(Debug)]
pub enum LitmusRunError<E> {
    NoMain,
    Execution(String),
    Footprint(FootprintError),
    CallbackErrors(Vec<E>),
}

impl<E: Error> fmt::Display for LitmusRunError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use LitmusRunError::*;
        match self {
            NoMain => write!(
                f,
                "There is no `main` function in the specified architecture.\
                 This function is used as the entry point for each thread in a litmus test."
            ),
            Execution(msg) => write!(f, "Error during symbolic execution: {}", msg),
            Footprint(e) => write!(f, "{}", e),
            CallbackErrors(errs) => {
                for e in errs {
                    writeln!(f, "{}", e)?
                }
                Ok(())
            }
        }
    }
}

impl<E: Error> Error for LitmusRunError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

pub struct LitmusRunOpts {
    pub num_threads: usize,
    pub timeout: Option<u64>,
    pub ignore_ifetch: bool,
    pub exhaustive: bool,
    pub armv8_page_tables: bool,
}

pub struct LitmusRunInfo {
    pub candidates: usize,
}

fn setup_armv8_page_tables<B: BV>(
    memory: &mut Memory<B>,
    litmus: &Litmus<B>,
    isa_config: &ISAConfig<B>,
) -> Checkpoint<B> {
    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::<B>::new(&ctx);

    // Create page tables for both stage 1 and stage 2 address translation
    let mut s1_tables = PageTables::new("stage 1", isa_config.page_table_base);
    let mut s2_tables = PageTables::new("stage 2", isa_config.s2_page_table_base);

    let s1_level0 = s1_tables.alloc();
    let s2_level0 = s2_tables.alloc();

    // We map each thread's code into both levels of page tables
    for i in 0..litmus.assembled.len() {
        let addr = isa_config.thread_base + (i as u64 * isa_config.page_size);
        s1_tables.identity_map(s1_level0, addr, S1PageAttrs::code()).unwrap();
        s2_tables.identity_map(s2_level0, addr, S2PageAttrs::code()).unwrap()
    }

    // Map the region where we will install exception handlers if required
    for i in 0..8 {
        s1_tables.identity_map(s1_level0, 0x1000 * i, S1PageAttrs::code()).unwrap();
        s2_tables.identity_map(s2_level0, 0x1000 * i, S2PageAttrs::code()).unwrap()
    }

    // Create an identity mapping for each variable in the litmus test
    for (_, addr) in &litmus.symbolic_addrs {
        s1_tables.identity_map(s1_level0, *addr, S1PageAttrs::default()).unwrap();
        // Allow the hypervisor to mark stage 2 mappings as invalid
        s2_tables.identity_or_invalid_map(s2_level0, *addr, S2PageAttrs::default(), &mut solver).unwrap()
    }

    // Map the stage 2 tables into the stage 2 mapping
    let mut page = isa_config.s2_page_table_base;
    while page < s2_tables.range().end {
        s2_tables.identity_map(s2_level0, page, S2PageAttrs::default());
        page += isa_config.s2_page_size
    }
    
    // Map the stage 1 tables into the stage 1 and stage 2 mappings
    page = isa_config.page_table_base;
    while page < s1_tables.range().end {
        s1_tables.identity_map(s1_level0, page, S1PageAttrs::default());
        s2_tables.identity_map(s2_level0, page, S2PageAttrs::default());
        page += isa_config.page_size
    }

    memory.add_region(Region::Custom(s1_tables.range(), Box::new(s1_tables.freeze())));
    memory.add_region(Region::Custom(s2_tables.range(), Box::new(s2_tables.freeze())));

    checkpoint(&mut solver)
}

#[allow(clippy::too_many_arguments)]
pub fn litmus_per_candidate<B, P, F, E>(
    opts: &LitmusRunOpts,
    litmus: &Litmus<B>,
    regs: Bindings<B>,
    mut lets: Bindings<B>,
    shared_state: &SharedState<B>,
    isa_config: &ISAConfig<B>,
    fregs: Bindings<B>,
    flets: Bindings<B>,
    fshared_state: &SharedState<B>,
    footprint_config: &ISAConfig<B>,
    cache: P,
    callback: &F,
) -> Result<LitmusRunInfo, LitmusRunError<E>>
where
    B: BV,
    P: AsRef<Path>,
    F: Sync + Send + Fn(ThreadId, &[&[Event<B>]], &HashMap<B, Footprint>, &Memory<B>) -> Result<(), E>,
    E: Send,
{
    use LitmusRunError::*;

    let mut memory = Memory::new();

    for region in &litmus.self_modify_regions {
        memory.add_region(region.clone())
    }

    memory.add_concrete_region(isa_config.thread_base..isa_config.thread_top, HashMap::new());
    // FIXME: Insert a blank exception vector table for AArch64
    memory.add_concrete_region(0x0_u64..0x8000_u64, HashMap::new());

    let memory_checkpoint = if opts.armv8_page_tables {
        setup_armv8_page_tables(&mut memory, litmus, isa_config)
    } else {
        Checkpoint::new()
    };

    let mut current_base = isa_config.thread_base;
    for thread in litmus.assembled.iter() {
        log!(log::VERBOSE, &format!("Thread {} @ 0x{:x}", thread.name, current_base));
        for (i, byte) in thread.code.iter().enumerate() {
            memory.write_byte(current_base + i as u64, *byte)
        }
        current_base += isa_config.thread_stride
    }
    for (addr, bytes) in litmus.sections.iter() {
        log!(log::VERBOSE, &format!("Section 0x{:x}", addr));
        for (i, byte) in bytes.iter().enumerate() {
            memory.write_byte(addr + i as u64, *byte)
        }
    }
    memory.log();

    let function_id = match shared_state.symtab.get("zmain") {
        Some(id) => id,
        None => return Err(NoMain),
    };

    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task_states: Vec<_> =
        litmus.assembled.iter().map(|thread| TaskState::with_reset_registers(thread.reset.clone())).collect();
    let tasks: Vec<_> = litmus
        .assembled
        .iter()
        .enumerate()
        .map(|(i, thread)| {
            let address = isa_config.thread_base + (isa_config.thread_stride * i as u64);
            lets.insert(ELF_ENTRY, UVal::Init(Val::I128(address as i128)));
            let mut regs = regs.clone();
            for (reg, value) in &thread.inits {
                regs.insert(*reg, UVal::Init(Val::Bits(B::from_u64(*value))));
            }
            LocalFrame::new(function_id, args, Some(&[Val::Unit]), instrs)
                .add_lets(&lets)
                .add_regs(&regs)
                .set_memory(memory.clone())
                .task_with_checkpoint(i, &task_states[i], memory_checkpoint.clone())
        })
        .collect();

    let mut thread_buckets: Vec<Vec<EvPath<B>>> = vec![Vec::new(); tasks.len()];
    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(
        opts.num_threads,
        opts.timeout,
        tasks,
        &shared_state,
        queue.clone(),
        &executor::trace_collector,
    );
    log!(log::VERBOSE, &format!("Symbolic execution took: {}ms", now.elapsed().as_millis()));

    let rk_ifetch = shared_state.enum_member(isa_config.ifetch_read_kind).expect("Invalid ifetch read kind");

    loop {
        match queue.pop() {
            Ok(Ok((task_id, mut events))) => {
                let mut events: EvPath<B> = events
                    .drain(..)
                    .rev()
                    .filter(|ev| {
                        (ev.is_memory() && !(opts.ignore_ifetch && ev.has_read_kind(rk_ifetch)))
                            || ev.is_smt()
                            || ev.is_instr()
                            || ev.is_cycle()
                            || ev.is_write_reg()
                    })
                    .collect();
                simplify::remove_unused(&mut events);
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

    let footprints = footprint_analysis(
        opts.num_threads,
        &thread_buckets,
        &flets,
        &fregs,
        &fshared_state,
        &footprint_config,
        Some(cache.as_ref()),
    )
    .map_err(Footprint)?;

    let candidates = Candidates::new(&thread_buckets);
    let num_candidates = candidates.total();
    log!(log::VERBOSE, &format!("There are {} candidate executions", num_candidates));

    let cqueue = ArrayQueue::new(num_candidates);
    for (i, candidate) in candidates.enumerate() {
        cqueue.push((i, candidate)).unwrap();
    }

    let err_queue = ArrayQueue::new(num_candidates);

    thread::scope(|scope| {
        for _ in 0..opts.num_threads {
            scope.spawn(|_| {
                while let Ok((i, candidate)) = cqueue.pop() {
                    if let Err(err) = callback(i, &candidate, &footprints, &memory) {
                        err_queue.push(err).unwrap()
                    }
                }
            });
        }
    })
    .unwrap();

    let mut callback_errors = Vec::new();
    while let Ok(err) = err_queue.pop() {
        callback_errors.push(err)
    }

    if callback_errors.is_empty() {
        Ok(LitmusRunInfo { candidates: num_candidates })
    } else {
        Err(CallbackErrors(callback_errors))
    }
}

#[derive(Debug)]
pub enum CallbackError<E> {
    Internal(String),
    User(E),
}

fn internal_err<I: Error, E>(internal: I) -> CallbackError<E> {
    CallbackError::Internal(format!("{}", internal))
}

fn internal_err_boxed<E>(internal: Box<dyn Error>) -> CallbackError<E> {
    CallbackError::Internal(format!("{}", internal))
}

impl<E: Error> fmt::Display for CallbackError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use CallbackError::*;
        match self {
            Internal(msg) => write!(f, "{}", msg),
            User(err) => write!(f, "{}", err),
        }
    }
}

impl<E: Error> Error for CallbackError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// This function runs a callback on the output of the SMT solver for
/// each candidate execution combined with a cat model.
#[allow(clippy::too_many_arguments)]
pub fn smt_output_per_candidate<B, P, F, E>(
    uid: &str,
    opts: &LitmusRunOpts,
    litmus: &Litmus<B>,
    cat: &Cat<cat::Ty>,
    regs: Bindings<B>,
    lets: Bindings<B>,
    shared_state: &SharedState<B>,
    isa_config: &ISAConfig<B>,
    fregs: Bindings<B>,
    flets: Bindings<B>,
    fshared_state: &SharedState<B>,
    footprint_config: &ISAConfig<B>,
    check_sat_using: Option<&str>,
    cache: P,
    callback: &F,
) -> Result<LitmusRunInfo, LitmusRunError<CallbackError<E>>>
where
    B: BV,
    P: AsRef<Path> + Sync,
    F: Sync + Send + Fn(ExecutionInfo<B>, &HashMap<B, Footprint>, &str) -> Result<(), E>,
    E: Send,
{
    litmus_per_candidate(
        opts,
        &litmus,
        regs,
        lets,
        &shared_state,
        &isa_config,
        fregs,
        flets,
        &fshared_state,
        &footprint_config,
        &cache,
        &|tid, candidate, footprints, memory| {
            let mut negate_rf_assertion = "true".to_string();
            let mut first_run = true;
            loop {
                let now = Instant::now();

                let exec = ExecutionInfo::from(&candidate, &shared_state, isa_config).map_err(internal_err)?;

                let mut path = cache.as_ref().to_owned();
                path.push(format!("isla_candidate_{}_{}_{}.smt2", uid, std::process::id(), tid));

                // Create the SMT file with all the thread traces and the cat model.
                {
                    let mut fd = File::create(&path).unwrap();
                    writeln!(&mut fd, "(set-option :produce-models true)").map_err(internal_err)?;

                    let mut enums = HashSet::new();
                    for thread in candidate {
                        for event in *thread {
                            if let Event::Smt(smtlib::Def::DefineEnum(_, size), _) = event {
                                enums.insert(*size);
                            }
                        }
                    }

                    for size in enums {
                        write!(&mut fd, "(declare-datatypes ((Enum{} 0)) ((", size).map_err(internal_err)?;
                        for i in 0..size {
                            write!(&mut fd, "(e{}_{})", size, i).map_err(internal_err)?
                        }
                        writeln!(&mut fd, ")))").map_err(internal_err)?
                    }

                    for thread in candidate {
                        write_events_with_opts(&mut fd, thread, &shared_state.symtab, &WriteOpts::smtlib())
                            .map_err(internal_err)?;
                    }

                    // We want to make sure we can extract the values read and written by the model if they are
                    // symbolic. Therefore we declare new variables that are guaranteed to appear in the generated model.
                    for (name, event) in exec.events.iter().map(|ev| (&ev.name, ev.base)) {
                        match event {
                            Event::ReadMem { value, address, bytes, .. }
                            | Event::WriteMem { data: value, address, bytes, .. } => {
                                if let Val::Symbolic(v) = value {
                                    writeln!(&mut fd, "(declare-const |{}:value| (_ BitVec {}))", name, bytes * 8)
                                        .map_err(internal_err)?;
                                    writeln!(&mut fd, "(assert (= |{}:value| v{}))", name, v).map_err(internal_err)?;
                                }
                                if let Val::Symbolic(v) = address {
                                    // TODO handle non 64-bit physical addresses
                                    writeln!(&mut fd, "(declare-const |{}:address| (_ BitVec 64))", name)
                                        .map_err(internal_err)?;
                                    writeln!(&mut fd, "(assert (= |{}:address| v{}))", name, v)
                                        .map_err(internal_err)?;
                                }
                            }
                            _ => (),
                        }
                    }

                    smt_of_candidate(
                        &mut fd,
                        &exec,
                        &litmus,
                        opts.ignore_ifetch,
                        footprints,
                        memory,
                        &shared_state,
                        &isa_config,
                    )
                    .map_err(internal_err_boxed)?;
                    isla_cat::smt::compile_cat(&mut fd, &cat).map_err(internal_err_boxed)?;

                    writeln!(&mut fd, "(assert (and {}))", negate_rf_assertion).map_err(internal_err)?;
                    if let Some(tactic) = check_sat_using {
                        writeln!(&mut fd, "(check-sat-using {})", tactic).map_err(internal_err)?
                    } else {
                        writeln!(&mut fd, "(check-sat)").map_err(internal_err)?
                    }
                    writeln!(&mut fd, "(get-model)").map_err(internal_err)?;
                }

                let mut z3_command = Command::new("z3");
                if let Some(secs) = opts.timeout {
                    z3_command.arg(format!("-T:{}", secs));
                }
                z3_command.arg(&path);

                let z3 = z3_command.output().map_err(internal_err)?;

                let z3_output = std::str::from_utf8(&z3.stdout).map_err(internal_err)?;

                log!(log::VERBOSE, &format!("solver took: {}ms", now.elapsed().as_millis()));

                //if std::fs::remove_file(&path).is_err() {}

                if !opts.exhaustive {
                    break callback(exec, footprints, &z3_output).map_err(CallbackError::User);
                } else if z3_output.starts_with("sat") {
                    let mut event_names: Vec<&str> = exec.events.iter().map(|ev| ev.name.as_ref()).collect();
                    event_names.push("IW");
                    let model_buf = &z3_output[3..];
                    let mut model = Model::<B>::parse(&event_names, model_buf).ok_or_else(|| {
                        CallbackError::Internal("Could not parse SMT output in exhaustive mode".to_string())
                    })?;

                    let rf = model.interpret_rel("rf", &event_names).map_err(|_| {
                        CallbackError::Internal("Could not interpret rf relation in exhaustive mode".to_string())
                    })?;

                    negate_rf_assertion += &format!(
                        " (or {})",
                        rf.iter().fold("false".to_string(), |res, (ev1, ev2)| {
                            res + &format!(" (not (rf {} {}))", ev1, ev2)
                        })
                    );

                    match callback(exec, footprints, &z3_output) {
                        Err(e) => break Err(CallbackError::User(e)),
                        Ok(()) => (),
                    }

                    first_run = false;
                } else if z3_output.starts_with("unsat") && !first_run {
                    break Ok(());
                } else {
                    break callback(exec, footprints, &z3_output).map_err(CallbackError::User);
                }
            }
        },
    )
}
