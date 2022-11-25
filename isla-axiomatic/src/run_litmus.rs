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
use isla_lib::init::InitArchWithConfig;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::process::Command;
use std::sync::Arc;
use std::time::Instant;

use isla_lib::bitvector::BV;
use isla_lib::error::IslaError;
use isla_lib::executor;
use isla_lib::executor::{LocalFrame, TaskState, TraceError};
use isla_lib::ir::*;
use isla_lib::memory::Memory;
use isla_lib::simplify;
use isla_lib::simplify::{write_events_with_opts, WriteOpts};
use isla_lib::smt::smtlib;
use isla_lib::smt::{checkpoint, Checkpoint, Config, Context, EvPath, Event, Solver};
use isla_lib::source_loc::SourceLoc;
use isla_lib::{if_logging, log};

use isla_mml::memory_model;
use isla_mml::smt::{SexpArena, SexpId, write_sexps};
use isla_mml::accessor::generate_accessor_function;

use crate::axiomatic::model::Model;
use crate::axiomatic::{Candidates, ExecutionInfo, ThreadId};
use crate::footprint_analysis::{footprint_analysis, Footprint, FootprintError};
use crate::graph::GraphOpts;
use crate::litmus::exp::{partial_eval, reset_eval, Exp, Partial};
use crate::litmus::{Litmus, Thread};
use crate::page_table::setup::{armv8_litmus_page_tables, PageTableSetup, SetupError};
use crate::smt_events::smt_of_candidate;

#[derive(Debug)]
pub enum LitmusRunError<E> {
    NoMain,
    Trace(TraceError),
    Footprint(FootprintError),
    PageTableSetup(SetupError),
    Callback(Vec<E>),
}

impl<E: IslaError> IslaError for LitmusRunError<E> {
    fn source_loc(&self) -> SourceLoc {
        match self {
            LitmusRunError::Trace(err) => err.source_loc(),
            _ => SourceLoc::unknown(),
        }
    }
}

impl<E: fmt::Display> fmt::Display for LitmusRunError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use LitmusRunError::*;
        match self {
            NoMain => write!(
                f,
                "There is no `main` function in the specified architecture.\
                 This function is used as the entry point for each thread in a litmus test."
            ),
            Trace(err) => write!(f, "Error during symbolic execution: {}", err),
            Footprint(err) => write!(f, "{}", err),
            PageTableSetup(err) => write!(f, "Error during page table setup: {}", err),
            Callback(errs) => {
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
    pub memory: Option<u64>,
    pub ignore_ifetch: bool,
    pub exhaustive: bool,
    pub armv8_page_tables: bool,
    pub merge_translations: Option<bool>,
    pub remove_uninteresting_translates: Option<bool>,
}

pub struct LitmusRunInfo {
    pub candidates: usize,
}

/// This is the result of the setup of a litmus test that can then be used either to run
/// a test directly in isla, or be exported for a test to be run by another tool.
pub struct LitmusSetup<B> {
    /// The set of traces for each thread.
    pub threads: Vec<Vec<EvPath<B>>>,
    /// The final assertion of the test, simplified with concrete addresses
    pub final_assertion: Exp<u64>,
    /// The initial memory of the test
    pub memory: Memory<B>,
    /// The page table setup of the test
    pub page_table_setup: PageTableSetup<B>,
}

/// Run each thread in a litmus test symbolically, and returns a vector of
/// traces for each litmus threads and the final assertion
pub fn run_litmus_setup<B, F, E>(
    opts: &LitmusRunOpts,
    litmus: &Litmus<B>,
    arch: &InitArchWithConfig<B>,
    event_filter: F,
) -> Result<LitmusSetup<B>, LitmusRunError<E>>
where
    B: BV,
    E: Send + std::fmt::Debug,
    F: Fn(&Event<B>) -> bool,
{
    let isa_config = arch.isa_config;
    let shared_state = arch.shared_state;
    let mut memory = Memory::new();

    for region in &litmus.self_modify_regions {
        memory.add_region(region.clone())
    }

    memory.add_concrete_region(isa_config.thread_base..isa_config.thread_top, HashMap::new());
 
    let page_table_setup = if opts.armv8_page_tables {
        armv8_litmus_page_tables(&mut memory, litmus, isa_config).map_err(LitmusRunError::PageTableSetup)?
    } else {
        PageTableSetup {
            memory_checkpoint: Checkpoint::new(),
            all_addrs: litmus.symbolic_addrs.clone(),
            physical_addrs: litmus.symbolic_addrs.clone(),
            initial_physical_addrs: litmus.locations.clone(),
            tables: HashMap::new(),
            maybe_mapped: HashSet::new(),
        }
    };
    let all_addrs = &page_table_setup.all_addrs;

    for thread in litmus.threads.iter() {
        match thread {
            Thread::Assembled(thread) => {
                log!(log::VERBOSE, &format!("Thread {} @ 0x{:x}", thread.name, thread.address));
                for (i, byte) in thread.code.iter().enumerate() {
                    memory.write_byte(thread.address + i as u64, *byte)
                }
            }
            Thread::IR(thread) => {
                log!(log::VERBOSE, &format!("Thread {} @ IR {}", thread.name, shared_state.symtab.to_str(thread.call)))
            }
        }
    }
    for section in litmus.sections.iter() {
        log!(log::VERBOSE, &format!("Section {} @ 0x{:x}", section.name, section.address));
        memory.add_concrete_region((section.address)..(section.address + section.bytes.len() as u64), HashMap::new());

        for (i, byte) in section.bytes.iter().enumerate() {
            memory.write_byte(section.address + i as u64, *byte)
        }
    }
    memory.log();

    let (initial_checkpoint, final_assertion) = {
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B>::from_checkpoint(&ctx, page_table_setup.memory_checkpoint.clone());

        let final_assertion = match partial_eval(
            &litmus.final_assertion,
            &memory,
            all_addrs,
            &page_table_setup.physical_addrs,
            &litmus.objdump,
            &mut solver,
        )
        .and_then(Partial::into_exp)
        {
            Ok(exp) => exp,
            Err(err) => return Err(LitmusRunError::Trace(TraceError::exec(err))),
        };

        (checkpoint(&mut solver), final_assertion)
    };

    let function_id = match shared_state.symtab.get("zmain") {
        Some(id) => id,
        None => return Err(LitmusRunError::NoMain),
    };

    let task_states: Vec<_> = litmus
        .threads
        .iter()
        .map(|thread| {
            let reset = thread
                .reset()
                .iter()
                .map(|(loc, exp)| (loc.clone(), reset_eval(exp, all_addrs, &litmus.objdump)))
                .collect();
            TaskState::with_reset_registers(reset)
        })
        .collect();
    let mut lets = arch.lets.clone();
    let tasks: Vec<_> = litmus
        .threads
        .iter()
        .enumerate()
        .map(|(i, thread)| {
            let mut regs = arch.regs.clone();
            for (reg, value) in thread.inits() {
                regs.insert(
                    *reg,
                    isa_config.relaxed_registers.contains(reg),
                    UVal::Init(Val::Bits(B::from_u64(*value))),
                );
            }
            match thread {
                Thread::Assembled(thread) => {
                    let (args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();
                    lets.insert(ELF_ENTRY, UVal::Init(Val::I128(thread.address as i128)));
                    LocalFrame::new(function_id, args, ret_ty, Some(&[Val::Unit]), instrs)
                        .add_lets(&lets)
                        .add_regs(&regs)
                        .set_memory(memory.clone())
                        .task_with_checkpoint(i, &task_states[i], initial_checkpoint.clone())
                }
                Thread::IR(thread) => {
                    let (args, ret_ty, instrs) = shared_state.functions.get(&thread.call).unwrap();
                    LocalFrame::new(thread.call, args, ret_ty, Some(&[Val::Unit]), instrs)
                        .add_lets(&lets)
                        .add_regs(&regs)
                        .set_memory(memory.clone())
                        .task_with_checkpoint(i, &task_states[i], initial_checkpoint.clone())
                }
            }
        })
        .collect();

    let mut threads: Vec<Vec<EvPath<B>>> = vec![Vec::new(); tasks.len()];
    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(
        opts.num_threads,
        opts.timeout,
        tasks,
        shared_state,
        queue.clone(),
        &executor::trace_collector,
    );
    log!(log::VERBOSE, &format!("Symbolic execution took: {}ms", now.elapsed().as_millis()));

    loop {
        match queue.pop() {
            Some(Ok((task_id, mut events))) => {
                let mut events: EvPath<B> = events
                    .drain(..)
                    .rev()
                    .filter(&event_filter)
                    .collect();
                simplify::remove_unused(&mut events);
                for event in events.iter_mut() {
                    simplify::renumber_event(event, task_id as u32, threads.len() as u32)
                }
                threads[task_id].push(events)
            }
            // Error during execution
            Some(Err(err)) => return Err(LitmusRunError::Trace(err)),
            // Empty queue
            None => break,
        }
    }

    Ok(LitmusSetup { threads, final_assertion, memory, page_table_setup })
}

/// Run a callback on each candidate execution of a litmus test.
pub fn litmus_per_candidate<B, P, F, E>(
    opts: &LitmusRunOpts,
    litmus: &Litmus<B>,
    arch: &InitArchWithConfig<B>,
    farch: &InitArchWithConfig<B>,
    cache: P,
    callback: &F,
) -> Result<LitmusRunInfo, LitmusRunError<E>>
where
    B: BV,
    P: AsRef<Path>,
    F: Sync
        + Send
        + Fn(
            ThreadId,
            &[&[Event<B>]],
            &HashMap<B, Footprint>,
            &HashMap<String, u64>,
            &HashMap<u64, u64>,
            &HashMap<String, (u64, &'static str)>,
            &HashSet<u64>,
            &Memory<B>,
            &Exp<u64>,
        ) -> Result<(), E>,
    E: Send + std::fmt::Debug,
{
    let LitmusSetup { threads: thread_buckets, final_assertion, memory, page_table_setup } =
        run_litmus_setup(opts, litmus, arch, |ev| {
            (ev.is_memory_read_or_write() && !(opts.ignore_ifetch && ev.is_ifetch()))
                || ev.is_smt()
                || ev.is_function()
                || ev.is_instr()
                || ev.is_cycle()
                || ev.is_write_reg()
                || ev.is_read_reg()
                || ev.is_abstract()
        })?;

    let footprints = footprint_analysis(opts.num_threads, &thread_buckets, farch, Some(cache.as_ref()))
        .map_err(LitmusRunError::Footprint)?;

    let candidates = Candidates::new(&thread_buckets);
    let num_candidates = candidates.total();
    log!(log::VERBOSE, &format!("There are {} candidate executions", num_candidates));
    let mut event_counts: Vec<String> = Vec::new();

    let cqueue = ArrayQueue::new(num_candidates);
    for (i, candidate) in candidates.enumerate() {
        event_counts.push(format!("{}", candidate.iter().map(|thread_events| thread_events.len()).sum::<usize>()));
        cqueue.push((i, candidate)).unwrap();
    }

    log!(log::VERBOSE, &format!("with {} events", event_counts.join(", ")));

    let err_queue = ArrayQueue::new(num_candidates);

    thread::scope(|scope| {
        for _ in 0..opts.num_threads {
            scope.spawn(|_| {
                while let Some((i, candidate)) = cqueue.pop() {
                    if let Err(err) = callback(
                        i,
                        &candidate,
                        &footprints,
                        &page_table_setup.all_addrs,
                        &page_table_setup.initial_physical_addrs,
                        &page_table_setup.tables,
                        &page_table_setup.maybe_mapped,
                        &memory,
                        &final_assertion,
                    ) {
                        err_queue.push(err).unwrap()
                    }
                }
            });
        }
    })
    .unwrap();

    let mut callback_errors = Vec::new();
    while let Some(err) = err_queue.pop() {
        callback_errors.push(err)
    }

    if callback_errors.is_empty() {
        Ok(LitmusRunInfo { candidates: num_candidates })
    } else {
        Err(LitmusRunError::Callback(callback_errors))
    }
}

#[derive(Debug)]
pub enum CallbackError<E> {
    Internal(String),
    User(E),
}

impl<E: IslaError> IslaError for CallbackError<E> {
    fn source_loc(&self) -> SourceLoc {
        match self {
            CallbackError::Internal(_) => SourceLoc::unknown(),
            CallbackError::User(err) => err.source_loc(),
        }
    }
}

fn internal_err<I: Error, E>(internal: I) -> CallbackError<E> {
    CallbackError::Internal(format!("{}", internal))
}

fn internal_err_boxed<E>(internal: Box<dyn Error>) -> CallbackError<E> {
    CallbackError::Internal(format!("{}", internal))
}

impl<E: fmt::Display> fmt::Display for CallbackError<E> {
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
    graph_opts: &GraphOpts,
    arch: &InitArchWithConfig<B>,
    farch: &InitArchWithConfig<B>,
    sexps: &SexpArena,
    memory_model: &[SexpId],
    memory_model_symtab: &memory_model::Symtab,
    memory_model_accessors: &HashMap<memory_model::Name, (Option<SexpId>, &[memory_model::Accessor])>,
    extra_smt: &[(String, String)],
    check_sat_using: Option<&str>,
    get_model: bool,
    cache: P,
    callback: &F,
) -> Result<LitmusRunInfo, LitmusRunError<CallbackError<E>>>
where
    B: BV,
    P: AsRef<Path> + Sync,
    F: Sync
        + Send
        + Fn(
            ExecutionInfo<B>,
            &Memory<B>,
            &HashMap<String, u64>,
            &HashMap<String, (u64, &'static str)>,
            &HashMap<B, Footprint>,
            &str,
        ) -> Result<(), E>,
    E: Send + std::fmt::Debug + IslaError,
{
    litmus_per_candidate(
        opts,
        litmus,
        arch,
        farch,
        &cache,
        &|tid,
          candidate,
          footprints,
          all_addrs,
          initial_physical_addrs,
          translation_tables,
          maybe_mapped,
          memory,
          final_assertion| {
            let mut negate_rf_assertion = "true".to_string();
            let mut first_run = true;
            loop {
                let now = Instant::now();

                let mut memory_model_symtab = memory_model_symtab.clone();

                let mut exec = ExecutionInfo::from(
                    candidate,
                    arch.shared_state,
                    arch.isa_config,
                    graph_opts,
                    &mut memory_model_symtab,
                )
                .map_err(internal_err)?;
                if let Some(keep_entire_translation) = opts.remove_uninteresting_translates {
                    exec.remove_uninteresting_translates(maybe_mapped, memory, keep_entire_translation)
                }
                if let Some(split_stages) = opts.merge_translations {
                    exec.merge_translations(split_stages, &mut memory_model_symtab)
                }

                let mut path = cache.as_ref().to_owned();
                path.push(format!("isla_candidate_{}_{}_{}.smt2", uid, std::process::id(), tid));

                // Create the SMT file with all the thread traces and the cat model.
                {
                    let mut fd = File::create(&path).unwrap();
                    writeln!(&mut fd, "(set-option :produce-models true)").map_err(internal_err)?;

                    let mut enums = HashSet::new();
                    for thread in candidate {
                        for event in *thread {
                            if let Event::Smt(smtlib::Def::DefineEnum(size), _) = event {
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
                        write_events_with_opts(&mut fd, thread, &arch.shared_state.symtab, &WriteOpts::smtlib())
                            .map_err(internal_err)?;
                    }

                    // FIXME
                    // We want to make sure we can extract the values read and written by the model if they are
                    // symbolic. Therefore we declare new variables that are guaranteed to appear in the generated model.
                    for (name, events) in exec.smt_events.iter().map(|ev| (&ev.name, &ev.base)) {
                        match events.last() {
                            Some(Event::ReadMem { value, address, bytes, .. })
                            | Some(Event::WriteMem { data: value, address, bytes, .. }) => {
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
                        litmus,
                        opts.ignore_ifetch,
                        opts.armv8_page_tables,
                        footprints,
                        memory,
                        initial_physical_addrs,
                        final_assertion,
                        arch.shared_state,
                        arch.isa_config,
                    )
                    .map_err(internal_err_boxed)?;

                    log!(log::LITMUS, "generating final smt");
                    writeln!(&mut fd, "(assert (and {}))", negate_rf_assertion).map_err(internal_err)?;

                    let mut sexps = sexps.clone();

                    writeln!(&mut fd, "; Accessors").map_err(internal_err)?;
                    let mut accessor_sexps = Vec::new();
                    for (accessor_fn, (ty, accessors)) in memory_model_accessors {
                        log!(log::LITMUS, &format!("accessor function {}", &memory_model_symtab[*accessor_fn]));
                        let f = generate_accessor_function(
                            *accessor_fn,
                            *ty,
                            accessors,
                            &exec.smt_events,
                            &exec.types,
                            arch.shared_state,
                            &memory_model_symtab,
                            &mut sexps,
                        );
                        accessor_sexps.push(f);
                    }
                    write_sexps(&mut fd, &accessor_sexps, &sexps, &memory_model_symtab).map_err(internal_err)?;

                    writeln!(&mut fd, "; Memory Model").map_err(internal_err)?;
                    write_sexps(&mut fd, memory_model, &sexps, &memory_model_symtab).map_err(internal_err)?;

                    for (file, smt) in extra_smt {
                        writeln!(&mut fd, "; Extra SMT {}", file.as_str()).map_err(internal_err)?;
                        writeln!(&mut fd, "{}", smt.as_str()).map_err(internal_err)?
                    }

                    if let Some(tactic) = check_sat_using {
                        writeln!(&mut fd, "(check-sat-using {})", tactic).map_err(internal_err)?
                    } else {
                        writeln!(&mut fd, "(check-sat)").map_err(internal_err)?
                    }

                    if get_model {
                        // Use get-value rather than get-model so we only get the values we need, otherwise z3 is very slow.
                        write!(&mut fd, "(get-value (").map_err(internal_err)?;
                        for (n, name) in memory_model_symtab.iter_toplevel().enumerate() {
                            if n != 0 {
                                write!(&mut fd, " ").map_err(internal_err)?;
                            }
                            write!(&mut fd, "{}", &memory_model_symtab[name]).map_err(internal_err)?;
                        }
                        writeln!(&mut fd, "))").map_err(internal_err)?;
                    }
                    log!(log::LITMUS, &format!("finished generating {}", path.display()));
                }

                let mut z3_command = Command::new("z3");
                if let Some(secs) = opts.timeout {
                    z3_command.arg(format!("-T:{}", secs));
                }
                if let Some(mem) = opts.memory {
                    z3_command.arg(format!("-memory:{}", mem));
                }
                z3_command.arg(&path);

                let z3 = z3_command.output().map_err(internal_err)?;
                let z3_output = std::str::from_utf8(&z3.stdout).map_err(internal_err)?;

                log!(log::VERBOSE, &format!("solver took: {}ms", now.elapsed().as_millis()));

                if_logging!(log::LITMUS, {
                    let mut path = cache.as_ref().to_owned();
                    path.push(format!("isla_candidate_{}_{}_{}_model.smt2", uid, std::process::id(), tid));
                    let mut fd = File::create(&path).unwrap();
                    writeln!(&mut fd, "{}", z3_output).map_err(internal_err)?;
                    log!(log::LITMUS, &format!("output model written to {}", path.display()));
                });

                //if std::fs::remove_file(&path).is_err() {}

                if !opts.exhaustive {
                    break callback(exec, memory, all_addrs, translation_tables, footprints, z3_output)
                        .map_err(CallbackError::User);
                } else if let Some(model_buf) = z3_output.strip_prefix("sat") {
                    let mut event_names: Vec<&str> = exec.smt_events.iter().map(|ev| ev.name.as_ref()).collect();
                    event_names.push("IW");

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

                    match callback(exec, memory, all_addrs, translation_tables, footprints, z3_output) {
                        Err(e) => break Err(CallbackError::User(e)),
                        Ok(()) => (),
                    }

                    first_run = false;
                } else if z3_output.starts_with("unsat") && !first_run {
                    break Ok(());
                } else {
                    break callback(exec, memory, all_addrs, translation_tables, footprints, z3_output)
                        .map_err(CallbackError::User);
                }
            }
        },
    )
}
