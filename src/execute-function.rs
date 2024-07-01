// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
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

use crossbeam::queue::SegQueue;
use sha2::{Digest, Sha256};
use std::convert::TryFrom;
use std::io::Write;
use std::process::exit;
use std::str::FromStr;
use std::sync::Arc;
use std::time::Instant;

use isla_lib::bitvector::b129::B129;
use isla_lib::bitvector::BV;
use isla_lib::error::ExecError;
use isla_lib::executor;
use isla_lib::executor::{reset_registers, Backtrace, LocalFrame, Run, StopAction, StopConditions, TaskId, TaskState};
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::ir_lexer::new_ir_lexer;
use isla_lib::smt;
use isla_lib::smt::smtlib::Exp;
use isla_lib::smt::{Event, Model, SmtResult, Solver};
use isla_lib::source_loc::SourceLoc;
use isla_lib::value_parser::ValParser;
use isla_lib::zencode;
use isla_lib::{log, log_from};
use isla_lib::{simplify, simplify::EventTree, simplify::WriteOpts};

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

#[allow(clippy::mutex_atomic)]
fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optflag("", "optimistic", "assume assertions succeed");
    opts.optflag("", "traces", "print execution traces for successful executions");
    opts.optflag("t", "tree", "combine traces into tree");
    opts.optflag("", "error-traces", "print execution traces for paths that fail");
    opts.optflag("s", "simplify", "simplify function traces");
    opts.optflag("", "simplify-registers", "simplify register accesses in traces");
    opts.optflag("m", "model", "query SMT model to fill in variables");
    opts.optmulti(
        "k",
        "kill-at",
        "stop executions early and discard if they reach this function (with optional context)",
        "<function name[, function_name]>",
    );
    opts.optmulti(
        "",
        "stop-at",
        "stop executions early and keep trace if they reach this function (with optional context)",
        "<function name[, function_name]>",
    );
    opts.optopt("", "timeout", "Add a timeout (in seconds)", "<n>");
    opts.optflag("", "executable", "make trace executable");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse::<B129>(&mut hasher, &opts);
    let CommonOpts { num_threads, mut arch, mut symtab, type_info, isa_config, source_path: _ } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let timeout: Option<u64> = match matches.opt_get("timeout") {
        Ok(timeout) => timeout,
        Err(e) => {
            eprintln!("Failed to parse --timeout: {}", e);
            return 1;
        }
    };

    // We add an extra register write to the end of successful
    // executions with the result value, partly to make it obvious,
    // but mostly so that trace simplification doesn't remove relevant
    // parts.
    let final_result_register = symtab.intern("zFinal result");

    if matches.free.is_empty() {
        eprintln!("No function given");
        return 1;
    }
    let function_name = zencode::encode(&matches.free[0]);

    let assertion_mode =
        if matches.opt_present("optimistic") { AssertionMode::Optimistic } else { AssertionMode::Pessimistic };

    let use_model_reg_init = !matches.opt_present("no-model-reg-init");

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut arch, symtab, type_info, &isa_config, assertion_mode, use_model_reg_init);

    let kill_conditions = StopConditions::parse(matches.opt_strs("kill-at"), &shared_state, StopAction::Kill);
    let abstract_conditions = StopConditions::parse(matches.opt_strs("stop-at"), &shared_state, StopAction::Abstract);
    let stop_conditions = kill_conditions.union(&abstract_conditions);
    let function_id = shared_state.symtab.lookup(&function_name);
    let (args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    let mut frame = LocalFrame::new(function_id, args, ret_ty, None, instrs);

    for (i, arg) in matches.free[1..].iter().enumerate() {
        if let Some((id, ty)) = args.get(i) {
            if let Some(size_str) = arg.strip_prefix("_:") {
                let size = u32::from_str(size_str).unwrap_or_else(|_| panic!("Bad size in {}", arg));
                frame.vars_mut().insert(*id, UVal::Uninit(Box::leak(Box::new(Ty::Bits(size)))));
            } else if arg != "_" {
                let val = ValParser::new()
                    .parse(&shared_state.symtab, &shared_state.type_info, new_ir_lexer(arg))
                    .unwrap_or_else(|e| panic!("Unable to parse argument {}: {}", arg, e));
                let val = match (ty, val) {
                    (Ty::I64, Val::I128(i)) => {
                        let j = i64::try_from(i).unwrap();
                        Val::I64(j)
                    }
                    (_, v) => v,
                };
                val.plausible(ty, &shared_state)
                    .unwrap_or_else(|_| panic!("Bad initial value for {}", shared_state.symtab.to_str(*id)));
                frame.vars_mut().insert(*id, UVal::Init(val));
            }
        } else {
            eprintln!("Too many arguments");
            return 1;
        }
    }

    let smt_cfg = smt::Config::new();
    let smt_ctx = smt::Context::new(smt_cfg);
    let mut solver = Solver::new(&smt_ctx);

    let task_state = TaskState::new();

    frame.add_lets(&lets).add_regs(&regs);

    // We don't call model initialisation in execute-function, so do register reset here.
    reset_registers(0, &mut frame, &task_state, &shared_state, &mut solver, SourceLoc::unknown())
        .expect("Reset registers failed");

    let mut task = frame.task_with_checkpoint(TaskId::fresh(), &task_state, smt::checkpoint(&mut solver));
    task.set_stop_conditions(&stop_conditions);

    let traces = matches.opt_present("traces");
    let tree = matches.opt_present("tree");
    let error_traces = matches.opt_present("error-traces");
    let models = matches.opt_present("model");
    let collecting = Arc::new((SegQueue::new(), tree | traces | error_traces, models));
    let now = Instant::now();
    executor::start_multi(num_threads, timeout, vec![task], &shared_state, collecting.clone(), &model_collector);

    eprintln!("Execution took: {}ms", now.elapsed().as_millis());

    let (queue, _, _) = collecting.as_ref();

    let write_events = |mut events, handle: &mut dyn Write| {
        if matches.opt_present("simplify") {
            // Don't do simplify::hide_initialization(&mut events); because
            // individual functions might not have a separate initialization
            // phase
            if matches.opt_present("simplify-registers") {
                simplify::remove_extra_register_fields(&mut events);
                simplify::remove_repeated_register_reads(&mut events);
                simplify::remove_unused_register_assumptions(&mut events);
            }
            simplify::remove_unused(&mut events);
            simplify::propagate_forwards_used_once(&mut events);
            simplify::commute_extract(&mut events);
            simplify::eval(&mut events);
        }
        let events: Vec<Event<B129>> = events.drain(..).rev().collect();
        let write_opts = WriteOpts { define_enum: !matches.opt_present("simplify"), ..WriteOpts::default() };
        simplify::write_events_with_opts(handle, &events, &shared_state, &write_opts).unwrap();
    };

    let mut evtree: Option<EventTree<B129>> = None;
    let mut exit_code = 0;

    loop {
        match queue.pop() {
            Some(Ok((_, result, mut events))) if tree => {
                events.insert(0, Event::WriteReg(final_result_register, vec![], result.clone()));
                let stdout = std::io::stdout();
                let mut handle = stdout.lock();
                writeln!(handle, "Result: {}", result.to_string(&shared_state)).unwrap();
                let events: Vec<Event<B129>> = events.drain(..).rev().collect();
                if let Some(ref mut evtree) = evtree {
                    evtree.add_events(&events)
                } else {
                    evtree = Some(EventTree::from_events(&events))
                }
            }
            Some(Ok((_, result, mut events))) => {
                events.insert(0, Event::WriteReg(final_result_register, vec![], result.clone()));
                let stdout = std::io::stdout();
                let mut handle = stdout.lock();
                writeln!(handle, "Result: {}", result.to_string(&shared_state)).unwrap();
                if traces {
                    write_events(events, &mut handle);
                }
            }
            // Error during execution
            Some(Err((msg, events))) => {
                let stdout = std::io::stdout();
                let mut handle = stdout.lock();
                writeln!(handle, "{}", msg).unwrap();
                if error_traces {
                    write_events(events, &mut handle);
                }
                exit_code = 1;
            }
            // Empty queue
            None => break,
        }
    }

    if tree {
        if let Some(ref mut evtree) = evtree {
            evtree.renumber();
            evtree.sort();
            if matches.opt_present("simplify") {
                if matches.opt_present("simplify-registers") {
                    simplify::remove_extra_register_fields_tree(evtree);
                    simplify::remove_repeated_register_reads_tree(evtree);
                    simplify::remove_unused_register_assumptions_tree(evtree);
                }
                simplify::remove_unused_tree(evtree);
                simplify::propagate_forwards_used_once_tree(evtree);
                simplify::commute_extract_tree(evtree);
                simplify::eval_tree(evtree);
            }
            if matches.opt_present("executable") {
                evtree.make_executable()
            }
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();
            let write_opts = WriteOpts { define_enum: !matches.opt_present("simplify"), ..WriteOpts::default() };
            simplify::write_event_tree(&mut handle, evtree, &shared_state, &write_opts);
            writeln!(&mut handle).unwrap();
        }
    }

    exit_code
}

fn bits_to_bv<B: BV>(bits: &[bool]) -> B {
    let mut bv = B::zeros(bits.len() as u32);
    for (n, bit) in bits.iter().enumerate() {
        if *bit {
            bv = bv.set_slice(n as u32, B::BIT_ONE);
        };
    }
    bv
}

fn concrete_value<B: BV>(model: &mut Model<B>, val: &Val<B>) -> Val<B> {
    match val {
        Val::Symbolic(v) => match model.get_var(*v) {
            Ok(Some(Exp::Bits64(bv))) => Val::Bits(B::new(bv.lower_u64(), bv.len())),
            Ok(Some(Exp::Bits(bs))) => Val::Bits(bits_to_bv(&bs)),
            _ => val.clone(),
        },
        Val::Vector(vec) => Val::Vector(vec.iter().map(|v| concrete_value(model, v)).collect()),
        Val::List(vec) => Val::List(vec.iter().map(|v| concrete_value(model, v)).collect()),
        Val::Struct(map) => Val::Struct(map.iter().map(|(k, v)| (*k, concrete_value(model, v))).collect()),
        Val::Ctor(n, v) => Val::Ctor(*n, Box::new(concrete_value(model, v))),
        _ => val.clone(),
    }
}

type AllTraceValueQueue<B> = SegQueue<Result<(TaskId, Val<B>, Vec<Event<B>>), (String, Vec<Event<B>>)>>;

fn model_collector<'ir, B: BV>(
    tid: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    (collected, trace, models): &(AllTraceValueQueue<B>, bool, bool),
) {
    let events: Vec<Event<B>> = if *trace { solver.trace().to_vec().drain(..).cloned().collect() } else { vec![] };
    match result {
        Ok((Run::Finished(val), _)) => {
            if solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat {
                let val = if *models {
                    let mut model = Model::new(&solver);
                    concrete_value(&mut model, &val)
                } else {
                    val
                };
                collected.push(Ok((task_id, val, events)))
            } else {
                collected.push(Err((format!("Got value {} but unsat?", val.to_string(shared_state)), events)))
            }
        }
        Ok((Run::Exit, _)) => collected.push(Err(("Exit".to_string(), events))),
        Ok((Run::Suspended { .. }, _)) => collected.push(Err(("Suspended".to_string(), events))),
        Ok((Run::Dead, _)) => (),
        Err((err, backtrace)) => {
            log_from!(tid, log::VERBOSE, format!("Error {:?}", err));
            for (f, pc) in backtrace.iter().rev() {
                log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
            }
            if solver.check_sat(SourceLoc::unknown()) == SmtResult::Sat {
                let model = Model::new(&solver);
                collected.push(Err((format!("Error {:?}\n{:?}", err, model), events)))
            } else {
                collected.push(Err((format!("Error {:?}\nno model", err), events)))
            }
        }
    }
}
