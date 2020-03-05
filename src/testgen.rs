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

use crossbeam::queue::SegQueue;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::process::exit;
use std::sync::Arc;
use std::time::Instant;

use isla_axiomatic::litmus::assemble_instruction;
use isla_lib::concrete::{B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::error::ExecError;
use isla_lib::executor;
use isla_lib::executor::{freeze_frame, Frame, LocalFrame};
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::memory::Memory;
use isla_lib::simplify::write_events;
use isla_lib::smt;
use isla_lib::smt::smtlib;
use isla_lib::smt::{Checkpoint, Event, Model, SmtResult, Solver};
use isla_lib::zencode;

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn postprocess<'ir, B: BV>(
    _task_id: usize,
    frame: LocalFrame<'ir, B>,
    _shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    events: &Vec<Event<B64>>,
    mut memory: u32,
) -> Result<(Frame<'ir, B>, Checkpoint<B>, u32), String> {
    use isla_lib::primop::smt_value;
    use isla_lib::smt::smtlib::{Def, Exp};

    for event in events {
        match event {
            Event::ReadMem { value, read_kind: _, address, bytes } => {
                let read_exp = smt_value(value).expect(&format!("Bad memory read value {:?}", value));
                let addr_exp = smt_value(address).expect(&format!("Bad read address value {:?}", address));
                // TODO: endianness?
                let mut mem_exp = Exp::Select(Box::new(Exp::Var(memory)), Box::new(addr_exp.clone()));
                for i in 1..*bytes {
                    mem_exp = Exp::Concat(
                        Box::new(mem_exp),
                        Box::new(Exp::Select(
                            Box::new(Exp::Var(memory)),
                            Box::new(Exp::Bvadd(Box::new(addr_exp.clone()), Box::new(Exp::Bits64(i as u64, 64)))),
                        )),
                    )
                }
                solver.add(Def::Assert(Exp::Eq(Box::new(read_exp), Box::new(mem_exp))));
            }
            Event::WriteMem { value: _, write_kind: _, address, data, bytes } => {
                let data_exp = smt_value(data).expect(&format!("Bad memory read value {:?}", data));
                let addr_exp = smt_value(address).expect(&format!("Bad read address value {:?}", address));
                // TODO: endianness?
                let mut mem_exp = Exp::Store(
                    Box::new(Exp::Var(memory)),
                    Box::new(addr_exp.clone()),
                    Box::new(Exp::Extract(bytes * 8 - 1, bytes * 8 - 8, Box::new(data_exp.clone()))),
                );
                for i in 1..*bytes {
                    mem_exp = Exp::Store(
                        Box::new(mem_exp),
                        Box::new(Exp::Bvadd(Box::new(addr_exp.clone()), Box::new(Exp::Bits64(i as u64, 64)))),
                        Box::new(Exp::Extract((bytes - i) * 8 - 1, (bytes - i) * 8 - 8, Box::new(data_exp.clone()))),
                    )
                }
                memory = solver.fresh();
                solver.add(Def::DefineConst(memory, mem_exp));
            }
            _ => (),
        }
    }

    match solver.check_sat() {
        SmtResult::Sat => return Ok((freeze_frame(&frame), smt::checkpoint(&mut solver), memory)),
        SmtResult::Unsat => return Err(String::from("unsatisfiable")),
        SmtResult::Unknown => return Err(String::from("solver returned unknown")),
    }
}

// Get a single opcode for debugging
fn get_opcode(checkpoint: Checkpoint<B64>, opcode_var: u32) -> Result<u32, String> {
    let cfg = smt::Config::new();
    cfg.set_param_value("model", "true");
    let ctx = smt::Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    match solver.check_sat() {
        SmtResult::Sat => (),
        SmtResult::Unsat => return Err(String::from("Unsatisfiable at recheck")),
        SmtResult::Unknown => return Err(String::from("Solver returned unknown at recheck")),
    };
    let mut model = Model::new(&solver);
    log!(log::VERBOSE, format!("Model: {:?}", model));
    let opcode = model.get_bv_var(opcode_var).unwrap().unwrap();
    match opcode {
        smt::smtlib::Exp::Bits64(bits, _) => Ok(bits as u32),
        _ => Err(String::from("Bad model value")),
    }
}

enum RegSource {
    Concrete(u64),
    Symbolic(u32),
    Uninit,
}

fn setup_init_regs<'ir>(
    shared_state: &SharedState<'ir, B64>,
    frame: Frame<'ir, B64>,
    checkpoint: Checkpoint<B64>,
) -> (Frame<'ir, B64>, Checkpoint<B64>, Vec<(String, RegSource)>, u32) {
    let mut local_frame = executor::unfreeze_frame(&frame);
    let ctx = smt::Context::new(smt::Config::new());
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    let mut regs: Vec<String> = (0..31).map(|r| format!("R{}", r)).collect();
    let mut other_regs = ["SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| r.to_string()).collect();
    regs.append(&mut other_regs);

    let mut inits = vec![];
    for reg in regs {
        let ex_var =
            shared_state.symtab.get(&zencode::encode(&reg)).expect(&format!("Register {} missing during setup", reg));
        let ex_val =
            local_frame.regs_mut().get_mut(&ex_var).expect(&format!("No value for register {} during setup", reg));
        match ex_val {
            UVal::Uninit(Ty::Bits(64)) => {
                let var = solver.fresh();
                solver.add(smtlib::Def::DeclareConst(var, smtlib::Ty::BitVec(64)));
                *ex_val = UVal::Init(Val::Symbolic(var));
                inits.push((reg, RegSource::Symbolic(var)));
            }
            UVal::Init(Val::Symbolic(var)) => {
                inits.push((reg, RegSource::Symbolic(*var)));
            }
            UVal::Init(Val::Bits(bits)) => {
                inits.push((reg, RegSource::Concrete(bits.bits)));
            }
            _ => panic!("Bad value for register {} in setup", reg),
        }
    }

    let memory = solver.fresh();
    solver.add(smtlib::Def::DeclareConst(
        memory,
        smtlib::Ty::Array(Box::new(smtlib::Ty::BitVec(64)), Box::new(smtlib::Ty::BitVec(8))),
    ));

    (freeze_frame(&local_frame), smt::checkpoint(&mut solver), inits, memory)
}

fn regs_for_state<'ir>(shared_state: &SharedState<'ir, B64>, frame: Frame<'ir, B64>) -> Vec<(String, RegSource)> {
    let mut local_frame = executor::unfreeze_frame(&frame);
    let mut regs: Vec<String> = (0..31).map(|r| format!("R{}", r)).collect();
    let mut other_regs = ["SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| r.to_string()).collect();
    regs.append(&mut other_regs);

    let mut reg_sources = vec![];
    for reg in regs {
        let ex_var =
            shared_state.symtab.get(&zencode::encode(&reg)).expect(&format!("Register {} missing during setup", reg));
        let ex_val =
            local_frame.regs_mut().get_mut(&ex_var).expect(&format!("No value for register {} during setup", reg));
        match ex_val {
            UVal::Uninit(Ty::Bits(64)) => {
                reg_sources.push((reg, RegSource::Uninit));
            }
            UVal::Init(Val::Symbolic(var)) => {
                reg_sources.push((reg, RegSource::Symbolic(*var)));
            }
            UVal::Init(Val::Bits(bits)) => {
                reg_sources.push((reg, RegSource::Concrete(bits.bits)));
            }
            _ => panic!("Bad value for register {} in setup", reg),
        }
    }
    reg_sources
}

// Report final model details
fn interrogate_model<'i, V>(checkpoint: Checkpoint<B64>, vars: V) -> Result<(), String>
where
    V: Iterator<Item = &'i (String, RegSource)>,
{
    let cfg = smt::Config::new();
    cfg.set_param_value("model", "true");
    let ctx = smt::Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    match solver.check_sat() {
        SmtResult::Sat => (),
        SmtResult::Unsat => return Err(String::from("Unsatisfiable at recheck")),
        SmtResult::Unknown => return Err(String::from("Solver returned unknown at recheck")),
    };

    let mut model = Model::new(&solver);
    log!(log::VERBOSE, format!("Model: {:?}", model));

    let mut unassigned = Vec::new();

    for (name, val) in vars {
        match val {
            RegSource::Symbolic(var) => {
                let model_val = model.get_bv_var(*var).unwrap();
                match model_val {
                    Some(smtlib::Exp::Bits64(bits, _)) => println!("{}: {:#010x}", name, bits),
                    Some(_) => println!("Bad model value"),
                    None => unassigned.push(name),
                }
            }
            RegSource::Concrete(v) => {
                println!("{}: {:#010x}  (fixed)", name, v);
            }
            RegSource::Uninit => unassigned.push(name),
        }
    }
    if unassigned.len() > 0 {
        print!("Unassigned:");
        for name in unassigned {
            print!(" {}", name)
        }
        println!(".")
    }
    Ok(())
}

fn init_model<'ir, B: BV>(
    shared_state: &SharedState<'ir, B>,
    lets: Bindings<'ir, B>,
    regs: Bindings<'ir, B>,
    memory: &Memory,
) -> (Frame<'ir, B>, Checkpoint<B>) {
    eprintln!("Initialising model...");

    let init_fn = shared_state.symtab.lookup("zinit");
    let (init_args, _, init_instrs) = shared_state.functions.get(&init_fn).unwrap();
    let init_result = SegQueue::new();
    let init_task = LocalFrame::new(init_args, None, init_instrs)
        .add_lets(&lets)
        .add_regs(&regs)
        .set_memory(memory.clone())
        .task(0);

    executor::start_single(
        init_task,
        &shared_state,
        &init_result,
        &move |_tid, _task_id, result, _shared_state, mut solver, init_result| match result {
            Ok((_, frame)) => {
                init_result.push((freeze_frame(&frame), smt::checkpoint(&mut solver)));
            }
            Err(err) => eprintln!("Initialisation failed: {:?}", err),
        },
    );
    if init_result.len() != 1 {
        eprintln!("Expected initialisation to have one path, found {}", init_result.len());
        exit(1);
    }
    let (frame, post_init_checkpoint) = init_result.pop().expect("pop failed");
    eprintln!("...done");

    (frame, post_init_checkpoint)
}

fn setup_opcode(
    opcode: B64,
    opcode_mask: Option<u32>,
    prev_checkpoint: Checkpoint<B64>,
) -> (Val<B64>, u32, Checkpoint<B64>) {
    use isla_lib::smt::smtlib::{Def, Exp, Ty};
    use isla_lib::smt::*;

    let ctx = smt::Context::new(smt::Config::new());
    let mut solver = Solver::from_checkpoint(&ctx, prev_checkpoint);

    let opcode_var = solver.fresh();
    solver.add(Def::DeclareConst(opcode_var, Ty::BitVec(32)));

    // Working with a mask currently requires the model to be
    // sufficiently monomorphic, so prefer using a concrete value if
    // we can.  (Even if the variable bitvector length part of the
    // model is fully determined by the unmasked bits, the executor
    // doesn't attempt to replace them with a concrete value.)
    let opcode_val: Val<B64>;
    if let Some(opcode_mask) = opcode_mask {
        solver.add(Def::Assert(Exp::Eq(
            Box::new(Exp::Bvand(Box::new(Exp::Var(opcode_var)), Box::new(Exp::Bits64(opcode_mask as u64, 32)))),
            Box::new(Exp::Bits64(opcode.bits & opcode_mask as u64, opcode.length)),
        )));
        opcode_val = Val::Symbolic(opcode_var);
    } else {
        solver.add(Def::Assert(Exp::Eq(
            Box::new(Exp::Var(opcode_var)),
            Box::new(Exp::Bits64(opcode.bits, opcode.length)),
        )));
        opcode_val = Val::Bits(opcode);
    }

    (opcode_val, opcode_var, checkpoint(&mut solver))
}

fn run_model_instruction<'ir>(
    num_threads: usize,
    shared_state: &SharedState<'ir, B64>,
    frame: Frame<'ir, B64>,
    checkpoint: Checkpoint<B64>,
    opcode_var: u32,
    opcode_val: Val<B64>,
    memory: u32,
    dump_events: bool,
) -> Vec<(Frame<'ir, B64>, Checkpoint<B64>, u32)> {
    let function_id = shared_state.symtab.lookup("zdecode64");
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();

    let mut local_frame = executor::unfreeze_frame(&frame);
    let see_id = shared_state.symtab.lookup("zSEE");
    let see = local_frame.regs_mut().get_mut(&see_id).expect("SEE register missing");
    *see = UVal::Init(Val::I128(-1));

    let task = local_frame.new_call(args, Some(&[opcode_val]), instrs).task_with_checkpoint(1, checkpoint);

    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(
        num_threads,
        None,
        vec![task],
        &shared_state,
        queue.clone(),
        &move |_, task_id, result, shared_state, solver, collected| {
            use isla_lib::simplify::simplify;
            let mut events = simplify(solver.trace());
            let events: Vec<Event<B64>> = events.drain(..).map({ |ev| ev.clone() }).collect();
            match result {
                Ok((Val::Unit, frame)) => {
                    collected.push((postprocess(task_id, frame, shared_state, solver, &events, memory), events))
                }
                // Anything else is an error!
                Ok((val, _)) => collected.push((Err(format!("Unexpected footprint return value: {:?}", val)), events)),
                Err(ExecError::Dead) => collected.push((Err(String::from("dead")), events)),
                Err(err) => collected.push((Err(format!("Error {:?}", err)), events)),
            }
        },
    );

    eprintln!("Execution took: {}ms", now.elapsed().as_millis());

    let mut result = vec![];

    loop {
        match queue.pop() {
            Ok((Ok((new_frame, new_checkpoint, new_memory)), mut events)) => {
                log!(
                    log::VERBOSE,
                    match get_opcode(new_checkpoint.clone(), opcode_var) {
                        Ok(model_opcode) => format!("Found {:#010x}", model_opcode),
                        Err(msg) => format!("Failed to retrieve opcode: {}", msg),
                    }
                );
                if dump_events {
                    let stdout = std::io::stderr();
                    let mut handle = stdout.lock();
                    let events: Vec<Event<B64>> = events.drain(..).rev().collect();
                    write_events(&mut handle, &events, &shared_state.symtab);
                }
                result.push((new_frame, new_checkpoint, new_memory));
            }

            // Error during execution
            Ok((Err(msg), mut events)) => {
                println!("Failed path {}", msg);
                if dump_events {
                    let stdout = std::io::stderr();
                    let mut handle = stdout.lock();
                    let events: Vec<Event<B64>> = events.drain(..).rev().collect();
                    write_events(&mut handle, &events, &shared_state.symtab);
                }
            }
            // Empty queue
            Err(_) => break,
        }
    }
    result
}

fn parse_instructions(
    hex: bool,
    little_endian: bool,
    isa_config: &ISAConfig<B64>,
    args: Vec<String>,
) -> Vec<(B64, Option<u32>)> {
    let mut iter = args.iter().peekable();
    let mut v: Vec<(&str, Option<&str>)> = vec![];
    loop {
        let s = match iter.next() {
            None => break,
            Some(s) => s,
        };
        let p = iter.peek();
        let p = p.map(|r| *r);
        let m: Option<&str> = match p {
            None => None,
            Some(s) => {
                if s.starts_with("mask:") {
                    iter.next();
                    Some(&s[5..])
                } else {
                    None
                }
            }
        };
        v.push((s, m));
    }
    v.iter()
        .map(|(instruction, mask)| {
            let opcode = if hex {
                match u32::from_str_radix(&instruction, 16) {
                    Ok(opcode) => opcode.to_le_bytes(),
                    Err(e) => {
                        eprintln!("Could not parse instruction: {}", e);
                        exit(1)
                    }
                }
            } else {
                match assemble_instruction(&instruction, &isa_config) {
                    Ok(bytes) => {
                        let mut opcode: [u8; 4] = Default::default();
                        opcode.copy_from_slice(&bytes);
                        opcode
                    }
                    Err(msg) => {
                        eprintln!("Could not assemble instruction: {}", msg);
                        exit(1);
                    }
                }
            };
            let opcode =
                B64::from_u32(if little_endian { u32::from_le_bytes(opcode) } else { u32::from_be_bytes(opcode) });
            let mask = mask.map(|mask| match u32::from_str_radix(&mask, 16) {
                Ok(m) => m,
                Err(e) => {
                    eprintln!("Could not parse mask: {}", e);
                    exit(1)
                }
            });
            (opcode, mask)
        })
        .collect()
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optopt("e", "endianness", "instruction encoding endianness (little default)", "big/little");
    opts.optflag("x", "hex", "parse instruction as hexadecimal opcode, rather than assembly");
    opts.optflag("", "events", "dump final events");
    opts.optflag("", "all-events", "dump events for every behaviour");

    let mut hasher = Sha256::new();
    let (matches, mut arch) = opts::parse(&mut hasher, &opts);

    // The model initialisation needs a nominal entry point.
    let elf_entry = "elf_entry";
    arch.push(Def::Let(
        vec![(elf_entry.to_string(), Ty::I128)],
        vec![Instr::Init(elf_entry.to_string(), Ty::I128, Exp::I128(0))],
    ));

    let CommonOpts { num_threads, mut arch, symtab, isa_config } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    let little_endian = match matches.opt_str("endianness").as_ref().map(String::as_str) {
        Some("little") | None => true,
        Some("big") => false,
        Some(_) => {
            eprintln!("--endianness argument must be one of either `big` or `little`");
            exit(1)
        }
    };

    let dump_events = matches.opt_present("events");
    let dump_all_events = matches.opt_present("all-events");

    let mut memory = Memory::new();
    memory.add_concrete_region(isa_config.thread_base..isa_config.thread_top, HashMap::new());
    memory.log();

    let instructions = parse_instructions(matches.opt_present("hex"), little_endian, &isa_config, matches.free);

    let (frame, checkpoint) = init_model(&shared_state, lets, regs, &memory);
    let (mut frame, mut checkpoint, init_regs, mut memory) = setup_init_regs(&shared_state, frame, checkpoint);

    let mut opcode_vars = vec![];

    let mut opcode_index = 0;
    for (opcode, opcode_mask) in instructions {
        let mask_str = match opcode_mask {
            None => "none".to_string(),
            Some(m) => format!("{:#010x}", m),
        };
        eprintln!("opcode: {:#010x}  mask: {}", opcode.bits, mask_str);
        let (opcode_val, opcode_var, op_checkpoint) = setup_opcode(opcode, opcode_mask, checkpoint);
        opcode_vars.push((format!("opcode {}", opcode_index), RegSource::Symbolic(opcode_var)));
        opcode_index += 1;
        let mut continuations = run_model_instruction(
            num_threads,
            &shared_state,
            frame,
            op_checkpoint,
            opcode_var,
            opcode_val,
            memory,
            dump_all_events,
        );
        let num_continuations = continuations.len();
        if let Some((f, c, m)) = continuations.pop() {
            eprintln!("{} successful execution(s)", num_continuations);
            frame = f;
            checkpoint = c;
            memory = m;
        } else {
            eprintln!("No successful executions");
            exit(1);
        }
    }

    eprintln!("Complete");

    if dump_events {
        use isla_lib::simplify::simplify;
        let trace = checkpoint.trace().as_ref().expect("No trace!");
        let mut events = simplify(trace);
        let events: Vec<Event<B64>> = events.drain(..).map({ |ev| ev.clone() }).rev().collect();
        write_events(&mut std::io::stdout(), &events, &shared_state.symtab);
    }

    println!("Initial state:");
    match interrogate_model(checkpoint.clone(), opcode_vars.iter().chain(init_regs.iter())) {
        Ok(_) => (),
        Err(msg) => {
            eprintln!("{}", msg);
            exit(1)
        }
    }

    println!("Sample final state:");
    match interrogate_model(checkpoint.clone(), regs_for_state(&shared_state, frame).iter()) {
        Ok(_) => (),
        Err(msg) => {
            eprintln!("{}", msg);
            exit(1)
        }
    }

    0
}
