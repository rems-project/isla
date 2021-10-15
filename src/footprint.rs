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

use crossbeam::queue::SegQueue;
use getopts::Matches;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::convert::TryInto;
use std::io::Write;
use std::path::PathBuf;
use std::process::exit;
use std::sync::Arc;
use std::time::Instant;

use isla_axiomatic::footprint_analysis::footprint_analysis;
use isla_axiomatic::litmus::assemble_instruction;
use isla_axiomatic::page_table;
use isla_axiomatic::page_table::setup::PageTableSetup;
use isla_lib::bitvector::{b129::B129, BV};
use isla_lib::executor;
use isla_lib::executor::{LocalFrame, TaskState};
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::source_loc::SourceLoc;
use isla_lib::ir::*;
use isla_lib::memory::Memory;
use isla_lib::simplify;
use isla_lib::simplify::{EventTree, WriteOpts};
use isla_lib::smt;
use isla_lib::smt::{smtlib, Checkpoint, EvPath, Event, Solver};
use isla_lib::smt_parser;
use isla_lib::zencode;

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

pub fn hex_bytes(s: &str) -> Result<Vec<u8>, std::num::ParseIntError> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16)).collect()
}

#[derive(Clone, Debug)]
enum InstructionSegment {
    Concrete(B129),
    Symbolic(String, u32),
}

impl std::fmt::Display for InstructionSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            InstructionSegment::Concrete(bv) => bv.fmt(f),
            InstructionSegment::Symbolic(s, _) => s.fmt(f),
        }
    }
}

fn instruction_to_string(opcode: &[InstructionSegment]) -> String {
    let mut s = "".to_string();
    for seg in opcode {
        s += &format!("{} ", seg);
    }
    s
}

fn instruction_to_val(opcode: &[InstructionSegment], matches: &Matches, solver: &mut Solver<B129>) -> Val<B129> {
    match opcode {
        [InstructionSegment::Concrete(bv)] => Val::Bits(*bv),
        _ => {
            let mut var_map = HashMap::new();
            let val = Val::MixedBits(
                opcode
                    .iter()
                    .map(|segment| match segment {
                        InstructionSegment::Concrete(bv) => BitsSegment::Concrete(*bv),
                        InstructionSegment::Symbolic(name, size) => {
                            if let Some((size2, v)) = var_map.get(name) {
                                if size == size2 {
                                    BitsSegment::Symbolic(*v)
                                } else {
                                    panic!(
                                        "{} appears in instruction with different sizes, {} and {}",
                                        name, size, size2
                                    )
                                }
                            } else {
                                let v = solver.declare_const(smtlib::Ty::BitVec(*size), SourceLoc::unknown());
                                var_map.insert(name, (*size, v));
                                BitsSegment::Symbolic(v)
                            }
                        }
                    })
                    .collect(),
            );
            for constraint in matches.opt_strs("instruction-constraint") {
                let mut lookup = |loc: &Loc<String>| match loc {
                    Loc::Id(name) => match var_map.get(&zencode::decode(&name)) {
                        Some((_size, v)) => Ok(smtlib::Exp::Var(*v)),
                        None => Err(format!("No variable {} in constraint", name)),
                    },
                    _ => Err(format!("Only names can appear in instruction constraints, not {}", loc)),
                };
                let assertion =
                    smt_parser::ExpParser::new().parse(&constraint).expect("Bad instruction constraint");
                solver.add_event(Event::Assume(assertion.clone()));
                let assertion_exp = assertion.map_var(&mut lookup).expect("Bad instruction constraint");
                solver.add(smtlib::Def::Assert(assertion_exp));
            }
            val
        }
    }
}

fn opcode_bytes(opcode: Vec<u8>, little_endian: bool) -> B129 {
    if opcode.len() > 8 {
        eprintln!("Currently instructions greater than 8 bytes in length are not supported");
        exit(1);
    }

    if opcode.len() == 2 {
        let opcode: Box<[u8; 2]> = opcode.into_boxed_slice().try_into().unwrap();
        B129::from_u16(if little_endian { u16::from_le_bytes(*opcode) } else { u16::from_be_bytes(*opcode) })
    } else if opcode.len() == 4 {
        let opcode: Box<[u8; 4]> = opcode.into_boxed_slice().try_into().unwrap();
        B129::from_u32(if little_endian { u32::from_le_bytes(*opcode) } else { u32::from_be_bytes(*opcode) })
    } else {
        B129::from_bytes(&opcode)
    }
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.reqopt("i", "instruction", "display footprint of instruction", "<instruction>");
    opts.optopt("e", "endianness", "instruction encoding endianness (default: little)", "big/little");
    opts.optflag("d", "dependency", "view instruction dependency info");
    opts.optflag("x", "hex", "parse instruction as hexadecimal opcode, rather than assembly");
    opts.optflag("s", "simplify", "simplify instruction footprint");
    opts.optflag("", "simplify-registers", "simplify register accesses in traces");
    opts.optflag("t", "tree", "combine traces into tree");
    opts.optopt("f", "function", "use a custom footprint function", "<identifer>");
    opts.optflag("c", "continue-on-error", "continue generating traces upon encountering an error");
    opts.optopt("", "source", "Sail source code directory for .ir file", "<path>");
    opts.optopt("", "armv8-page-tables", "set up page tables with provided constraints", "<constraints>");
    opts.optflag("", "create-memory-regions", "create default memory regions");
    opts.optflag("", "partial", "parse instruction as binary with unknown bits");
    opts.optmulti("", "instruction-constraint", "add constraint on variables in a partial instruction", "<constraint>");
    opts.optflag("", "pessimistic", "fail on any assertion that is not necessarily true");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse(&mut hasher, &opts);
    if !matches.free.is_empty() {
        eprintln!("Unexpected arguments: {}", matches.free.join(" "));
        exit(1)
    }
    let CommonOpts { num_threads, mut arch, symtab, isa_config } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    // Note this is the opposite default to other tools
    let assertion_mode =
        if matches.opt_present("pessimistic") { AssertionMode::Pessimistic } else { AssertionMode::Optimistic };

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, assertion_mode);

    let little_endian = match matches.opt_str("endianness").as_deref() {
        Some("little") | None => true,
        Some("big") => false,
        Some(_) => {
            eprintln!("--endianness argument must be one of either `big` or `little`");
            exit(1)
        }
    };

    let instruction = matches.opt_str("instruction").unwrap();

    let opcode: Vec<InstructionSegment> = if matches.opt_present("partial") {
        instruction
            .split_ascii_whitespace()
            .map(|s| {
                B129::from_str(&format!("0b{}", s))
                    .map(InstructionSegment::Concrete)
                    .or_else(|| {
                        let mut it = s.split(':');
                        let name = it.next()?;
                        let size = it.next()?;
                        u32::from_str_radix(size, 10)
                            .ok()
                            .map(|size| InstructionSegment::Symbolic(name.to_string(), size))
                    })
                    .unwrap_or_else(|| {
                        eprintln!("Unable to parse instruction segment {}", s);
                        exit(1)
                    })
            })
            .collect()
    } else if matches.opt_present("hex") {
        match hex_bytes(&instruction) {
            Ok(opcode) => vec![InstructionSegment::Concrete(opcode_bytes(opcode, little_endian))],
            Err(e) => {
                eprintln!("Could not parse hexadecimal opcode: {}", e);
                exit(1)
            }
        }
    } else {
        match assemble_instruction(&instruction, &isa_config) {
            Ok(opcode) => vec![InstructionSegment::Concrete(opcode_bytes(opcode, little_endian))],
            Err(msg) => {
                eprintln!("{}", msg);
                return 1;
            }
        }
    };

    eprintln!("opcode: {}", instruction_to_string(&opcode));

    let mut memory = Memory::new();

    let PageTableSetup { memory_checkpoint, .. } = if let Some(setup) = matches.opt_str("armv8-page-tables") {
        let lexer = page_table::setup_lexer::SetupLexer::new(&setup);
        let constraints =
            match page_table::setup_parser::SetupParser::new().parse(&isa_config, lexer).map_err(|error| error.to_string()) {
                Ok(constraints) => constraints,
                Err(msg) => {
                    eprintln!("{}", msg);
                    return 1;
                }
            };
        page_table::setup::armv8_page_tables(&mut memory, HashMap::new(), 0, &constraints, &isa_config).unwrap()
    } else {
        PageTableSetup {
            memory_checkpoint: Checkpoint::new(),
            all_addrs: HashMap::new(),
            physical_addrs: HashMap::new(),
            initial_physical_addrs: HashMap::new(),
            tables: HashMap::new(),
        }
    };

    if matches.opt_present("create-memory-regions") {
        memory.add_zero_region(0x0..0xffff_ffff_ffff_ffff);
    }

    let footprint_function = match matches.opt_str("function") {
        Some(id) => zencode::encode(&id),
        None => "zisla_footprint".to_string(),
    };

    let (initial_checkpoint, opcode_val) = {
        let solver_cfg = smt::Config::new();
        let solver_ctx = smt::Context::new(solver_cfg);
        let mut solver = Solver::from_checkpoint(&solver_ctx, memory_checkpoint);
        let opcode_val = instruction_to_val(&opcode, &matches, &mut solver);
        // Record register assumptions from defaults; others are recorded at reset-registers
        let mut sorted_regs: Vec<(&Name, &UVal<_>)> = regs.iter().collect();
        sorted_regs.sort_by_key(|(name, _)| *name);
        for (register, uval) in sorted_regs {
            match uval {
                UVal::Init(value) => solver.add_event(Event::AssumeReg(*register, vec![], value.clone())),
                UVal::Uninit(_) => (),
            }
        }
        (smt::checkpoint(&mut solver), opcode_val)
    };

    let function_id = shared_state.symtab.lookup(&footprint_function);
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task_state = TaskState::new();
    let task = LocalFrame::new(function_id, args, Some(&[opcode_val.clone()]), instrs)
        .add_lets(&lets)
        .add_regs(&regs)
        .set_memory(memory)
        .task_with_checkpoint(0, &task_state, initial_checkpoint);

    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(num_threads, None, vec![task], &shared_state, queue.clone(), &executor::trace_collector);
    eprintln!("Execution took: {}ms", now.elapsed().as_millis());

    let mut paths = Vec::new();
    let rk_ifetch = shared_state.enum_member(isa_config.ifetch_read_kind).expect("Invalid ifetch read kind");
    let mut evtree: Option<EventTree<B129>> = None;

    loop {
        match queue.pop() {
            Some(Ok((_, mut events))) if matches.opt_present("dependency") => {
                let mut events: EvPath<B129> = events
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
                simplify::remove_unused(&mut events);
                events.push(Event::Instr(opcode_val.clone()));
                paths.push(events)
            }
            Some(Ok((_, mut events))) if matches.opt_present("tree") => {
                let events: Vec<Event<B129>> = events.drain(..).rev().collect();
                if let Some(ref mut evtree) = evtree {
                    evtree.add_events(&events)
                } else {
                    evtree = Some(EventTree::from_events(&events))
                }
            }
            Some(Ok((_, mut events))) => {
                if matches.opt_present("simplify") {
                    simplify::hide_initialization(&mut events);
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
                let stdout = std::io::stdout();
                let mut handle = stdout.lock();
                let write_opts = WriteOpts {
                    define_enum: !matches.opt_present("simplify"),
                    source_directory: matches.opt_str("source").map(PathBuf::from),
                    ..WriteOpts::default()
                };
                simplify::write_events_with_opts(&mut handle, &events, &shared_state.symtab, &write_opts).unwrap();
            }
            // Error during execution
            Some(Err(msg)) => {
                eprintln!("{}", msg);
                if !matches.opt_present("continue-on-error") {
                    return 1;
                }
            }
            // Empty queue
            None => break,
        }
    }

    if matches.opt_present("tree") {
        if let Some(ref mut evtree) = evtree {
            if matches.opt_present("simplify") {
                simplify::remove_unused_tree(evtree);
            }
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();
            simplify::write_event_tree(&mut handle, evtree, &shared_state.symtab);
            writeln!(&mut handle).unwrap();
        }
    }

    if matches.opt_present("dependency") {
        match footprint_analysis(num_threads, &[paths], &lets, &regs, &shared_state, &isa_config, None) {
            Ok(footprints) => {
                for (_, footprint) in footprints {
                    {
                        let stdout = std::io::stdout();
                        let mut handle = stdout.lock();
                        let _ = footprint.pretty(&mut handle, &shared_state.symtab);
                    }
                }
            }
            Err(footprint_error) => {
                eprintln!("{:?}", footprint_error);
                return 1;
            }
        }
    }

    0
}
