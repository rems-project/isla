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
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::io;
use std::io::Write;
use std::process::exit;
use std::sync::Arc;
use std::time::Instant;

use isla_cat::cat;

use isla_lib::concrete::Sbits;
use isla_lib::executor;
use isla_lib::executor::LocalFrame;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::litmus::Litmus;
use isla_lib::log;
use isla_lib::memory::Memory;
use isla_lib::simplify::{write_events_with_opts, EventReferences, Taints};
use isla_lib::smt::{Accessor, Event};
use isla_lib::zencode;

mod opts;
mod smt_events;

use opts::CommonOpts;
use smt_events::{smt_candidate, Candidates};

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

#[derive(Debug)]
struct Footprint {
    mem_data_taints: (Taints, bool),
    mem_addr_taints: (Taints, bool),
    register_reads: HashSet<(u32, Vec<Accessor>)>,
    register_writes: HashSet<(u32, Vec<Accessor>)>,
    /// A store is any instruction with a WriteMem event
    is_store: bool,
    /// A load is any instruction with a ReadMem event
    is_load: bool,
}

impl Footprint {
    fn new() -> Self {
        Footprint {
            mem_data_taints: (HashSet::new(), false),
            mem_addr_taints: (HashSet::new(), false),
            register_reads: HashSet::new(),
            register_writes: HashSet::new(),
            is_store: false,
            is_load: false,
        }
    }

    fn pretty(&self, buf: &mut dyn Write, symtab: &Symtab) -> Result<(), Box<dyn Error>> {
        write!(buf, "Footprint:\n  Memory data:")?;
        for (reg, accessor) in &self.mem_data_taints.0 {
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

/// The axiomatic memory model requires deriving (syntactic) address,
/// data, and control dependencies. As such, we need to know what
/// registers could be touched by each opcode based purely on its
/// opcode. For this we analyse all the traces from a litmus test run,
/// and use symbolic execution on each opcode again.
fn footprint_analysis<'ir>(
    num_threads: usize,
    thread_buckets: &[Vec<Vec<Event>>],
    lets: &Bindings<'ir>,
    regs: &Bindings<'ir>,
    shared_state: &SharedState,
) -> Option<()> {
    let mut concrete_opcodes: HashSet<Sbits> = HashSet::new();

    for thread in thread_buckets {
        for path in thread {
            for event in path {
                match event {
                    Event::Instr(Val::Bits(bv)) => {
                        concrete_opcodes.insert(bv.clone());
                    }
                    Event::Instr(_) => panic!("Cannot currently handle symbolic instructions!"),
                    _ => (),
                }
            }
        }
    }

    log!(log::VERBOSE, &format!("Got {} concrete opcodes for footprint analysis", concrete_opcodes.len()));

    let function_id = match shared_state.symtab.get("zisla_footprint") {
        Some(id) => id,
        None => {
            eprintln!(
                "Footprint analysis failed. To calculate the syntactic\n\
                 register footprint, isla expects a sail function\n\
                 `isla_footprint' to be available in the model, which\n\
                 can be used to decode and execute an instruction"
            );
            return None;
        }
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
            Ok(Err(msg)) => {
                eprintln!("{}", msg);
                return None;
            }
            // Empty queue
            Err(_) => break,
        }
    }

    let num_footprints: usize = footprint_buckets.iter().map(|instr_paths| instr_paths.len()).sum();
    log!(log::VERBOSE, &format!("There are {} footprints", num_footprints));

    let now = Instant::now();
    for (i, paths) in footprint_buckets.iter().enumerate() {
        let opcode = task_opcodes[i];
        log!(log::VERBOSE, &format!("{:?}", opcode));

        let mut footprint = Footprint::new();

        for events in paths {
            let evrefs = EventReferences::from_events(events);
            for event in events {
                match event {
                    Event::ReadReg(reg, accessor, _) => {
                        footprint.register_reads.insert((*reg, accessor.clone()));
                    }
                    Event::WriteReg(reg, accessor, _) => {
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
                            &mut footprint.mem_data_taints.0,
                            &mut footprint.mem_data_taints.1,
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
    }

    Some(())
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.reqopt("l", "litmus", "load a litmus file", "<file>");
    opts.reqopt("m", "model", "load a cat memory model", "<file>");

    let (matches, arch) = opts::parse(&opts);
    let CommonOpts { num_threads, mut arch, symtab, isa_config } = opts::parse_with_arch(&opts, &matches, &arch);

    let Initialized { regs, mut lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    let litmus = match Litmus::from_file(matches.opt_str("litmus").unwrap(), &isa_config) {
        Ok(litmus) => litmus,
        Err(e) => {
            eprintln!("{}", e);
            return 1;
        }
    };

    let cat = match cat::load_cat(&matches.opt_str("model").unwrap()) {
        Ok(cat) => {
            let mut tcx = cat::initial_tcx(isa_config.fences.iter().map(String::clone));
            match cat::infer_cat(&mut tcx, cat) {
                Ok(cat) => cat,
                Err(e) => {
                    eprintln!("Type error in cat: {:?}", e);
                    return 1;
                }
            }
        }
        Err(e) => {
            eprintln!("Could not load cat: {}", e);
            return 1;
        }
    };

    {
        let stdout = io::stdout();
        let mut handle = stdout.lock();
        isla_cat::smt::compile_cat(&mut handle, &cat).expect("Failed to compile cat");
    }

    let mut memory = Memory::new();
    memory.add_concrete_region(isa_config.thread_base..isa_config.thread_top, HashMap::new());

    let mut current_base = isa_config.thread_base;
    for (thread, code) in litmus.assembled.iter() {
        log!(log::VERBOSE, &format!("Thread {} @ 0x{:x}", thread, current_base));
        for (i, byte) in code.iter().enumerate() {
            memory.write_byte(current_base + i as u64, *byte)
        }
        current_base += isa_config.thread_stride
    }

    litmus.log();
    memory.log();

    let function_id = shared_state.symtab.lookup("zmain");
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();
    let tasks: Vec<_> = litmus
        .assembled
        .iter()
        .enumerate()
        .map(|(i, _)| {
            let address = isa_config.thread_base + (isa_config.thread_stride * i as u64);
            lets.insert(ELF_ENTRY, UVal::Init(Val::I128(address as i128)));
            LocalFrame::new(args, Some(&[Val::Unit]), instrs)
                .add_lets(&lets)
                .add_regs(&regs)
                .set_memory(memory.clone())
                .task(i)
        })
        .collect();

    let mut thread_buckets: Vec<Vec<Vec<Event>>> = vec![Vec::new(); tasks.len()];
    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(num_threads, tasks, &shared_state, queue.clone(), &executor::trace_collector);
    log!(log::VERBOSE, &format!("Symbolic execution took: {}ms", now.elapsed().as_millis()));

    let rk_ifetch = match shared_state.enum_member("Read_ifetch") {
        Some(rk) => rk,
        None => {
            eprintln!("No `Read_ifetch' read kind found in specified architecture!");
            return 1;
        }
    };

    loop {
        match queue.pop() {
            Ok(Ok((task_id, mut events))) => {
                let events: Vec<Event> = events
                    .drain(..)
                    .filter(|ev| (ev.is_memory() && !ev.has_read_kind(rk_ifetch)) || ev.is_smt() || ev.is_instr())
                    .collect();
                let mut events = isla_lib::simplify::remove_unused(events.to_vec());
                for event in events.iter_mut() {
                    isla_lib::simplify::renumber_event(event, task_id as u32, thread_buckets.len() as u32)
                }
                /*
                let mut buf = String::new();
                write_events_with_opts(&events, &shared_state.symtab, &mut buf, true);
                println!("{}", buf);
                */
                thread_buckets[task_id].push(events)
            }
            // Error during execution
            Ok(Err(msg)) => {
                eprintln!("{}", msg);
                return 1;
            }
            // Empty queue
            Err(_) => break,
        }
    }

    footprint_analysis(num_threads, &thread_buckets, &lets, &regs, &shared_state);

    let candidates = Candidates::new(&thread_buckets);

    log!(log::VERBOSE, &format!("There are {} candidate executions", candidates.total()));

    for candidate in candidates {
        /*
        let stdout = std::io::stderr();
        let mut handle = stdout.lock();
        match smt_candidate(&mut handle, &candidate) {
            Ok(_) => {
                writeln!(handle, "Ok");
            }
            Err(e) => {
                writeln!(handle, "Fail");
            }
        }
         */
        ()
    }

    0
}
