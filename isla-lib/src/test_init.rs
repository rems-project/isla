#![allow(unused_imports)]
#![allow(dead_code)]

use std::fs;
use std::path::PathBuf;
use std::time::Instant;
use std::collections::HashMap;
use std::sync::Arc;
use isla_lib::concrete::{bitvector64::B64, BV};
use isla_lib::memory::Memory;
use isla_lib::init;
use isla_lib::init::Initialized;
use isla_lib::ir::serialize as ir_serialize;
use isla_lib::ir::*;
use isla_lib::executor::LocalFrame;
use isla_lib::executor::Frame;
use isla_lib::executor::Task;
use isla_lib::smt::Checkpoint;
use isla_lib::executor;
use isla_lib::config::ISAConfig;
use isla_lib::smt::Config;
use isla_lib::smt::Context;
use isla_lib::smt;
use isla_lib::smt::Solver;
use isla_lib::error::ExecError;
use isla_lib::smt::Event;
use isla_lib::log;
use isla_lib::executor::Backtrace;
use isla_lib::elf_loader;
use isla_lib::ir::UVal;
use crossbeam::queue::SegQueue;

pub fn create_initial_task() -> (Task<B64>, SharedState<B64>) {
    let now = Instant::now();
    let folder = PathBuf::from(r"C:\Users\Benni\repositories\master\verification\sail-arm\1166c197b127ed30d95421dcfa5fc59716aa1368");
    //let folder = PathBuf::from(r"C:\Users\Benni\Downloads\");
    //let folder = PathBuf::from(r"C:\Users\Benni\repositories\master-arm\aarch64");
    let config_file = folder.join("aarch64.toml");
    let symtab_file = folder.join("aarch64.symtab");
    let ir_file     = folder.join("aarch64.irx");

    let strings: Vec<String> = bincode::deserialize(&fs::read(&symtab_file).unwrap()).unwrap();
    let symtab = Symtab::from_raw_table(&strings);
    let ir: Vec<Def<Name, B64>> = ir_serialize::deserialize(&fs::read(&ir_file).unwrap()).expect("Failed to deserialize IR");
    let isa_config: ISAConfig<B64> = ISAConfig::parse(&fs::read_to_string(&config_file).unwrap(), &symtab).unwrap();
    println!("Loaded architecture in: {}ms", now.elapsed().as_millis());

    let Initialized { mut regs, lets, shared_state } = init::initialize_architecture(ir, symtab, &isa_config, AssertionMode::Optimistic);
    init::initialize_registers_arm64(&mut regs, &shared_state);

    let reset_function_id = shared_state.symtab.lookup("zTakeReset");
    let (reset_args, _, reset_instrs) = shared_state.functions.get(&reset_function_id).unwrap();

    let vals = vec!(Val::Bool(true));
    let mut lf: LocalFrame<B64> = LocalFrame::new(reset_function_id, reset_args, Some(&vals), reset_instrs.clone());
    lf.add_lets(&lets);
    lf.add_regs(&regs);
    let mem = lf.memory_mut();
    elf_loader::load_elf(r"C:\Users\Benni\repositories\isla_orig\isla-lib\router", mem);
    let task = lf.task(0);

    (executor::execute_sail_function_no_fork(task, &shared_state), shared_state)
}
