
#![allow(unused_imports)]
#![allow(dead_code)]

pub mod test_init;

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
use isla_lib::ir::UVal;
use crossbeam::queue::SegQueue;

use elfloader::*;

fn main() {
    let (mut task, shared_state) = test_init::create_initial_task();
    let step_function_id = shared_state.symtab.lookup("zStep_CPU");
    let (_step_args, _, step_instrs) = shared_state.functions.get(&step_function_id).unwrap();

    // prepare os emulation
    log::set_flags(0xffffffff);
    let mut lf = executor::unfreeze_frame(&task.frame);
    lf.regs_mut().insert(shared_state.symtab.lookup("z_PC"), UVal::Init(Val::Bits(B64::from_u64(0x0000000000215f38))));
    lf.function_name = step_function_id;
    lf.instrs = step_instrs.clone();
    init::reinitialize_registers_arm64(lf.regs_mut(), &shared_state);
    task.frame = executor::freeze_frame(&lf);

    // go!
    print_register(&task.frame, &shared_state.symtab, "zPSTATE");
    println!("starting execution");
    loop {
        task = executor::execute_sail_function_no_fork(task, &shared_state);
        //print_registers(&task.frame, &shared_state.symtab);
        print_register(&task.frame, &shared_state.symtab, "z_PC");
        print_register(&task.frame, &shared_state.symtab, "zR30");
        print_register(&task.frame, &shared_state.symtab, "zSP_EL3");
    }
}

fn print_register<B: BV>(frame: &Frame<B>, symtab: &Symtab, name: &str) {
    let x1 = symtab.get(name).unwrap();
    let val = frame.local_state.regs.get(&x1).unwrap();
    match val {
        UVal::Init(Val::Bits(bits)) => println!("{}={:#018X}", name, bits.lower_u64()),
        UVal::Init(Val::Struct(s)) => {
            let mut buf = format!("{}=\n", name);
            for (k, v) in s.iter() {
                buf.push_str(&format!("    .{} = {:?}\n", &symtab.to_str(*k), v));
            }
            println!("{}", &buf);
        },
        other => panic!("{} is not bits or struct: {:?}", name, other)
    }
}

fn read_register<B: BV>(frame: &Frame<B>, symtab: &Symtab, name:&str) -> u64 {
    let x1 = symtab.get(name).unwrap();
    let val = frame.local_state.regs.get(&x1).unwrap();
    match val {
        UVal::Init(Val::Bits(bits)) => bits.lower_u64(),
        other => panic!("{:?}", other)
    }
}

fn print_registers<B: BV>(frame: &Frame<B>, symtab: &Symtab) {
    for (reg_name, reg_val) in &frame.local_state.regs {
        println!("{:?}={:?}", symtab.to_str(*reg_name), reg_val)
    }
}
