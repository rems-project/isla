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
use std::collections::HashMap;
use std::fs;

use crate::memory::Memory;
use crate::concrete::BV;

use elfloader::*;


fn step<B: 'static + BV>(
    task: isla_lib::executor::Task<B>,
    shared_state: &isla_lib::ir::SharedState<B>) -> Vec<executor::Task<B>> {
    println!("--------------- begin step -----------------------------");
    let queue = Arc::new(SegQueue::new());
    executor::start_multi(
        1,
        None,
        vec![task],
        shared_state,
        queue.clone(),
        &simple_collector,
    );
    let mut successors = vec!();
    loop {
        match queue.pop() {
            Ok(Ok((mut local_frame, checkpoint))) => {
                local_frame.pc = 0;
                let frame = executor::freeze_frame(&local_frame);
                successors.push(executor::Task {
                    id: 42,
                    frame: frame,
                    checkpoint: checkpoint,
                    fork_cond: None,
                    stop_functions: None
                });
            }
            Ok(Err((error, backtrace))) =>  {
                panic!("queue got error: {}", error.to_string(&backtrace, &shared_state));
                break
            }
            Err(_) => {
                break
            }
        }
    }
    println!("--------------- end step -------------------------------");
    //println!("{:?}", &queue);
    successors
}

fn main() {
    let now = Instant::now();
    let folder = PathBuf::from(r"C:\Users\Benni\repositories\master\verification\sail-arm\1166c197b127ed30d95421dcfa5fc59716aa1368");
    //let folder = PathBuf::from(r"C:\Users\Benni\Downloads\");
    //let folder = PathBuf::from(r"C:\Users\Benni\repositories\master-arm\aarch64");
    let config_file = folder.join("aarch64.toml");
    let symtab_file = folder.join("aarch64.symtab");
    let ir_file     = folder.join("aarch64.irx");

    let strings: Vec<String> = bincode::deserialize(&fs::read(&symtab_file).unwrap()).unwrap();
    let symtab = Symtab::from_raw_table(&strings);
    let mut ir: Vec<Def<Name, B64>> = ir_serialize::deserialize(&fs::read(&ir_file).unwrap()).expect("Failed to deserialize IR");
    let isa_config: ISAConfig<B64> = ISAConfig::parse(&fs::read_to_string(&config_file).unwrap(), &symtab).unwrap();
    println!("Loaded architecture in: {}ms", now.elapsed().as_millis());

    let Initialized { mut regs, lets, shared_state } = init::initialize_architecture(ir, symtab, &isa_config, AssertionMode::Optimistic);
    init::initialize_registers_arm64(&mut regs, &shared_state);

    let step_function_id = shared_state.symtab.lookup("zStep_CPU");
    let reset_function_id = shared_state.symtab.lookup("zTakeReset");
    let (reset_args, _, reset_instrs) = shared_state.functions.get(&reset_function_id).unwrap();
    let (_step_args, _, step_instrs) = shared_state.functions.get(&step_function_id).unwrap();

    let vals = vec!(Val::Bool(true));
    let mut lf: LocalFrame<B64> = LocalFrame::new(reset_function_id, reset_args, Some(&vals), reset_instrs.clone());
    lf.add_lets(&lets);
    lf.add_regs(&regs);
    let mem = lf.memory_mut();
    elf_loader::load_elf(r"C:\Users\Benni\repositories\isla_orig\isla-lib\router", mem);
    let mut task = lf.task(0);
    print_register(&task.frame, &shared_state.symtab, "zPSTATE");

    // cold reset device (TakeReset(true))
    task = execute_sail_function_no_fork(task, &shared_state);

    // prepare os emulation
    log::set_flags(0xffffffff);
    let mut lf = executor::unfreeze_frame(&task.frame);
    lf.regs_mut().insert(shared_state.symtab.lookup("z_PC"), UVal::Init(Val::Bits(B64::from_u64(0x0000000000215f38))));
    lf.function_name = step_function_id;
    lf.instrs = step_instrs.clone();
    init::reinitialize_registers_arm64(lf.regs_mut(), &shared_state);
    task.frame = executor::freeze_frame(&lf);

    // go!
    println!("starting execution");
    loop {
        task = execute_sail_function_no_fork(task, &shared_state);
        //print_registers(&task.frame, &shared_state.symtab);
        print_register(&task.frame, &shared_state.symtab, "z_PC");
        print_register(&task.frame, &shared_state.symtab, "zR30");
        print_register(&task.frame, &shared_state.symtab, "zSP_EL3");
    }
}

fn execute_sail_function_no_fork<B: 'static + BV>(task: executor::Task<B>, shared_state: &SharedState<B>) -> executor::Task<B> {
    let mut succs = step(task, &shared_state);
    if succs.len() > 1 {
        panic!("single_step_no_fork forked")
    }
    succs.remove(0)
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
        other => panic!("{} is not bits: {:?}", name, other)
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

pub type SimpleResultQueue<B> = SegQueue<Result<(LocalFrame<B>, Checkpoint<B>), (ExecError, Backtrace)>>;

fn simple_collector<B: BV>(
    _: usize,
    task_id: usize,
    result: Result<(Val<B>, LocalFrame<B>), (ExecError, Backtrace)>,
    shared_state: &SharedState<B>,
    mut solver: Solver<B>,
    collected: &SimpleResultQueue<B>,
) {
    match result {
        Ok((_, frame)) => {
            //println!("collector got frame: {:?}", shared_state.symtab.to_str(frame.function_name));
            collected.push(Ok((frame, smt::checkpoint(&mut solver))))
        },
        Err(e) => collected.push(Err(e))
    }
}

/// A simple ExampleLoader, that implements ElfLoader
/// but does nothing but logging
struct ExampleLoader<'ir, B: BV> {
    memory: &'ir mut Memory<B>
}

impl<'ir, B: BV> ElfLoader for ExampleLoader<'ir, B> {
    fn allocate(&mut self, load_headers: LoadableHeaders) -> Result<(), &'static str> {
        for header in load_headers {
            let base = header.virtual_addr();
            let end = base + header.mem_size();
            self.memory.add_concrete_region(base..end, HashMap::new());
            println!(
                "allocate base = {:#x} size = {:#x} flags = {}",
                header.virtual_addr(),
                header.mem_size(),
                header.flags()
            );
        }
        Ok(())
    }

    fn relocate(&mut self, _entry: &Rela<P64>) -> Result<(), &'static str> {
        unimplemented!()
    }

    fn load(&mut self, _flags: Flags, base: VAddr, region: &[u8]) -> Result<(), &'static str> {
        let start = base;
        let end = base + region.len() as u64;
        let mut i = 0;
        for b in region {
            self.memory.write_byte(start + i, *b);
            i += 1;
        }
        println!("load region into = {:#x} -- {:#x}", start, end);
        Ok(())
    }

    fn tls(
        &mut self,
        _tdata_start: VAddr,
        _tdata_length: u64,
        _total_size: u64,
        _align: u64
    ) -> Result<(), &'static str> {
        unimplemented!()
    }
}

pub fn load_elf<'ir, B: BV>(path: &str, memory: &'ir mut Memory<B>) {
    let binary_blob = fs::read(path).expect("Can't read binary");
    let binary = ElfBinary::new("test", binary_blob.as_slice()).expect("Got proper ELF file");
    let mut loader = ExampleLoader { memory: memory };
    binary.load(&mut loader).expect("Can't load the binary?");
}
