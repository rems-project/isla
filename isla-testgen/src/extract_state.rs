use std::collections::{HashMap, HashSet};

use isla_lib::concrete::B64;
use isla_lib::error::ExecError;
use isla_lib::ir;
use isla_lib::ir::Name;
use isla_lib::log;
use isla_lib::primop::smt_value;
use isla_lib::smt;
use isla_lib::smt::smtlib::Exp;
use isla_lib::smt::{Checkpoint, Event, Model, SmtResult, Solver};

fn get_model_val(model: &mut Model<B64>, val: &ir::Val<B64>) -> Result<Option<B64>, ExecError> {
    let exp = smt_value(val)?;
    match model.get_bv_exp(&exp)? {
        Some(Exp::Bits64(bits, length)) => Ok(Some(B64 { length, bits })),
        None => Ok(None),
        Some(exp) => Err(ExecError::Z3Error(format!("Bad model value {:?}", exp))),
    }
}

pub fn interrogate_model(
    checkpoint: Checkpoint<B64>,
    shared_state: &ir::SharedState<B64>,
    register_types: &HashMap<Name, ir::Ty<Name>>,
) -> Result<(), ExecError> {
    let cfg = smt::Config::new();
    cfg.set_param_value("model", "true");
    let ctx = smt::Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    match solver.check_sat() {
        SmtResult::Sat => (),
        SmtResult::Unsat => return Err(ExecError::Z3Error(String::from("Unsatisfiable at recheck"))),
        SmtResult::Unknown => return Err(ExecError::Z3Unknown),
    };

    let mut model = Model::new(&solver);
    log!(log::VERBOSE, format!("Model: {:?}", model));

    let mut events = isla_lib::simplify::simplify(solver.trace());
    let events: Vec<Event<B64>> = events.drain(..).map({ |ev| ev.clone() }).rev().collect();

    let mut initial_memory: HashMap<u64, u8> = HashMap::new();
    let mut touched_memory: HashSet<u64> = HashSet::new();
    // TODO: field accesses
    let mut initial_registers: HashMap<Name, B64> = HashMap::new();
    let mut touched_registers: HashSet<Name> = HashSet::new();

    // At the moment we assume that anything written in the
    // initialisation phase does not need to be initialised before the
    // test.  TODO: consider read/writes which just modify part of a
    // register, and later allowing initialised resources to be
    // modified by the test harness.
    let mut init_complete = false;

    for event in events {
        match &event {
            Event::ReadMem { value, read_kind: _, address, bytes } if init_complete => {
                let address = get_model_val(&mut model, address)?.expect("Arbitrary address");
                let val = get_model_val(&mut model, value)?;
                match val {
                    Some(val) => {
                        let vals = val.bits.to_le_bytes();
                        if 8 * *bytes == val.length {
                            for i in 0..*bytes {
                                if touched_memory.insert(address.bits) {
                                    initial_memory.insert(address.bits + i as u64, vals[i as usize]);
                                }
                            }
                        } else {
                            return Err(ExecError::Type("Memory read had wrong number of bytes"));
                        }
                    }
                    None => eprintln!("Ambivalent read of {} bytes from {:x}", bytes, address.bits),
                }
            }
            Event::WriteMem { value: _, write_kind: _, address, data: _, bytes } => {
                let address = get_model_val(&mut model, address)?.expect("Arbitrary address");
                for i in 0..*bytes {
                    touched_memory.insert(address.bits + i as u64);
                }
            }
            Event::ReadReg(reg, accessors, value) if init_complete => {
                if touched_registers.insert(*reg) {
                    if accessors.is_empty() {
                        match register_types.get(reg) {
                            Some(ir::Ty::Bits(sz)) if *sz <= 64 => match get_model_val(&mut model, value)? {
                                Some(val) => {
                                    initial_registers.insert(*reg, val);
                                }
                                None => eprintln!("Ambivalent read of register {}", shared_state.symtab.to_str(*reg)),
                            },
                            ty => eprintln!(
                                "Skipping read of {} due to unsupported type {:?}",
                                shared_state.symtab.to_str(*reg),
                                ty.unwrap()
                            ),
                        }
                    } else {
                        let fields: Vec<String> = accessors.iter().map(|a| a.to_string(&shared_state.symtab)).collect();
                        eprintln!(
                            "Skipping unsupported field read {} of register {}",
                            fields.join(","),
                            shared_state.symtab.to_str(*reg)
                        );
                    }
                }
            }
            Event::WriteReg(reg, accessors, _value) => {
                if touched_registers.insert(*reg) {
                    if !accessors.is_empty() {
                        let fields: Vec<String> = accessors.iter().map(|a| a.to_string(&shared_state.symtab)).collect();
                        eprintln!(
                            "Skipping unsupported field write {} to register {}",
                            fields.join(","),
                            shared_state.symtab.to_str(*reg)
                        );
                    }
                }
            }
            Event::Instr(_) => init_complete = true,
            _ => (),
        }
    }

    println!("Initial memory:");
    for (address, value) in &initial_memory {
        print!("{:08x}:{:02x} ", address, value);
    }
    println!("");
    print!("Initial registers: ");
    for (reg, value) in &initial_registers {
        print!("{}:{} ", shared_state.symtab.to_str(*reg), value);
    }
    println!("");

    Ok(())
}
