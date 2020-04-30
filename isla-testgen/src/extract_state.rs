use std::collections::{HashMap, HashSet};
use std::iter;
use std::ops::Range;

use isla_lib::concrete::B64;
use isla_lib::error::ExecError;
use isla_lib::ir;
use isla_lib::ir::Name;
use isla_lib::log;
use isla_lib::memory;
use isla_lib::primop::smt_value;
use isla_lib::smt;
use isla_lib::smt::smtlib::Exp;
use isla_lib::smt::{Checkpoint, Event, Accessor, Model, SmtResult, Solver};

fn get_model_val(model: &mut Model<B64>, val: &ir::Val<B64>) -> Result<Option<B64>, ExecError> {
    let exp = smt_value(val)?;
    match model.get_exp(&exp)? {
        Some(Exp::Bits64(bits, length)) => Ok(Some(B64 { length, bits })),
        None => Ok(None),
        Some(exp) => Err(ExecError::Z3Error(format!("Bad model value {:?}", exp))),
    }
}

pub struct InitialState {
    pub memory: Vec<(Range<memory::Address>, Vec<u8>)>,
    pub code: Vec<(Range<memory::Address>, Vec<u8>)>,
    pub gprs: Vec<(u32, u64)>,
    pub nzcv: u32,
}

fn regacc_to_str(shared_state: &ir::SharedState<B64>, regacc: &(Name, Vec<Accessor>)) -> String {
    let (reg,acc) = regacc;
    let reg_str = shared_state.symtab.to_str(*reg);
    let fields =
        acc.iter().map(|Accessor::Field(a)| shared_state.symtab.to_str(*a));
    let parts: Vec<&str> = iter::once(reg_str).chain(fields).collect();
    parts.join(".")
}

fn apply_accessors(shared_state: &ir::SharedState<B64>, start_ty: &ir::Ty<Name>, accessors: &Vec<Accessor>, start_value: &ir::Val<B64>) -> (ir::Ty<Name>, ir::Val<B64>) {
    let mut ty = start_ty;
    let mut value = start_value;
    for Accessor::Field(field) in accessors {
        match ty {
            ir::Ty::Struct(name) => {
                ty = shared_state.structs.get(&name).unwrap().get(&field).unwrap();
                match value {
                    ir::Val::Struct(field_vals) => value = field_vals.get(&field).unwrap(),
                    _ => panic!("Bad value for struct {:?}", value)
                }
            }
            _ => panic!("Bad type for struct {:?}", ty)
        }
    }
    (ty.clone(), value.clone())
}

fn iter_b64_types<F,G,T>
    (shared_state: &ir::SharedState<B64>, f: &mut F, g: &mut G, ty: &ir::Ty<Name>, accessors: &mut Vec<Accessor>, v: &ir::Val<B64>, r: &mut T)
where F: FnMut(u32, &Vec<Accessor>, &ir::Val<B64>, &mut T), G: FnMut(&ir::Ty<Name>, &Vec<Accessor>, &ir::Val<B64>, &mut T)
{
    match ty {
        ir::Ty::Bits(sz) if *sz <= 64 => f(*sz, accessors, v, r),
        ir::Ty::Struct(name) => {
            match v {
                ir::Val::Struct(field_vals) => {
                    let fields = shared_state.structs.get(name).unwrap();
                    for (field, ty) in fields {
                        accessors.push(Accessor::Field(*field));
                        iter_b64_types(shared_state, f, g, ty, accessors, field_vals.get(field).unwrap(), r);
                        accessors.pop();
                    }
                }
                _ => panic!("Struct type, non-struct value {:?}", v)
            }
        }
        _ => g(ty, accessors, v, r)
    }
}

pub fn interrogate_model(
    checkpoint: Checkpoint<B64>,
    shared_state: &ir::SharedState<B64>,
    register_types: &HashMap<Name, ir::Ty<Name>>,
    symbolic_regions: &[Range<memory::Address>],
    symbolic_code_regions: &[Range<memory::Address>],
) -> Result<InitialState, ExecError> {
    let cfg = smt::Config::new();
    cfg.set_param_value("model", "true");
    let ctx = smt::Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    match solver.check_sat() {
        SmtResult::Sat => (),
        SmtResult::Unsat => return Err(ExecError::Z3Error(String::from("Unsatisfiable at recheck"))),
        SmtResult::Unknown => return Err(ExecError::Z3Unknown),
    };

    // The events in the processor initialisation aren't relevant, so we take
    // them from the first instruction fetch.
    let read_kind_name = shared_state.symtab.get("zRead_ifetch").expect("Read_ifetch missing");
    let (read_kind_pos, read_kind_size) = shared_state.enum_members.get(&read_kind_name).unwrap();
    let read_kind_id = solver.get_enum(*read_kind_size);

    let mut model = Model::new(&solver);
    log!(log::VERBOSE, format!("Model: {:?}", model));

    let mut events = isla_lib::simplify::simplify(solver.trace());
    let events: Vec<Event<B64>> = events.drain(..).map({ |ev| ev.clone() }).rev().collect();

    let mut initial_memory: HashMap<u64, u8> = HashMap::new();
    let mut current_memory: HashMap<u64, Option<u8>> = HashMap::new();
    // TODO: field accesses
    let mut initial_registers: HashMap<(Name, Vec<Accessor>), B64> = HashMap::new();
    let mut current_registers: HashMap<(Name, Vec<Accessor>), (bool, Option<B64>)> = HashMap::new();
    let mut skipped_register_reads: HashSet<(Name, Vec<Accessor>)> = HashSet::new();

    // TODO: consider read/writes which just modify part of a
    // register, and later allowing initialised resources to be
    // modified by the test harness.
    let mut init_complete = false;

    let is_ifetch = |val: &ir::Val<B64>| match val {
        ir::Val::Enum(ir::EnumMember { enum_id, member }) => *enum_id == read_kind_id && *member == *read_kind_pos,
        _ => false,
    };

    for event in events {
        match &event {
            Event::ReadMem { value, read_kind, address, bytes } if init_complete || is_ifetch(read_kind) => {
                init_complete = true;
                let address = get_model_val(&mut model, address)?.expect("Arbitrary address");
                let val = get_model_val(&mut model, value)?;
                match val {
                    Some(val) => {
                        let vals = val.bits.to_le_bytes();
                        if 8 * *bytes == val.length {
                            for i in 0..*bytes {
                                let byte_address = address.bits + i as u64;
                                let byte_val = vals[i as usize];
                                if current_memory.insert(byte_address, Some(byte_val)).is_none() {
                                    initial_memory.insert(byte_address, byte_val);
                                }
                            }
                        } else {
                            return Err(ExecError::Type("Memory read had wrong number of bytes"));
                        }
                    }
                    None => eprintln!("Ambivalent read of {} bytes from {:x}", bytes, address.bits),
                }
            }
            Event::WriteMem { value: _, write_kind: _, address, data, bytes } => {
                let address = get_model_val(&mut model, address)?.expect("Arbitrary address");
                let val = get_model_val(&mut model, data)?;
                match val {
                    Some(val) => {
                        let vals = val.bits.to_le_bytes();
                        for i in 0..*bytes {
                            current_memory.insert(address.bits + i as u64, Some(vals[i as usize]));
                        }
                    }
                    None => {
                        eprintln!("Ambivalent write of {} bytes to {:x}", bytes, address.bits);
                        for i in 0..*bytes {
                            current_memory.insert(address.bits + i as u64, None);
                        }
                    }
                }
            }
            Event::ReadReg(reg, accessors, value) if init_complete => {
                let mut process_read_bits64 = |_sz: u32, accessors: &Vec<Accessor>, value: &ir::Val<B64>, skipped: &mut HashSet<_>| {
                    let key = (*reg, accessors.clone());
                    if skipped.contains(&key) { return () };
                    let val = get_model_val(&mut model, value).expect("get_model_val");
                    if let None = current_registers.insert(key.clone(), (true, val)) {
                        match val {
                            Some(val) => {
                                initial_registers.insert(key, val);
                            }
                            None => {
                                eprintln!("Ambivalent read of register {}", regacc_to_str(shared_state, &key))
                            }
                        }
                    }
                };
                let mut process_read_unsupported = |ty: &ir::Ty<Name>, accessors: &Vec<Accessor>, value: &ir::Val<B64>, skipped: &mut HashSet<_>| {
                    let key = (*reg, accessors.clone());
                    if skipped.contains(&key) { return () };
                    eprintln!(
                        "Skipping read of {} with value {:?} due to unsupported type {:?}",
                        regacc_to_str(shared_state, &key),
                        value,
                        ty
                    );
                    skipped.insert(key);
                };
                match register_types.get(reg) {
                    Some(ty) => {
                        let (read_ty, read_value) = apply_accessors(shared_state, ty, accessors, &value);
                        iter_b64_types(shared_state, &mut process_read_bits64, &mut process_read_unsupported, &read_ty, &mut accessors.clone(), &read_value, &mut skipped_register_reads)
                    }
                    None => panic!("Missing type for register {}", shared_state.symtab.to_str(*reg)),
                }
            }
            Event::WriteReg(reg, accessors, value) => {
                let mut process_write = |_sz : u32, accessors: &Vec<Accessor>, value: &ir::Val<B64>, _: &mut ()| {
                    let val = get_model_val(&mut model, value).expect("get_model_val");
                    current_registers.insert((*reg, accessors.clone()), (init_complete, val));
                };
                let mut process_unsupported = |_ty: &ir::Ty<Name>, _accessors: &Vec<Accessor>, _value: &ir::Val<B64>, _: &mut ()| { () };
                match register_types.get(reg) {
                    Some(ty) => {
                        let (assigned_ty, assigned_value) = apply_accessors(shared_state, ty, accessors, &value);
                        iter_b64_types(shared_state, &mut process_write, &mut process_unsupported, &assigned_ty, &mut accessors.clone(), &assigned_value, &mut ())
                    }
                    None => panic!("Missing type for register {}", shared_state.symtab.to_str(*reg)),
                }
            },
            Event::Instr(_) if !init_complete => {
                // We should see the instruction fetch first and look
                // at events from then on
                eprintln!("Instruction announced without an ifetch");
                init_complete = true;
            }
            _ => (),
        }
    }

    println!("Initial memory:");
    for (address, value) in &initial_memory {
        print!("{:08x}:{:02x} ", address, value);
    }
    println!("");
    print!("Initial registers: ");
    for (regacc, value) in &initial_registers {
        print!("{}:{} ", regacc_to_str(shared_state, regacc), value);
    }
    println!("");

    println!("Final memory:");
    for (address, value) in &current_memory {
        match value {
            Some(val) => print!("{:08x}:{:02x} ", address, val),
            None => print!("{:08x}:?? ", address),
        }
    }
    println!("");
    print!("Final registers: ");
    for (regacc, (post_init, value)) in &current_registers {
        if *post_init {
            match value {
                Some(val) => print!("{}:{} ", regacc_to_str(shared_state, regacc), val),
                None => print!("{}:?? ", regacc_to_str(shared_state, regacc)),
            }
        }
    }
    println!("");

    let mut initial_symbolic_memory : Vec<(Range<memory::Address>, Vec<u8>)> =
        symbolic_regions.iter()
        .map(|r| (r.clone(), vec![0; (r.end - r.start) as usize]))
        .collect();

    let mut initial_symbolic_code_memory : Vec<(Range<memory::Address>, Vec<u8>)> =
        symbolic_code_regions.iter()
        .map(|r| (r.clone(), vec![0; (r.end - r.start) as usize]))
        .collect();

    for (address, value) in &initial_memory {
        for (r,v) in &mut initial_symbolic_memory {
            if r.contains(address) {
                v[(address - r.start) as usize] = *value;
                break;
            }
        }
        for (r,v) in &mut initial_symbolic_code_memory {
            if r.contains(address) {
                v[(address - r.start) as usize] = *value;
                break;
            }
        }
    }

    let mut gprs = Vec::new();
    let mut nzcv = 0u32;
    for ((reg, accessor), value) in &initial_registers {
        let name = shared_state.symtab.to_str(*reg);
        if name.starts_with("zR") {
            let reg_str = &name[2..];
            if let Ok(reg_num) = u32::from_str_radix(reg_str, 10) {
                gprs.push((reg_num, value.bits));
            }
        } else if name == "zPSTATE" {
            if let &[Accessor::Field(id)] = accessor.as_slice() {
                match shared_state.symtab.to_str(id) {
                    "zN" => nzcv |= (value.bits as u32) << 3,
                    "zZ" => nzcv |= (value.bits as u32) << 2,
                    "zC" => nzcv |= (value.bits as u32) << 1,
                    "zV" => nzcv |=  value.bits as u32,
                    _ => ()
                }
            }
        }
    }

    Ok(InitialState { memory: initial_symbolic_memory, code: initial_symbolic_code_memory, gprs, nzcv })
}
