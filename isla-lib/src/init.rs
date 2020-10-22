// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
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

//! This module defines a function to initialize a Sail architecture
//! specification. The function [initialize_architecture] takes a
//! mutable reference to some parsed IR with it's symbols interned
//! into a [Symtab], and produces a [SharedState] struct, along with
//! [Bindings] environments for both the registers and the global let
//! bindings.
//!
//! The general flow to load and initialize a Sail specification is as
//! follows:
//!
//! * Load the architecture `.ir` file, containing the compiled _Jib_
//! IR produced by Sail.
//!
//! * Then create a symbol table and intern the IR symbols producing
//! new IR with identifiers of type [Name].
//!
//! * Next load the ISA configuration file to generate an
//! [ISAConfig]. This configuration can refer to symbols in the
//! architecture which is why we need to produce the symbol table
//! before loading this.
//!
//! * Finally use the [initialize_architecture] function in this
//! module to set up everything ready for symbolic execution.

use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::Arc;

use crate::concrete::BV;
use crate::config::ISAConfig;
use crate::executor::{start_single, LocalFrame};
use crate::ir::*;
use crate::log;
use crate::zencode;

fn initialize_letbindings<B: 'static + BV>(
    arch: Vec<Def<Name, B>>,
    shared_state: &SharedState<B>,
    regs: &Bindings<B>,
    letbindings: &Mutex<Bindings<B>>,
) {
    for def in &arch {
        if let Def::Let(bindings, setup) = def {
            let vars: Vec<_> = bindings.iter().map(|(id, ty)| (*id, Arc::new(ty.clone()))).collect();
            let mut frame = LocalFrame::new(TOP_LEVEL_LET, &*vars, None, setup.clone());
            {
                let lets = letbindings.lock().unwrap();
                frame.add_regs(&regs);
                frame.add_lets(&lets);
            }
            let task = frame.task(0);
            start_single(
                task,
                &shared_state,
                &letbindings,
                &move |_tid, _task_id, result, shared_state, _solver, letbindings| match result {
                    Ok((_, frame)) => {
                        for (id, _) in bindings.iter() {
                            let symbol = zencode::decode(&shared_state.symtab.to_str(*id));
                            match frame.vars().get(id) {
                                Some(value) => {
                                    let mut state = letbindings.lock().unwrap();
                                    state.insert(*id, value.clone());
                                    let symbol = zencode::decode(&shared_state.symtab.to_str(*id));
                                    log!(log::VERBOSE, &format!("{} = {:?}", symbol, value));
                                }
                                None => log!(log::VERBOSE, &format!("No value for symbol {}", symbol)),
                            }
                        }
                    }
                    Err(err) => log!(log::VERBOSE, &format!("Failed to evaluate letbinding: {:?}", err)),
                },
            );
        }
    }
}

fn initialize_register_state<B: BV>(
    defs: &mut [Def<Name, B>],
    initial_registers: &HashMap<Name, Val<B>>,
    symtab: &Symtab,
) -> Bindings<B> {
    let mut registers = HashMap::new();
    for def in defs.iter() {
        if let Def::Register(id, ty) = def {
            if let Some(value) = initial_registers.get(id) {
                value.plausible(ty, symtab).unwrap_or_else(|_| panic!("Bad initial value for {}", symtab.to_str(*id)));
                registers.insert(*id, UVal::Init(value.clone()));
            } else {
                registers.insert(*id, UVal::Uninit(Arc::new(ty.clone())));
            }
        }
    }
    registers
}

pub struct Initialized<B> {
    pub regs: Bindings<B>,
    pub lets: Bindings<B>,
    pub shared_state: SharedState<B>,
}


pub fn initialize_architecture<B: 'static + BV>(
    mut arch: Vec<Def<Name, B>>,
    symtab: Symtab,
    isa_config: &ISAConfig<B>,
    mode: AssertionMode,
) -> Initialized<B> {
    insert_monomorphize(&mut arch);
    insert_primops(&mut arch, mode);

    let regs = initialize_register_state(&mut arch, &isa_config.default_registers, &symtab);
    let lets = Mutex::new(HashMap::new());
    let shared_state = SharedState::new(symtab, &arch, isa_config.probes.clone());

    initialize_letbindings(arch, &shared_state, &regs, &lets);

    Initialized { regs, lets: lets.into_inner().unwrap(), shared_state }
}

pub fn initialize_registers_arm64<'ir, B: BV>(regs: &mut HashMap<Name, UVal<B>>, shared_state: &SharedState<B>) {
    regs.insert(shared_state.symtab.lookup("z_PC"), UVal::Init(Val::Bits(B::from_u64(0x0000000000215f38))));
    regs.insert(shared_state.symtab.lookup("zR14"), UVal::Init(Val::Bits(B::from_u64(0))));
    regs.insert(shared_state.symtab.lookup("zR29"), UVal::Init(Val::Bits(B::from_u64(0))));
    regs.insert(shared_state.symtab.lookup("zR30"), UVal::Init(Val::Bits(B::from_u64(0))));
    regs.insert(shared_state.symtab.lookup("zSP_EL0"), UVal::Init(Val::Bits(B::from_u64(0x10000))));
    regs.insert(shared_state.symtab.lookup("zSP_EL1"), UVal::Init(Val::Bits(B::from_u64(0x10000))));
    regs.insert(shared_state.symtab.lookup("zSP_EL2"), UVal::Init(Val::Bits(B::from_u64(0x10000))));
    regs.insert(shared_state.symtab.lookup("zSP_EL3"), UVal::Init(Val::Bits(B::from_u64(0x10000))));
    regs.insert(shared_state.symtab.lookup("zCNTKCTL_EL1"), UVal::Init(Val::Bits(B::new(0, 32))));
    regs.insert(shared_state.symtab.lookup("zMPIDR_EL1"), UVal::Init(Val::Bits(B::from_u64(0))));
    regs.insert(shared_state.symtab.lookup("zOSLSR_EL1"), UVal::Init(Val::Bits(B::new(0, 64))));        // lock stuff
    regs.insert(shared_state.symtab.lookup("zOSDLR_EL1"), UVal::Init(Val::Bits(B::new(0, 64))));        // double lock stuff
    regs.insert(shared_state.symtab.lookup("zCNTHCTL_EL2"), UVal::Init(Val::Bits(B::new(0, 32))));
    regs.insert(shared_state.symtab.lookup("zHCR_EL2"), UVal::Init(Val::Bits(B::from_u64(0))));
    regs.insert(shared_state.symtab.lookup("zSCTLR_EL3"), UVal::Init(Val::Bits(B::new(0, 64))));        // this is most likely invalid // is changed by reset
    regs.insert(shared_state.symtab.lookup("zSCR_EL3"), UVal::Init(Val::Bits(B::new(0, 32)))); // is changed by reset
    regs.insert(shared_state.symtab.lookup("zEDSCR"), UVal::Init(Val::Bits(B::new(0, 32)))); // is changed by reset to 0b000010 ("PE is in Non-debug state.")
    regs.insert(shared_state.symtab.lookup("z__defaultRAM"), UVal::Init(Val::Bits(B::new(4096, 56))));
    regs.insert(shared_state.symtab.lookup("zCNTCV"), UVal::Init(Val::Bits(B::new(0, 64))));
    // these are set in sail
    //regs.insert(shared_state.symtab.lookup("zCFG_ID_AA64PFR0_EL1_EL3"), UVal::Init(Val::Bits(B::new(2, 4))));
    //regs.insert(shared_state.symtab.lookup("zCFG_ID_AA64PFR0_EL1_EL2"), UVal::Init(Val::Bits(B::new(2, 4))));
    //regs.insert(shared_state.symtab.lookup("zCFG_ID_AA64PFR0_EL1_EL1"), UVal::Init(Val::Bits(B::new(2, 4))));
    //regs.insert(shared_state.symtab.lookup("zCFG_ID_AA64PFR0_EL1_EL0"), UVal::Init(Val::Bits(B::new(2, 4))));
    regs.insert(shared_state.symtab.lookup("z__highest_el_aarch32"), UVal::Init(Val::Bool(false)));
    regs.insert(shared_state.symtab.lookup("z_IRQPending"), UVal::Init(Val::Bool(false)));
    regs.insert(shared_state.symtab.lookup("z_FIQPending"), UVal::Init(Val::Bool(false)));
    regs.insert(shared_state.symtab.lookup("zDBGEN"), UVal::Init(Val::Enum(EnumMember { // DBGEN = LOW
        enum_id: 3,
        member: 0
    })));

    let mut pstate = HashMap::new();
    pstate.insert(shared_state.symtab.lookup("zN"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zZ"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zC"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zV"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zD"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zA"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zI"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zF"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zPAN"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zUAO"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zDIT"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zTCO"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zBTYPE"), Val::Bits(B::new(0, 2)));
    pstate.insert(shared_state.symtab.lookup("zSS"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zIL"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zEL"), Val::Bits(B::new(3, 2)));
    pstate.insert(shared_state.symtab.lookup("znRW"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zSP"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zQ"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zGE"), Val::Bits(B::new(0, 4)));
    pstate.insert(shared_state.symtab.lookup("zSSBS"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zIT"), Val::Bits(B::new(0, 8)));
    pstate.insert(shared_state.symtab.lookup("zJ"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zT"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zE"), Val::Bits(B::new(0, 1)));
    pstate.insert(shared_state.symtab.lookup("zM"), Val::Bits(B::new(0, 5)));
    regs.insert(shared_state.symtab.lookup("zPSTATE"), UVal::Init(Val::Struct(pstate)));

    regs.insert(shared_state.symtab.lookup("zID_AA64PFR0_EL1"), UVal::Init(Val::Bits(B::from_u64(0))));
    regs.insert(shared_state.symtab.lookup("zRMR_EL3"), UVal::Init(Val::Bits(B::from_u64(1))));
    regs.insert(shared_state.symtab.lookup("zCPTR_EL2"), UVal::Init(Val::Bits(B::from_u64(0)))); // Architectural Feature Trap Register
    regs.insert(shared_state.symtab.lookup("zCPTR_EL3"), UVal::Init(Val::Bits(B::from_u64(0))));
    regs.insert(shared_state.symtab.lookup("zDBGCLAIMCLR_EL1"), UVal::Init(Val::Bits(B::new(0, 32))));
    regs.insert(shared_state.symtab.lookup("zDBGCLAIMSET_EL1"), UVal::Init(Val::Bits(B::new(0, 32))));
}

pub fn reinitialize_registers_arm64<'ir, B: BV>(regs: &mut HashMap<Name, UVal<B>>, shared_state: &SharedState<B>) {
    regs.insert(shared_state.symtab.lookup("z_IRQPending"), UVal::Init(Val::Bool(false)));
    regs.insert(shared_state.symtab.lookup("z_FIQPending"), UVal::Init(Val::Bool(false)));
    regs.insert(shared_state.symtab.lookup("zSP_EL0"), UVal::Init(Val::Bits(B::from_u64(0x10000))));
    regs.insert(shared_state.symtab.lookup("zSP_EL1"), UVal::Init(Val::Bits(B::from_u64(0x10000))));
    regs.insert(shared_state.symtab.lookup("zSP_EL2"), UVal::Init(Val::Bits(B::from_u64(0x10000))));
    regs.insert(shared_state.symtab.lookup("zSP_EL3"), UVal::Init(Val::Bits(B::from_u64(0x10000))));
}
