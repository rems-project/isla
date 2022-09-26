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

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use crate::bitvector::BV;
use crate::config::ISAConfig;
use crate::executor::{start_single, LocalFrame, TaskState};
use crate::ir::*;
use crate::log;
use crate::register::RegisterBindings;
use crate::zencode;

fn initialize_letbindings<'ir, B: BV>(
    arch: &'ir [Def<Name, B>],
    shared_state: &SharedState<'ir, B>,
    regs: &RegisterBindings<'ir, B>,
    letbindings: &Mutex<Bindings<'ir, B>>,
) {
    for def in arch.iter() {
        if let Def::Let(bindings, setup) = def {
            let vars: Vec<_> = bindings.iter().map(|(id, ty)| (*id, ty)).collect();
            let task_state = TaskState::new();
            let task = {
                let lets = letbindings.lock().unwrap();
                LocalFrame::new(TOP_LEVEL_LET, &vars, &Ty::Unit, None, setup).add_regs(regs).add_lets(&lets).task(0, &task_state)
            };

            start_single(
                task,
                shared_state,
                &letbindings,
                &move |_tid, _task_id, result, shared_state, _solver, letbindings| match result {
                    Ok((_, frame)) => {
                        for (id, _) in bindings.iter() {
                            let symbol = zencode::decode(shared_state.symtab.to_str(*id));
                            match frame.vars().get(id) {
                                Some(value) => {
                                    let mut state = letbindings.lock().unwrap();
                                    state.insert(*id, value.clone());
                                    let symbol = zencode::decode(shared_state.symtab.to_str(*id));
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

fn initialize_register_state<'ir, B: BV>(
    defs: &'ir [Def<Name, B>],
    initial_registers: &HashMap<Name, Val<B>>,
    relaxed_registers: &HashSet<Name>,
    symtab: &Symtab,
) -> RegisterBindings<'ir, B> {
    let mut registers = RegisterBindings::new();
    for def in defs.iter() {
        if let Def::Register(id, ty) = def {
            if let Some(value) = initial_registers.get(id) {
                value.plausible(ty, symtab).unwrap_or_else(|_| panic!("Bad initial value for {}", symtab.to_str(*id)));
                registers.insert(*id, relaxed_registers.contains(id), UVal::Init(value.clone()));
            } else {
                registers.insert(*id, relaxed_registers.contains(id), UVal::Uninit(ty));
            }
        }
    }
    registers
}

pub struct Initialized<'ir, B> {
    pub regs: RegisterBindings<'ir, B>,
    pub lets: Bindings<'ir, B>,
    pub shared_state: SharedState<'ir, B>,
}

pub fn initialize_architecture<'ir, B: BV>(
    arch: &'ir mut [Def<Name, B>],
    symtab: Symtab<'ir>,
    isa_config: &ISAConfig<B>,
    mode: AssertionMode,
) -> Initialized<'ir, B> {
    insert_monomorphize(arch);
    insert_primops(arch, mode);

    let regs = initialize_register_state(arch, &isa_config.default_registers, &isa_config.relaxed_registers, &symtab);
    let lets = Mutex::new(HashMap::default());
    let shared_state = SharedState::new(
        symtab,
        arch,
        isa_config.probes.clone(),
        isa_config.trace_functions.clone(),
        isa_config.reset_registers.clone(),
        isa_config.reset_constraints.clone(),
    );

    initialize_letbindings(arch, &shared_state, &regs, &lets);

    Initialized { regs, lets: lets.into_inner().unwrap(), shared_state }
}
