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
//!   IR produced by Sail.
//!
//! * Then create a symbol table and intern the IR symbols producing
//!   new IR with identifiers of type [Name].
//!
//! * Next load the ISA configuration file to generate an
//!   [ISAConfig]. This configuration can refer to symbols in the
//!   architecture which is why we need to produce the symbol table
//!   before loading this.
//!
//! * Finally use the [initialize_architecture] function in this
//!   module to set up everything ready for symbolic execution.

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use crate::bitvector::BV;
use crate::config::ISAConfig;
use crate::executor::start_single;
use crate::executor::{LocalFrame, TaskId, TaskState};
use crate::ir::*;
use crate::log;
use crate::register::RegisterBindings;
use crate::zencode;

fn initialize_letbinding<'ir, B: BV>(
    bindings: &'ir [(Name, Ty<Name>)],
    setup: &'ir [Instr<Name, B>],
    shared_state: &SharedState<'ir, B>,
    registers: &Mutex<RegisterBindings<'ir, B>>,
    letbindings: &Mutex<Bindings<'ir, B>>,
) {
    let vars: Vec<_> = bindings.iter().map(|(id, ty)| (*id, ty)).collect();
    let task_state = TaskState::new();
    let task = {
        let regs = registers.lock().unwrap();
        let lets = letbindings.lock().unwrap();
        LocalFrame::new(TOP_LEVEL_LET, &vars, &Ty::Unit, None, setup)
            .add_regs(&regs)
            .add_lets(&lets)
            .task(TaskId::fresh(), &task_state)
    };

    start_single(
        task,
        shared_state,
        &letbindings,
        &move |_tid, _task_id, result, shared_state, _solver, letbindings| match result {
            Ok((_, frame)) => {
                for (id, _) in bindings.iter() {
                    match frame.vars().get(id) {
                        Some(value) => {
                            let mut state = letbindings.lock().unwrap();
                            state.insert(*id, value.clone());
                        }
                        None => {
                            let symbol = zencode::decode(shared_state.symtab.to_str(*id));
                            log!(log::VERBOSE, &format!("No value for symbol {}", symbol))
                        }
                    }
                }
            }
            Err(err) => log!(log::VERBOSE, &format!("Failed to evaluate letbinding: {:?}", err)),
        },
    );
}

fn initialize_register<'ir, B: BV>(
    id: &Name,
    ty: &'ir Ty<Name>,
    setup: &'ir [Instr<Name, B>],
    shared_state: &SharedState<'ir, B>,
    initial_registers: &HashMap<Name, Val<B>>,
    relaxed_registers: &HashSet<Name>,
    use_model_init: bool,
    registers: &Mutex<RegisterBindings<'ir, B>>,
    letbindings: &Mutex<Bindings<'ir, B>>,
) {
    if let Some(value) = initial_registers.get(id) {
        // The value parser doesn't know what integer size to use, so correct it if necessary
        let value = match (value, ty) {
            (Val::I128(i), Ty::I64) => Val::I64(
                i64::try_from(*i)
                    .unwrap_or_else(|err| panic!("Bad initial value for {}: {}", shared_state.symtab.to_str(*id), err)),
            ),
            (v, _) => v.clone(),
        };
        value
            .plausible(ty, shared_state)
            .unwrap_or_else(|err_msg| panic!("Bad initial value for {}: {}", shared_state.symtab.to_str(*id), err_msg));
        let mut regs = registers.lock().unwrap();
        regs.insert(*id, relaxed_registers.contains(id), UVal::Init(value));
    } else {
        {
            let mut regs = registers.lock().unwrap();
            regs.insert(*id, relaxed_registers.contains(id), UVal::Uninit(ty));
        }

        if use_model_init {
            let task_state = TaskState::new();
            let task = {
                let lets = letbindings.lock().unwrap();
                let regs = registers.lock().unwrap();
                LocalFrame::new(REGISTER_INIT, &[], &Ty::Unit, None, setup)
                    .add_regs(&regs)
                    .add_lets(&lets)
                    .task(TaskId::fresh(), &task_state)
            };

            start_single(
                task,
                shared_state,
                &(),
                &move |_tid, _task_id, result, _shared_state, _solver, _| match result {
                    Ok((_, frame)) => {
                        if let Some(v) = frame.regs().get_last_if_initialized(*id) {
                            let mut regs = registers.lock().unwrap();
                            regs.insert(*id, relaxed_registers.contains(id), UVal::Init(v.clone()))
                        }
                    }
                    Err(err) => log!(log::VERBOSE, &format!("Failed to evaluate register initialiser: {:?}", err)),
                },
            );
        }
    }
}

pub struct Initialized<'ir, B> {
    pub regs: RegisterBindings<'ir, B>,
    pub lets: Bindings<'ir, B>,
    pub shared_state: SharedState<'ir, B>,
}

/// Initialize an architecture for symbolic execution, producing an
/// `Initialized` struct containing a `SharedState` for symbolic
/// execution threads, and initial values for registers and global
/// letbindings.
///
/// # Arguments
///
/// * `arch` - The Sail Jib IR definitions for the architecture
/// * `symtab` - Sail symbol name information
/// * `isa_config` - The ISA configuration file (see the examples in the config/ subdirectory)
/// * `mode` - How assertions are treated in the model
/// * `use_model_register_init` - If true we will use the initial value
///   of registers from register bindings such as
///
///   ```sail
///   register R : T = value
///   ```
///
///   Often we don't want to do this as we are assuming we are
///   executing at some arbitrary point in time, and therefore don't
///   want to fix initial values.
pub fn initialize_architecture<'ir, B: BV>(
    arch: &'ir mut [Def<Name, B>],
    symtab: Symtab<'ir>,
    type_info: IRTypeInfo,
    isa_config: &ISAConfig<B>,
    mode: AssertionMode,
    use_model_register_init: bool,
) -> Initialized<'ir, B> {
    insert_monomorphize(arch);
    insert_primops(arch, mode, isa_config);

    let shared_state = SharedState::new(
        symtab,
        arch,
        type_info,
        isa_config.probes.clone(),
        isa_config.probe_functions.clone(),
        isa_config.trace_functions.clone(),
        isa_config.reset_registers.clone(),
        isa_config.reset_constraints.clone(),
        isa_config.function_assumptions.clone(),
    );

    let lets = Mutex::new(HashMap::default());
    let regs = Mutex::new(RegisterBindings::new());

    for def in arch.iter() {
        match def {
            Def::Let(bindings, setup) => initialize_letbinding(bindings, setup, &shared_state, &regs, &lets),
            Def::Register(id, ty, setup) => initialize_register(
                id,
                ty,
                setup,
                &shared_state,
                &isa_config.default_registers,
                &isa_config.relaxed_registers,
                use_model_register_init,
                &regs,
                &lets,
            ),
            _ => (),
        }
    }

    Initialized { regs: regs.into_inner().unwrap(), lets: lets.into_inner().unwrap(), shared_state }
}

#[derive(Clone)]
pub struct InitArchWithConfig<'ir, B> {
    pub regs: &'ir RegisterBindings<'ir, B>,
    pub lets: &'ir Bindings<'ir, B>,
    pub shared_state: &'ir SharedState<'ir, B>,
    pub isa_config: &'ir ISAConfig<B>,
}

impl<'ir, B> InitArchWithConfig<'ir, B>
where
    B: BV,
{
    pub fn from_initialized(
        iarch: &'ir Initialized<'ir, B>,
        isa_config: &'ir ISAConfig<B>,
    ) -> InitArchWithConfig<'ir, B> {
        InitArchWithConfig { regs: &iarch.regs, lets: &iarch.lets, shared_state: &iarch.shared_state, isa_config }
    }
}
