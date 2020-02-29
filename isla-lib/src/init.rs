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

use std::collections::HashMap;
use std::sync::Mutex;

use crate::concrete::BV;
use crate::config::ISAConfig;
use crate::executor::{start_single, LocalFrame};
use crate::ir::*;
use crate::log;
use crate::zencode;

fn initialize_letbindings<'ir, B: BV>(
    arch: &'ir [Def<u32, B>],
    shared_state: &SharedState<'ir, B>,
    regs: &Bindings<'ir, B>,
    letbindings: &Mutex<Bindings<'ir, B>>,
) {
    for def in arch.iter() {
        if let Def::Let(bindings, setup) = def {
            let vars: Vec<_> = bindings.iter().map(|(id, ty)| (*id, ty)).collect();
            let task = {
                let lets = letbindings.lock().unwrap();
                LocalFrame::new(&vars, None, setup).add_regs(&regs).add_lets(&lets).task(0)
            };

            start_single(
                task,
                &shared_state,
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
    defs: &'ir [Def<u32, B>],
    initial_registers: &HashMap<u32, Val<B>>,
) -> Bindings<'ir, B> {
    let mut registers = HashMap::new();
    for def in defs.iter() {
        if let Def::Register(id, ty) = def {
            if let Some(value) = initial_registers.get(id) {
                registers.insert(*id, UVal::Init(value.clone()));
            } else {
                registers.insert(*id, UVal::Uninit(ty));
            }
        }
    }
    registers
}

pub struct Initialized<'ir, B> {
    pub regs: Bindings<'ir, B>,
    pub lets: Bindings<'ir, B>,
    pub shared_state: SharedState<'ir, B>,
}

pub fn initialize_architecture<'ir, B: BV>(
    arch: &'ir mut [Def<u32, B>],
    symtab: Symtab<'ir>,
    isa_config: &ISAConfig<B>,
    mode: AssertionMode,
) -> Initialized<'ir, B> {
    insert_monomorphize(arch);
    insert_primops(arch, mode);

    let regs = initialize_register_state(arch, &isa_config.default_registers);
    let lets = Mutex::new(HashMap::new());
    let shared_state = SharedState::new(symtab, arch, isa_config.probes.clone());

    initialize_letbindings(arch, &shared_state, &regs, &lets);

    Initialized { regs, lets: lets.into_inner().unwrap(), shared_state }
}
