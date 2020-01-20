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

use std::sync::Mutex;

use crate::ast::*;
use crate::executor;
use crate::executor::Frame;
use crate::log::*;
use crate::smt::Checkpoint;
use crate::zencode;

pub fn initialize_letbindings<'ir>(
    arch: &'ir [Def<u32>],
    shared_state: &SharedState<'ir>,
    regs: &Bindings<'ir>,
    letbindings: &Mutex<Bindings<'ir>>,
) {
    for def in arch.iter() {
        if let Def::Let(bindings, setup) = def {
            let vars: Vec<_> = bindings.iter().map(|(id, ty)| (*id, ty)).collect();
            let task = {
                let lets = letbindings.lock().unwrap();
                (Frame::new(&vars, regs.clone(), lets.clone(), setup), Checkpoint::new(), None)
            };

            executor::start_single(
                task,
                &shared_state,
                &letbindings,
                &move |_tid, result, shared_state, _solver, letbindings| match result {
                    Ok((_, frame)) => {
                        for (id, _) in bindings.iter() {
                            let symbol = zencode::decode(shared_state.symtab.to_str(*id));
                            match frame.vars.get(id) {
                                Some(value) => {
                                    let mut state = letbindings.lock().unwrap();
                                    state.insert(*id, value.clone());
                                    let symbol = zencode::decode(shared_state.symtab.to_str(*id));
                                    log_from(0, 0, &format!("{} = {:?}", symbol, value));
                                }
                                None => log_from(0, 0, &format!("No value for symbol {}", symbol)),
                            }
                        }
                    }
                    Err(err) => log_from(0, 0, &format!("Failed to evaluate letbinding: {:?}", err)),
                },
            );
        }
    }
}
