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

use crate::bitvector::BV;
use crate::ir::*;
use crate::log;
use crate::simplify::{EventReferences, Taints};
use crate::smt::{Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;

/// Logs the taint info for a symbol, the set of registers that it's
/// value is derived from, and whether the value is derived from a
/// memory access. Note that computing this is relatively expensive,
/// so use of this should usually be done only in the event of an
/// error or guarded behind a flag.
///
/// This function can be called from a context without a SharedState
/// reference, so this argument is optional.
pub fn taint_info<B: BV>(log_type: u32, sym: Sym, shared_state: Option<&SharedState<B>>, solver: &Solver<B>) {
    let events = solver.trace().to_vec();
    let references = EventReferences::from_events(&events);

    let Taints { registers, memory } = references.taints(sym, &events);
    let registers: Vec<String> = registers
        .iter()
        .map(|(reg, _)| {
            if let Some(shared_state) = shared_state {
                let sym = shared_state.symtab.to_str(*reg);
                zencode::try_decode(sym).unwrap_or(sym.to_string())
            } else {
                format!("{:?}", reg)
            }
        })
        .collect();
    let memory = if memory { ", MEMORY" } else { "" };

    log!(log_type, &format!("Symbol {} taints: {:?}{}", sym, registers, memory))
}

pub fn args_info<B: BV>(tid: usize, args: &[Val<B>], shared_state: &SharedState<B>, solver: &Solver<B>) {
    let events = solver.trace().to_vec();
    let references = EventReferences::from_events(&events);

    for arg in args {
        for sym in arg.symbolic_variables() {
            let Taints { registers, memory } = references.taints(sym, &events);
            let registers: Vec<String> = registers
                .iter()
                .map(|(reg, _)| {
                    let sym = shared_state.symtab.to_str(*reg);
                    zencode::try_decode(sym).unwrap_or(sym.to_string())
                })
                .collect();
            let memory = if memory { ", MEMORY" } else { "" };
            log_from!(tid, log::PROBE, &format!("Symbol {} taints: {:?}{}", sym, registers, memory))
        }
    }
}

pub fn call_info<B: BV>(f: Name, args: &[Val<B>], shared_state: &SharedState<B>, info: SourceLoc) -> String {
    let symbol = zencode::decode(shared_state.symtab.to_str(f));
    format!(
        "Calling {}({:?}) at {}",
        symbol,
        args.iter().map(|arg| arg.to_string(shared_state)).collect::<Vec<String>>(),
        info.location_string(shared_state.symtab.files())
    )
}
