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

use crate::ir::*;
use crate::log;
use crate::simplify::EventReferences;
use crate::smt::Solver;
use crate::zencode;

pub fn args_info(tid: usize, args: &[Val], shared_state: &SharedState, solver: &Solver) {
    let events = solver.trace().to_vec();
    let references = EventReferences::from_events(&events);

    for arg in args {
        if let Val::Symbolic(sym) = arg {
            let (taints, memory) = references.taints(*sym, &events);
            let taints: Vec<String> =
                taints.iter().map(|(reg, _)| zencode::decode(shared_state.symtab.to_str(*reg))).collect();
            let memory = if memory { ", MEMORY" } else { "" };
            log_from!(tid, log::PROBE, &format!("Symbol {} taints: {:?}{}", sym, taints, memory))
        }
    }
}
