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

//! This module implements utilities for working with axiomatic memory
//! models.

use std::collections::HashMap;
use std::error::Error;
use std::fmt;

use isla_lib::concrete::BV;
use isla_lib::ir::{SharedState, Val};
use isla_lib::smt::{EvPath, Event};

pub type ThreadId = usize;

/// An iterator over candidate executions
pub struct Candidates<'ev, B> {
    index: Vec<usize>,
    max_index: Vec<usize>,
    threads: &'ev [Vec<EvPath<B>>],
    out_of_bounds: bool,
}

impl<'ev, B: BV> Candidates<'ev, B> {
    /// Create a candidate exeuction iterator from a slice containing
    /// vectors for each path through a thread.
    pub fn new(threads: &'ev [Vec<EvPath<B>>]) -> Self {
        Candidates {
            index: vec![0; threads.len()],
            max_index: threads.iter().map(|t| t.len()).collect(),
            threads,
            out_of_bounds: !threads.iter().all(|t| !t.is_empty()),
        }
    }

    pub fn total(&self) -> usize {
        if self.threads.is_empty() {
            0
        } else {
            self.max_index.iter().product()
        }
    }
}

fn increment_index(index: &mut [usize], max_index: &[usize], carry: usize) -> bool {
    if carry == index.len() {
        return true;
    }

    index[carry] += 1;
    if index[carry] == max_index[carry] {
        index[carry] = 0;
        increment_index(index, max_index, carry + 1)
    } else {
        false
    }
}

impl<'ev, B: BV> Iterator for Candidates<'ev, B> {
    type Item = Vec<&'ev [Event<B>]>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.out_of_bounds {
            None
        } else {
            let mut result = Vec::with_capacity(self.threads.len());
            self.threads.iter().zip(self.index.iter()).for_each(|(thread, i)| result.push(thread[*i].as_ref()));
            self.out_of_bounds = increment_index(&mut self.index, &self.max_index, 0);
            Some(result)
        }
    }
}

pub struct Pairs<'a, A> {
    index: (usize, usize),
    slice: &'a [A],
}

impl<'a, A> Pairs<'a, A> {
    pub fn from_slice(slice: &'a [A]) -> Self {
        Pairs { index: (0, 0), slice }
    }
}

impl<'a, A> Iterator for Pairs<'a, A> {
    type Item = (&'a A, &'a A);

    fn next(&mut self) -> Option<Self::Item> {
        self.index.1 += 1;
        if self.index.1 > self.slice.len() {
            self.index.1 = 1;
            self.index.0 += 1;
        }
        if self.index.0 >= self.slice.len() {
            return None;
        }
        Some((&self.slice[self.index.0], &self.slice[self.index.1 - 1]))
    }
}

/// An AxEvent (axiomatic event) is an event combined with metadata
/// about where and when it was executed in a candidate
/// execution. This can be combined with the footprint analysis to
/// determine various dependency orders on events.
#[derive(Debug)]
pub struct AxEvent<'a, B> {
    /// The opcode for the instruction that contained the underlying event
    pub opcode: B,
    /// The place of the event in po-order for it's thread
    pub po: usize,
    /// The thread id for the event
    pub thread_id: ThreadId,
    /// A generated unique name for the event
    pub name: String,
    /// The underlying event in the SMT trace
    pub base: &'a Event<B>,
}

impl<'a, B: BV> AxEvent<'a, B> {
    pub fn address(&self) -> Option<&'a Val<B>> {
        match self.base {
            Event::ReadMem { address, .. } | Event::WriteMem { address, .. } => Some(address),
            _ => None,
        }
    }

    pub fn read_value(&self) -> Option<(&'a Val<B>, u32)> {
        match self.base {
            Event::ReadMem { value, bytes, .. } => Some((value, *bytes)),
            _ => None,
        }
    }

    pub fn write_data(&self) -> Option<&'a Val<B>> {
        match self.base {
            Event::WriteMem { data, .. } => Some(data),
            _ => None,
        }
    }
}

pub mod relations {
    use std::collections::HashMap;

    use isla_lib::concrete::BV;

    use super::AxEvent;
    use crate::footprint_analysis::{addr_dep, ctrl_dep, data_dep, rmw_dep, Footprint};

    pub fn is_write<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base.is_memory_write()
    }

    pub fn is_read<B: BV>(ev: &AxEvent<B>) -> bool {
        ev.base.is_memory_read()
    }

    // TODO:
    pub fn amo<B: BV>(_ev1: &AxEvent<B>, _ev2: &AxEvent<B>) -> bool {
        false
    }

    pub fn univ<B: BV>(_: &AxEvent<B>, _: &AxEvent<B>) -> bool {
        true
    }

    pub fn disjoint<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po != ev2.po || ev1.thread_id != ev2.thread_id
    }

    pub fn po<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po < ev2.po && ev1.thread_id == ev2.thread_id
    }

    pub fn internal<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po != ev2.po && ev1.thread_id == ev2.thread_id
    }

    pub fn external<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>) -> bool {
        ev1.po != ev2.po && ev1.thread_id != ev2.thread_id
    }

    pub type DepRel<B> = fn(&AxEvent<B>, &AxEvent<B>, &[Vec<B>], &HashMap<B, Footprint>) -> bool;

    pub fn addr<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        po(ev1, ev2) && addr_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn data<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        po(ev1, ev2) && data_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn ctrl<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        po(ev1, ev2) && ctrl_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }

    pub fn rmw<B: BV>(
        ev1: &AxEvent<B>,
        ev2: &AxEvent<B>,
        thread_opcodes: &[Vec<B>],
        footprints: &HashMap<B, Footprint>,
    ) -> bool {
        po(ev1, ev2) && rmw_dep(ev1.po, ev2.po, &thread_opcodes[ev1.thread_id], footprints)
    }
}

pub struct ExecutionInfo<'ev, B> {
    /// A vector containing all the events in a candidate execution
    pub events: Vec<AxEvent<'ev, B>>,
    /// A vector of po-ordered instruction opcodes for each thread
    pub thread_opcodes: Vec<Vec<B>>,
    /// The final write for each register in each thread (if written at all)
    pub final_writes: HashMap<(u32, ThreadId), &'ev Val<B>>,
}

#[derive(Debug)]
pub enum CandidateError<B> {
    MultipleInstructionsInCycle { opcode1: B, opcode2: B },
    NoInstructionsInCycle,
    NoReadIFetch,
}

impl<B: BV> fmt::Display for CandidateError<B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use CandidateError::*;
        match self {
            MultipleInstructionsInCycle { opcode1, opcode2 } => write!(
                f,
                "A single fetch-execute-decode cycle in this candidate execution was associated with multiple instructions: {} and {}",
                opcode1,
                opcode2
            ),
            NoInstructionsInCycle => write!(
                f,
                "A fetch-execute-decode cycle was encountered that had no associated instructions"
            ),
            NoReadIFetch => write!(f, "No `Read_ifetch' read kind found in specified architecture!"),
        }
    }
}

impl<B: BV> Error for CandidateError<B> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

impl<'ev, B: BV> ExecutionInfo<'ev, B> {
    pub fn from(candidate: &'ev [&[Event<B>]], shared_state: &SharedState<B>) -> Result<Self, CandidateError<B>> {
        use CandidateError::*;
        let mut exec = ExecutionInfo {
            events: Vec::new(),
            thread_opcodes: vec![Vec::new(); candidate.len()],
            final_writes: HashMap::new(),
        };

        let rk_ifetch = match shared_state.enum_member("Read_ifetch") {
            Some(rk) => rk,
            None => return Err(NoReadIFetch),
        };

        for (tid, thread) in candidate.iter().enumerate() {
            for (po, cycle) in thread.split(|ev| ev.is_cycle()).skip(1).enumerate() {
                let mut cycle_events: Vec<(usize, String, &Event<B>)> = Vec::new();
                let mut cycle_instr: Option<B> = None;

                for (eid, event) in cycle.iter().enumerate() {
                    match event {
                        Event::Instr(Val::Bits(bv)) => {
                            if let Some(opcode) = cycle_instr {
                                return Err(MultipleInstructionsInCycle { opcode1: *bv, opcode2: opcode });
                            } else {
                                exec.thread_opcodes[tid].push(*bv);
                                cycle_instr = Some(*bv)
                            }
                        }
                        Event::ReadMem { .. } => cycle_events.push((tid, format!("R{}_{}_{}", po, eid, tid), event)),
                        Event::WriteMem { .. } => cycle_events.push((tid, format!("W{}_{}_{}", po, eid, tid), event)),
                        Event::Barrier { .. } => cycle_events.push((tid, format!("F{}_{}_{}", po, eid, tid), event)),
                        Event::WriteReg(reg, _, val) => {
                            exec.final_writes.insert((*reg, tid), val);
                        }
                        _ => (),
                    }
                }

                for (tid, evid, ev) in cycle_events {
                    // Events must be associated with an instruction
                    if let Some(opcode) = cycle_instr {
                        exec.events.push(AxEvent { opcode, po, thread_id: tid, name: evid, base: ev })
                    } else if !ev.has_read_kind(rk_ifetch) {
                        // Unless we have a single failing ifetch
                        return Err(NoInstructionsInCycle);
                    }
                }
            }
        }

        Ok(exec)
    }
}

/// This module defines utilites for parsing and interpreting the
/// models returned by Z3 when invoked on the command line.
pub mod model {
    use std::collections::HashMap;

    use isla_lib::concrete::BV;
    use isla_lib::ir::Val;

    use super::Pairs;
    use crate::sexp::{DefineFun, InterpretEnv, InterpretError, SexpFn, SexpVal};
    use crate::sexp_lexer::SexpLexer;
    use crate::sexp_parser::SexpParser;

    /// A model, as parsed from the SMT solver output, contains a list
    /// of function declarations (which can have arity 0 for
    /// constants) for each declare-const and declare-fun in the
    /// model. A model can also be parameterised by a set of
    /// events. The two lifetime parameters correspond to the
    /// underlying smtlib model `'s` and the events `'ev`.
    pub struct Model<'s, 'ev, B> {
        env: InterpretEnv<'s, 'ev, B>,
        functions: HashMap<&'s str, SexpFn<'s>>,
    }

    impl<'s, 'ev, B: BV> Model<'s, 'ev, B> {
        /// Parse a model from a string of the form (model (define-fun ...) (define-fun ...) ...)
        pub fn parse(events: &[&'ev str], model: &'s str) -> Option<Self> {
            let mut env = InterpretEnv::new();
            for event in events {
                env.add_event(event)
            }

            let lexer = SexpLexer::new(model);
            match SexpParser::new().parse(lexer) {
                Ok(sexp) => match sexp.dest_fn("model") {
                    Some(function_sexps) => {
                        let mut functions = HashMap::new();
                        for f in function_sexps {
                            if let Some(DefineFun { name, params, body, .. }) = f.dest_define_fun() {
                                let params = params.iter().map(|(a, _)| *a).collect();
                                functions.insert(name, SexpFn { params, body });
                            } else {
                                return None;
                            }
                        }
                        Some(Model { env, functions })
                    }
                    None => None,
                },
                Err(_) => None,
            }
        }

        /// Interprets a function in the model
        pub fn interpret(&mut self, f: &str, args: &[SexpVal<'ev, B>]) -> Result<SexpVal<'ev, B>, InterpretError> {
            let function = self.functions.get(f).ok_or_else(|| InterpretError::UnknownFunction(f.to_string()))?;

            self.env.add_args(&function.params, args)?;
            let result = function.body.interpret(&mut self.env, &self.functions)?;
            self.env.clear_args(&function.params);

            Ok(result)
        }

        /// Inteprets a relation (an Event * Event -> Bool function)
        /// over a set of events. Note that all events in this set
        /// must have been used to parameterise the model in
        /// Model::parse.
        pub fn interpret_rel(
            &mut self,
            rel: &str,
            events: &[&'ev str],
        ) -> Result<Vec<(&'ev str, &'ev str)>, InterpretError> {
            let mut pairs = Vec::new();

            for (ev1, ev2) in Pairs::from_slice(events) {
                match self.interpret(rel, &[SexpVal::Event(*ev1), SexpVal::Event(ev2)])? {
                    SexpVal::Bool(true) => pairs.push((*ev1, *ev2)),
                    SexpVal::Bool(false) => (),
                    _ => return Err(InterpretError::Type(rel.to_string())),
                }
            }

            Ok(pairs)
        }

        /// Interpret either a bitvector symbol in the model, or just
        /// return the bitvector directory if the val is concrete
        pub fn interpret_bits(&mut self, val: &Val<B>) -> Result<B, InterpretError> {
            match val {
                Val::Symbolic(v) => {
                    let smt_name = format!("v{}", v);
                    let sexp = self.interpret(&smt_name, &[])?;
                    sexp.into_bits().ok_or_else(|| InterpretError::NotFound(smt_name))
                }
                Val::Bits(bv) => Ok(*bv),
                _ => Err(InterpretError::Type("interpret_bv".to_string())),
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        use isla_lib::concrete::B64;

        #[test]
        fn test_parse() {
            let smtlib = "(model (define-fun v12331 () (_ BitVec 32) #x00000001))";
            Model::<B64>::parse(&[], smtlib).unwrap();
        }

        #[test]
        fn test_interpret_1() {
            let smtlib = "(model (define-fun dmb ((x!0 Event)) Bool false))";
            let ev = "R0";
            let mut model = Model::<B64>::parse(&[ev], smtlib).unwrap();
            let result = model.interpret("dmb", &[SexpVal::Event(ev)]).unwrap();
            assert_eq!(result, SexpVal::Bool(false));
        }

        #[test]
        fn test_interpret_2() {
            let smtlib = "(model (define-fun |0xdmb%| ((x!0 Event)) Bool false))";
            let ev = "R0";
            let mut model = Model::<B64>::parse(&[ev], smtlib).unwrap();
            let result = model.interpret("0xdmb%", &[SexpVal::Event(ev)]).unwrap();
            assert_eq!(result, SexpVal::Bool(false));
        }

        #[test]
        fn test_interpret_3() {
            let smtlib =
                "(model (define-fun |foo| ((x!0 Event)) Bool (let ((a!0 true)) (let ((a!0 false)) (and a!0)))))";
            let ev = "R0";
            let mut model = Model::<B64>::parse(&[ev], smtlib).unwrap();
            let result = model.interpret("foo", &[SexpVal::Event(ev)]).unwrap();
            assert_eq!(result, SexpVal::Bool(false));
        }

        #[test]
        fn test_interpret_4() {
            let smtlib = "(model (define-fun |foo| ((x!0 Event)) Bool (ite false true (not (= x!0 R0)))))";
            let ev = "R0";
            let mut model = Model::<B64>::parse(&[ev], smtlib).unwrap();
            let result = model.interpret("foo", &[SexpVal::Event(ev)]).unwrap();
            assert_eq!(result, SexpVal::Bool(false));
        }

        #[test]
        fn test_interpret_rel() {
            let smtlib = "(model (define-fun obs ((x!0 Event) (x!1 Event)) Bool
                            (or (and (= x!0 W0) (= x!1 R1))
                                (and (= x!0 IW) (= x!1 W0))
                                (and (= x!0 W1) (= x!1 R0))
                                (and (= x!0 IW) (= x!1 W1)))))";
            let evs = ["IW", "W0", "W1", "R0", "R1"];
            let mut model = Model::<B64>::parse(&evs, smtlib).unwrap();
            let result = model.interpret_rel("obs", &evs).unwrap();
            assert!(result.contains(&("W0", "R1")));
            assert!(result.contains(&("IW", "W0")));
            assert!(result.contains(&("W1", "R0")));
            assert!(result.contains(&("IW", "W1")));
            assert!(result.len() == 4);
        }
    }
}
