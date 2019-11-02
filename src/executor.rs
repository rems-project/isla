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

use crossbeam::deque::Worker;
use std::collections::HashMap;
use std::sync::Arc;

use crate::ast::*;
use isla_smt::*;

#[derive(Clone)]
enum Var {
    Uninitialized,
    Symbolic(u32),
}

fn eval_exp(exp: &Exp<u32>, vars: &HashMap<u32, Var>, solver: &mut Solver) -> Var {
    Var::Uninitialized
}

fn assign(loc: &Loc<u32>, v: Var, vars: &mut HashMap<u32, Var>, solver: &mut Solver) {
    ()
}

struct Frame<'ast> {
    pc: usize,
    backjumps: u32,
    vars: Arc<HashMap<u32, Var>>,
    globals: Arc<HashMap<u32, Var>>,
    instrs: &'ast [Instr<u32>],
    stack: Option<Arc<dyn 'ast + Fn(Var, &mut LocalFrame<'ast>, &mut Solver) -> ()>>,
}

struct LocalFrame<'ast> {
    pc: usize,
    backjumps: u32,
    vars: HashMap<u32, Var>,
    globals: HashMap<u32, Var>,
    instrs: &'ast [Instr<u32>],
    stack: Option<Arc<dyn 'ast + Fn(Var, &mut LocalFrame<'ast>, &mut Solver) -> ()>>,
}

fn unfreeze_frame<'ast>(frame: &Frame<'ast>) -> LocalFrame<'ast> {
    LocalFrame {
        pc: frame.pc,
        backjumps: frame.backjumps,
        vars: (*frame.vars).clone(),
        globals: (*frame.globals).clone(),
        instrs: frame.instrs,
        stack: frame.stack.clone(),
    }
}

fn freeze_frame<'ast>(frame: &LocalFrame<'ast>) -> Frame<'ast> {
    Frame {
        pc: frame.pc,
        backjumps: frame.backjumps,
        vars: Arc::new(frame.vars.clone()),
        globals: Arc::new(frame.globals.clone()),
        instrs: frame.instrs,
        stack: frame.stack.clone(),
    }
}

fn run<'ast>(
    tid: usize,
    queue: &Worker<(Frame<'ast>, Checkpoint)>,
    frame: &Frame<'ast>,
    checkpoint: Checkpoint,
    shared_state: &'ast SharedState,
) {
    // First, set up a solver instance for the frame's SMT checkpoint.
    let cfg = Config::new();
    let ctx = Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    // Now create a local mutable version of the frame for us to
    // execute with
    let mut frame = unfreeze_frame(frame);

    loop {
        match &frame.instrs[frame.pc] {
            Instr::Decl(v, _ty) => {
                frame.vars.insert(*v, Var::Uninitialized);
                frame.pc += 1;
            }

	    Instr::Init(var, _, exp) => {
		let value = eval_exp(exp, &frame.vars, &mut solver);
		frame.vars.insert(*var, value); 
		frame.pc += 1;
	    }

            Instr::Goto(target) => {
                frame.pc = *target
            }

	    Instr::Copy(loc, exp) => {
		let value = eval_exp(exp, &frame.vars, &mut solver);
		assign(loc, value, &mut frame.vars, &mut solver);
		frame.pc += 1;
	    }

            Instr::Call(loc, _, f, _) => {
                match shared_state.functions.get(&f) {
                    None => {
                        let symbol = shared_state.symtab.to_str(*f);
                        panic!(
                            "Attempted to call non-existent function {} ({})",
                            symbol, *f
                        )
                    }
                    Some((args, _, instrs)) => {
                        let caller = freeze_frame(&frame);
                        // Set up a closure to restore our state when
                        // the function we call returns
                        frame.stack = Some(Arc::new(move |ret, frame, solver| {
                            frame.pc = caller.pc + 1;
                            frame.vars = (*caller.vars).clone();
                            frame.instrs = caller.instrs;
                            frame.stack = caller.stack.clone();
			    assign(loc, ret, &mut frame.vars, solver)
                        }));
                        frame.pc = 0;
                        frame.instrs = instrs;
                    }
                }
            }

            Instr::End => {
                let caller = match &frame.stack {
                    None => return (),
                    Some(caller) => caller.clone(),
                };
                match frame.vars.get(&RETURN) {
                    None => panic!("Reached end without assigning to return"),
                    Some(value) => (*caller)(value.clone(), &mut frame, &mut solver),
                }
            }

            _ => (),
        }
    }
    ()
}
