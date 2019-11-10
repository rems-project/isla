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
use crate::log::*;
use isla_smt::*;

fn symbolic(ty: &Ty<u32>, solver: &mut Solver) -> u32 {
    let smt_ty = match ty {
        Ty::Bool => smtlib::Ty::Bool,
        Ty::I64 => smtlib::Ty::BitVec(64),
        Ty::I128 => smtlib::Ty::BitVec(128),
	Ty::Fbits(sz) => smtlib::Ty::BitVec(*sz),
        _ => panic!("Cannot convert type"),
    };
    let sym = solver.fresh();
    solver.add(smtlib::Def::DeclareConst(sym, smt_ty));
    sym
}

fn get_and_initialize<'ast>(v: u32, vars: &HashMap<u32, Val<'ast>>, solver: &mut Solver) -> Option<Val<'ast>> {
    match vars.get(&v) {
        Some(Val::Uninitialized(ty)) => Some(Val::Symbolic(symbolic(ty, solver))),
        Some(value) => Some(value.clone()),
        None => None,
    }
}

fn cast<'ast>(to: &'ast Ty<u32>, from: &Ty<u32>, value: Val<'ast>, solver: &mut Solver) -> Val<'ast> {
    match (to, from) {
	(Ty::I64, Ty::I128) => {
	    match value {
		Val::I128(i) => Val::I64(i as i64),
		_ => panic!("Type error in cast")
	    }
	}
	(Ty::I128, Ty::I64) => {
	    match value {
		Val::I64(i) => Val::I128(i as i128),
		_ => panic!("Type error in cast")
	    }
	}
	_ => Val::Uninitialized(to)
    }
}

fn eval_exp<'ast>(
    exp: &Exp<u32>,
    vars: &HashMap<u32, Val<'ast>>,
    globals: &HashMap<u32, Val<'ast>>,
    solver: &mut Solver,
) -> Val<'ast> {
    use Exp::*;
    match exp {
        Id(v) => match get_and_initialize(*v, vars, solver) {
            Some(value) => value.clone(),
            None => get_and_initialize(*v, globals, solver).expect("No register found").clone(),
        },
        I64(i) => Val::I64(*i),
        I128(i) => Val::I128(*i),
        Unit => Val::Unit,
        Bool(b) => Val::Bool(*b),
        _ => panic!("Could not evaluate expression"),
    }
}

fn assign<'ast>(loc: &Loc<u32>, v: Val<'ast>, vars: &mut HashMap<u32, Val<'ast>>, solver: &mut Solver) {
    match loc {
        Loc::Id(l) => {
            vars.insert(*l, v);
        }
        _ => panic!("Bad assign"),
    }
}

// The callstack is implemented as a closure that restores the caller's stack frame
type Stack<'ast> = Option<Arc<dyn 'ast + Send + Sync + Fn(Val<'ast>, &mut LocalFrame<'ast>, &mut Solver) -> ()>>;

pub struct Frame<'ast> {
    pc: usize,
    backjumps: u32,
    vars: Arc<HashMap<u32, Val<'ast>>>,
    globals: Arc<HashMap<u32, Val<'ast>>>,
    instrs: &'ast [Instr<u32>],
    stack: Stack<'ast>,
}

impl<'ast> Frame<'ast> {
    pub fn new(registers: HashMap<u32, Val<'ast>>, instrs: &'ast [Instr<u32>]) -> Self {
        Frame { pc: 0, backjumps: 0, vars: Arc::new(HashMap::new()), globals: Arc::new(registers), instrs, stack: None }
    }
}

struct LocalFrame<'ast> {
    pc: usize,
    backjumps: u32,
    vars: HashMap<u32, Val<'ast>>,
    globals: HashMap<u32, Val<'ast>>,
    instrs: &'ast [Instr<u32>],
    stack: Stack<'ast>,
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

pub fn run<'ast>(
    tid: usize,
    queue: &Worker<(Frame<'ast>, Checkpoint)>,
    frame: &Frame<'ast>,
    checkpoint: Checkpoint,
    shared_state: &SharedState<'ast>,
) -> Option<Val<'ast>> {
    // First, set up a solver instance for the frame's SMT checkpoint.
    let cfg = Config::new();
    let ctx = Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    // Now create a local mutable version of the frame for us to
    // execute with
    let mut frame = unfreeze_frame(frame);

    loop {
        match &frame.instrs[frame.pc] {
            Instr::Decl(v, ty) => {
                frame.vars.insert(*v, Val::Uninitialized(ty));
                frame.pc += 1;
            }

            Instr::Init(var, _, exp) => {
                let value = eval_exp(exp, &frame.vars, &frame.globals, &mut solver);
                frame.vars.insert(*var, value);
                frame.pc += 1;
            }

            Instr::InitCast(var, to, exp, from) => {
                let value = eval_exp(exp, &frame.vars, &frame.globals, &mut solver);
                frame.vars.insert(*var, cast(to, from, value, &mut solver));
                frame.pc += 1;
            }

            Instr::Jump(exp, target) => {
                let value = eval_exp(exp, &frame.vars, &frame.globals, &mut solver);
                match value {
                    Val::Symbolic(v) => {
                        use smtlib::Def::*;
                        use smtlib::Exp::*;
                        let test_true = Var(v);
                        let test_false = Not(Box::new(Var(v)));
                        let can_be_true = solver.check_sat_with(&test_true).is_sat();
                        let can_be_false = solver.check_sat_with(&test_false).is_sat();
                        if can_be_true && can_be_false {
                            let point = solver.checkpoint_with(Assert(test_false));
                            let frozen = Frame { pc: frame.pc + 1, ..freeze_frame(&frame) };
                            queue.push((frozen, point));
                            solver.add(Assert(test_true));
                            frame.pc = *target
                        } else if can_be_true {
                            solver.add(Assert(test_true));
                            frame.pc = *target
                        } else if can_be_false {
                            solver.add(Assert(test_false));
                            frame.pc += 1
                        } else {
                            // This execution path is dead
                            return None;
                        }
                    }
                    Val::Bool(jump) => {
                        if jump {
                            frame.pc = *target
                        } else {
                            frame.pc += 1
                        }
                    }
                    _ => {
                        panic!("Bad jump");
                    }
                }
            }

            Instr::Goto(target) => frame.pc = *target,

            Instr::Copy(loc, exp) => {
                let value = eval_exp(exp, &frame.vars, &frame.globals, &mut solver);
                assign(loc, value, &mut frame.vars, &mut solver);
                frame.pc += 1;
            }

            Instr::CopyCast(loc, to, exp, from) => {
                let value = eval_exp(exp, &frame.vars, &frame.globals, &mut solver);
                assign(loc, cast(to, from, value, &mut solver), &mut frame.vars, &mut solver);
                frame.pc += 1;
            }

            Instr::PrimopUnary(loc, f, arg) => {
                let arg = eval_exp(arg, &frame.vars, &frame.globals, &mut solver);
                let value = f(arg, &mut solver);
                assign(loc, value, &mut frame.vars, &mut solver);
                frame.pc += 1;
            }

            Instr::PrimopBinary(loc, f, arg1, arg2) => {
                let arg1 = eval_exp(arg1, &frame.vars, &frame.globals, &mut solver);
                let arg2 = eval_exp(arg2, &frame.vars, &frame.globals, &mut solver);
                let value = f(arg1, arg2, &mut solver);
                assign(loc, value, &mut frame.vars, &mut solver);
                frame.pc += 1;
            }

            Instr::Call(loc, _, f, _) => {
                match shared_state.functions.get(&f) {
                    None => {
                        let symbol = shared_state.symtab.to_str(*f);
                        panic!("Attempted to call non-existent function {} ({})", symbol, *f)
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

            Instr::End => match frame.vars.get(&RETURN) {
                None => panic!("Reached end without assigning to return"),
                Some(value) => {
                    let caller = match &frame.stack {
                        None => return Some(value.clone()),
                        Some(caller) => caller.clone(),
                    };
                    (*caller)(value.clone(), &mut frame, &mut solver)
                }
            },

            _ => frame.pc += 1,
        }
    }
}
