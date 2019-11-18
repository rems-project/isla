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
use crate::error::Error;
use crate::log::log_from;
use crate::zencode;
use isla_smt::*;

fn symbolic<'ast>(ty: &Ty<u32>, solver: &mut Solver) -> Val<'ast> {
    let smt_ty = match ty {
        Ty::I64 => smtlib::Ty::BitVec(64),
        Ty::I128 => smtlib::Ty::BitVec(128),
        Ty::Bits(sz) => smtlib::Ty::BitVec(*sz),
        Ty::Unit => return Val::Unit,
        Ty::Bool => smtlib::Ty::Bool,
        _ => panic!("Cannot convert type {:?}", ty),
    };
    let sym = solver.fresh();
    solver.add(smtlib::Def::DeclareConst(sym, smt_ty));
    Val::Symbolic(sym)
}

fn get_and_initialize<'ast>(v: u32, vars: &HashMap<u32, Val<'ast>>, solver: &mut Solver) -> Option<Val<'ast>> {
    match vars.get(&v) {
        Some(Val::Uninitialized(ty)) => Some(symbolic(ty, solver)),
        Some(value) => Some(value.clone()),
        None => None,
    }
}

fn eval_exp<'ast>(
    exp: &Exp<u32>,
    vars: &HashMap<u32, Val<'ast>>,
    globals: &HashMap<u32, Val<'ast>>,
    shared_state: &SharedState<'ast>,
    solver: &mut Solver,
) -> Val<'ast> {
    use Exp::*;
    match exp {
        Id(v) => match get_and_initialize(*v, vars, solver) {
            Some(value) => value.clone(),
            None => match get_and_initialize(*v, globals, solver) {
                Some(value) => value.clone(),
                None => panic!("Symbol {} not found", zencode::decode(shared_state.symtab.to_str(*v))),
            },
        },
        I64(i) => Val::I64(*i),
        I128(i) => Val::I128(*i),
        Unit => Val::Unit,
        Bool(b) => Val::Bool(*b),
        Bits(bv) => Val::Bits(*bv),
        _ => panic!("Could not evaluate expression {:?}", exp),
    }
}

fn assign<'ast>(loc: &Loc<u32>, v: Val<'ast>, vars: &mut HashMap<u32, Val<'ast>>, _solver: &mut Solver) {
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
    pub fn new(args: &[(u32, &'ast Ty<u32>)], registers: HashMap<u32, Val<'ast>>, instrs: &'ast [Instr<u32>]) -> Self {
        let mut vars = HashMap::new();
        for (id, ty) in args {
            vars.insert(*id, Val::Uninitialized(ty));
        }
        Frame { pc: 0, backjumps: 0, vars: Arc::new(vars), globals: Arc::new(registers), instrs, stack: None }
    }
}

pub struct LocalFrame<'ast> {
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

fn run<'ast>(
    _tid: usize,
    queue: &Worker<(Frame<'ast>, Checkpoint)>,
    frame: &Frame<'ast>,
    shared_state: &SharedState<'ast>,
    solver: &mut Solver,
) -> Result<(Val<'ast>, LocalFrame<'ast>), Error> {
    let mut frame = unfreeze_frame(frame);
    loop {
        match &frame.instrs[frame.pc] {
            Instr::Decl(v, ty) => {
                frame.vars.insert(*v, Val::Uninitialized(ty));
                frame.pc += 1;
            }

            Instr::Init(var, _, exp) => {
                let value = eval_exp(exp, &frame.vars, &frame.globals, shared_state, solver);
                frame.vars.insert(*var, value);
                frame.pc += 1;
            }

            Instr::Jump(exp, target) => {
                let value = eval_exp(exp, &frame.vars, &frame.globals, shared_state, solver);
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
                            return Err(Error::Dead);
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
                        return Err(Error::Type("Jump on non boolean"));
                    }
                }
            }

            Instr::Goto(target) => frame.pc = *target,

            Instr::Copy(loc, exp) => {
                let value = eval_exp(exp, &frame.vars, &frame.globals, shared_state, solver);
                assign(loc, value, &mut frame.vars, solver);
                frame.pc += 1;
            }

            Instr::PrimopUnary(loc, f, arg) => {
                let arg = eval_exp(arg, &frame.vars, &frame.globals, shared_state, solver);
                let value = f(arg, solver)?;
                assign(loc, value, &mut frame.vars, solver);
                frame.pc += 1;
            }

            Instr::PrimopBinary(loc, f, arg1, arg2) => {
                let arg1 = eval_exp(arg1, &frame.vars, &frame.globals, shared_state, solver);
                let arg2 = eval_exp(arg2, &frame.vars, &frame.globals, shared_state, solver);
                let value = f(arg1, arg2, solver)?;
                assign(loc, value, &mut frame.vars, solver);
                frame.pc += 1;
            }

            Instr::PrimopVariadic(loc, f, args) => {
                let args =
                    args.iter().map(|arg| eval_exp(arg, &frame.vars, &frame.globals, shared_state, solver)).collect();
                let value = f(args, solver)?;
                assign(loc, value, &mut frame.vars, solver);
                frame.pc += 1;
            }

            Instr::Call(loc, _, f, args) => {
                match shared_state.functions.get(&f) {
                    None => {
                        let symbol = shared_state.symtab.to_str(*f);
                        panic!("Attempted to call non-existent function {} ({})", symbol, *f)
                    }
                    Some((params, _, instrs)) => {
                        let mut args: Vec<Val<'ast>> = args
                            .iter()
                            .map(|arg| eval_exp(arg, &frame.vars, &frame.globals, shared_state, solver))
                            .collect();
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
                        frame.vars.clear();
                        for (i, arg) in args.drain(..).enumerate() {
                            frame.vars.insert(params[i].0, arg);
                        }
                        frame.pc = 0;
                        frame.instrs = instrs;
                    }
                }
            }

            Instr::End => match frame.vars.get(&RETURN) {
                None => panic!("Reached end without assigning to return"),
                Some(value) => {
                    let caller = match &frame.stack {
                        None => return Ok((value.clone(), frame)),
                        Some(caller) => caller.clone(),
                    };
                    (*caller)(value.clone(), &mut frame, solver)
                }
            },

            _ => frame.pc += 1,
        }
    }
}

pub fn start<'ast>(
    tid: usize,
    queue: &Worker<(Frame<'ast>, Checkpoint)>,
    frame: &Frame<'ast>,
    checkpoint: Checkpoint,
    shared_state: &SharedState<'ast>,
) -> Result<Val<'ast>, Error> {
    let cfg = Config::new();
    let ctx = Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    let (result, _frame) = run(tid, queue, frame, shared_state, &mut solver)?;
    match result {
        Val::Symbolic(v) => {
            use smtlib::Def::*;
            use smtlib::Exp::*;
            solver.add(Assert(Not(Box::new(Var(v)))));
            if solver.check_sat() == SmtResult::Unsat {
                log_from(tid, 0, &format!("Was unsat! {}", v))
            } else {
                log_from(tid, 0, &format!("Was sat! {}", v))
            }
        }
        _ => (),
    };
    Ok(result)
}

pub fn start_single<'ast, R>(
    frame: Frame<'ast>,
    checkpoint: Checkpoint,
    shared_state: &SharedState<'ast>,
    collector: fn(Val<'ast>, LocalFrame<'ast>, &SharedState<'ast>, &mut Solver, &mut R) -> Result<(), Error>,
    result: &mut R,
) -> Result<(), Error> {
    let queue = Worker::new_lifo();
    queue.push((frame, checkpoint));
    while let Some((frame, checkpoint)) = queue.pop() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
        let (value, frame) = run(0, &queue, &frame, shared_state, &mut solver)?;
        collector(value, frame, shared_state, &mut solver, result)?
    }
    Ok(())
}
