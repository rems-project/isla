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

//! This module provides a function [linearize()] that converts IR
//! from function bodies containing loops and other IR, into a linear
//! sequence of instructions without any control flow.
//!
//! The way this works is as follows:
//!
//! ```text
//!     A    A: declare x; if b ...
//!    / \   B: then { x = f(x) }
//!   B   C  C: else { x = g(x) }
//!    \ /   D: return x
//!     D
//! ```
//!
//! This is then converted into SSA form, like:
//!
//! ```text
//!     A    A: declare x/1; if b
//!    / \   B: then { x/2 = f(x/1) }
//!   B   C  C: else { x/3 = g(x/1) }
//!    \ /   D: x/4 = φ(x/2, x/3); return x/4
//!     D
//! ```
//!
//! Finally, we come out of SSA form by placing the control flow graph
//! into topological order, and replacing the phi functions with `ite`
//! functions that map directly to the `ite` construct in the SMT
//! solver.
//!
//! ```text
//!    A     A: declare x/1;
//!    |     B: declare x/2;
//!    B        x/2 = f(x/1);
//!    |     C: declare x/3;
//!    C        x/3 = g(x/1);
//!    |     D: declare x/4;
//!    D        x/4 = ite(b, x/2, x/3);
//!             return x/4
//! ```
//!
//! The obvious limitations of this are that the function in question
//! needs to be pure (it can only read architectural state), and its
//! control flow graph must be acyclic so it can be placed into a
//! topological order.

use petgraph::algo;
use petgraph::graph::{EdgeIndex, NodeIndex};
use petgraph::Direction;
use std::cmp;
use std::ops::{BitAnd, BitOr};

use super::ssa::{unssa_ty, BlockInstr, Edge, SSAName, Terminator, CFG};
use super::*;
use crate::primop::variadic_primops;

/// The reachability of a node in an SSA graph is determined by a
/// boolean formula over edges which can be taken to reach that node.
#[derive(Clone)]
enum Reachability {
    True,
    False,
    Edge(EdgeIndex),
    And(Box<Reachability>, Box<Reachability>),
    Or(Box<Reachability>, Box<Reachability>),
}

fn terminator_reachability_exp(terminator: &Terminator, edge: &Edge) -> Exp<SSAName> {
    match (terminator, edge) {
        (Terminator::Continue, Edge::Continue) => Exp::Bool(true),
        (Terminator::Goto(_), Edge::Goto) => Exp::Bool(true),
        (Terminator::Jump(exp, _, _), Edge::Jump(true)) => exp.clone(),
        (Terminator::Jump(exp, _, _), Edge::Jump(false)) => Exp::Call(Op::Not, vec![exp.clone()]),
        (_, _) => panic!("Bad terminator/edge pair in SSA"),
    }
}

impl Reachability {
    fn exp<B: BV>(&self, cfg: &CFG<B>) -> Exp<SSAName> {
        use Reachability::*;
        match self {
            True => Exp::Bool(true),
            False => Exp::Bool(false),
            Edge(edge) => {
                if let Some((pred, _)) = cfg.graph.edge_endpoints(*edge) {
                    terminator_reachability_exp(&cfg.graph[pred].terminator, &cfg.graph[*edge])
                } else {
                    panic!("Edge in reachability condition does not exist!")
                }
            }
            And(lhs, rhs) => Exp::Call(Op::And, vec![lhs.exp(cfg), rhs.exp(cfg)]),
            Or(lhs, rhs) => Exp::Call(Op::Or, vec![lhs.exp(cfg), rhs.exp(cfg)]),
        }
    }
}

impl BitOr for Reachability {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        use Reachability::*;
        match (self, rhs) {
            (True, _) => True,
            (_, True) => True,
            (False, rhs) => rhs,
            (lhs, False) => lhs,
            (lhs, rhs) => Or(Box::new(lhs), Box::new(rhs)),
        }
    }
}

impl BitAnd for Reachability {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        use Reachability::*;
        match (self, rhs) {
            (True, rhs) => rhs,
            (lhs, True) => lhs,
            (False, _) => False,
            (_, False) => False,
            (lhs, rhs) => And(Box::new(lhs), Box::new(rhs)),
        }
    }
}

/// Computes the reachability condition for each node in an acyclic graph.
fn compute_reachability<B: BV>(cfg: &CFG<B>, topo_order: &[NodeIndex]) -> HashMap<NodeIndex, Reachability> {
    let mut reachability: HashMap<NodeIndex, Reachability> = HashMap::new();

    for ix in topo_order {
        let mut r = if *ix == cfg.root { Reachability::True } else { Reachability::False };

        for pred in cfg.graph.neighbors_directed(*ix, Direction::Incoming) {
            let edge = cfg.graph.find_edge(pred, *ix).unwrap();
            let (pred, _) = cfg.graph.edge_endpoints(edge).unwrap();
            let pred_r = reachability.get(&pred).unwrap().clone();
            r = r | (pred_r & Reachability::Edge(edge))
        }

        reachability.insert(*ix, r);
    }

    reachability
}

fn unssa_loc(loc: &Loc<SSAName>, symtab: &mut Symtab, names: &mut HashMap<SSAName, Name>) -> Loc<Name> {
    use Loc::*;
    match loc {
        Id(id) => Id(id.unssa(symtab, names)),
        Field(loc, field) => Field(Box::new(unssa_loc(loc, symtab, names)), field.unssa(symtab, names)),
        Addr(loc) => Addr(Box::new(unssa_loc(loc, symtab, names))),
    }
}

fn unssa_exp(exp: &Exp<SSAName>, symtab: &mut Symtab, names: &mut HashMap<SSAName, Name>) -> Exp<Name> {
    use Exp::*;
    match exp {
        Id(id) => Id(id.unssa(symtab, names)),
        Ref(r) => Ref(r.unssa(symtab, names)),
        Bool(b) => Bool(*b),
        Bits(bv) => Bits(*bv),
        String(s) => String(s.clone()),
        Unit => Unit,
        I64(n) => I64(*n),
        I128(n) => I128(*n),
        Undefined(ty) => Undefined(unssa_ty(ty)),
        Struct(s, fields) => Struct(
            s.unssa(symtab, names),
            fields.iter().map(|(field, exp)| (field.unssa(symtab, names), unssa_exp(exp, symtab, names))).collect(),
        ),
        Kind(ctor, exp) => Kind(ctor.unssa(symtab, names), Box::new(unssa_exp(exp, symtab, names))),
        Unwrap(ctor, exp) => Unwrap(ctor.unssa(symtab, names), Box::new(unssa_exp(exp, symtab, names))),
        Field(exp, field) => Field(Box::new(unssa_exp(exp, symtab, names)), field.unssa(symtab, names)),
        Call(op, args) => Call(*op, args.iter().map(|arg| unssa_exp(arg, symtab, names)).collect()),
    }
}

fn unssa_block_instr<B: BV>(
    instr: &BlockInstr<B>,
    symtab: &mut Symtab,
    names: &mut HashMap<SSAName, Name>,
) -> Instr<Name, B> {
    use BlockInstr::*;
    match instr {
        Decl(v, ty) => Instr::Decl(v.unssa(symtab, names), unssa_ty(ty)),
        Init(v, ty, exp) => Instr::Init(v.unssa(symtab, names), unssa_ty(ty), unssa_exp(exp, symtab, names)),
        Copy(loc, exp) => Instr::Copy(unssa_loc(loc, symtab, names), unssa_exp(exp, symtab, names)),
        Monomorphize(v) => Instr::Monomorphize(v.unssa(symtab, names)),
        Call(loc, ext, f, args) => Instr::Call(
            unssa_loc(loc, symtab, names),
            *ext,
            *f,
            args.iter().map(|arg| unssa_exp(arg, symtab, names)).collect(),
        ),
        PrimopUnary(loc, fptr, exp) => {
            Instr::PrimopUnary(unssa_loc(loc, symtab, names), *fptr, unssa_exp(exp, symtab, names))
        }
        PrimopBinary(loc, fptr, exp1, exp2) => Instr::PrimopBinary(
            unssa_loc(loc, symtab, names),
            *fptr,
            unssa_exp(exp1, symtab, names),
            unssa_exp(exp2, symtab, names),
        ),
        PrimopVariadic(loc, fptr, args) => Instr::PrimopVariadic(
            unssa_loc(loc, symtab, names),
            *fptr,
            args.iter().map(|arg| unssa_exp(arg, symtab, names)).collect(),
        ),
    }
}

fn apply_label<B: BV>(label: &mut Option<usize>, instr: Instr<Name, B>) -> LabeledInstr<B> {
    if let Some(label) = label.take() {
        LabeledInstr::Labeled(label, instr)
    } else {
        LabeledInstr::Unlabeled(instr)
    }
}

#[allow(clippy::too_many_arguments)]
fn ite_chain<B: BV>(
    label: &mut Option<usize>,
    i: usize,
    path_conds: &[Exp<SSAName>],
    id: Name,
    first: SSAName,
    rest: &[SSAName],
    ty: &Ty<Name>,
    names: &mut HashMap<SSAName, Name>,
    symtab: &mut Symtab,
    linearized: &mut Vec<LabeledInstr<B>>,
) {
    let ite = *variadic_primops::<B>().get("ite").unwrap();

    if let Some((second, rest)) = rest.split_first() {
        let gs = symtab.gensym();
        linearized.push(apply_label(label, Instr::Decl(gs, ty.clone())));
        ite_chain(label, i + 1, path_conds, gs, *second, rest, ty, names, symtab, linearized);
        linearized.push(apply_label(
            label,
            Instr::PrimopVariadic(
                Loc::Id(id),
                ite,
                vec![unssa_exp(&path_conds[i], symtab, names), Exp::Id(first.unssa(symtab, names)), Exp::Id(gs)],
            ),
        ))
    } else {
        linearized.push(apply_label(label, Instr::Copy(Loc::Id(id), Exp::Id(first.unssa(symtab, names)))))
    }
}

#[allow(clippy::too_many_arguments)]
fn linearize_phi<B: BV>(
    label: &mut Option<usize>,
    id: SSAName,
    args: &[SSAName],
    n: NodeIndex,
    cfg: &CFG<B>,
    reachability: &HashMap<NodeIndex, Reachability>,
    names: &mut HashMap<SSAName, Name>,
    types: &HashMap<Name, Ty<Name>>,
    symtab: &mut Symtab,
    linearized: &mut Vec<LabeledInstr<B>>,
) {
    let mut path_conds = Vec::new();

    for pred in cfg.graph.neighbors_directed(n, Direction::Incoming) {
        let edge = cfg.graph.find_edge(pred, n).unwrap();
        let cond = reachability[&pred].clone() & Reachability::Edge(edge);
        path_conds.push(cond.exp(cfg))
    }

    // A phi function with no arguments has been explicitly pruned, so
    // we do nothing in that case.
    if let Some((first, rest)) = args.split_first() {
        let ty = &types[&id.base_name()];
        ite_chain(label, 0, &path_conds, id.unssa(symtab, names), *first, rest, ty, names, symtab, linearized)
    }
}

fn linearize_block<B: BV>(
    n: NodeIndex,
    cfg: &CFG<B>,
    reachability: &HashMap<NodeIndex, Reachability>,
    names: &mut HashMap<SSAName, Name>,
    types: &HashMap<Name, Ty<Name>>,
    symtab: &mut Symtab,
    linearized: &mut Vec<LabeledInstr<B>>,
) {
    let block = cfg.graph.node_weight(n).unwrap();
    let mut label = block.label;

    for (id, args) in &block.phis {
        let ty = &types[&id.base_name()];

        linearized.push(apply_label(&mut label, Instr::Decl(id.unssa(symtab, names), ty.clone())));

        // We never have to insert ites for phi functions with unit
        // types, and in fact cannot because unit is always concrete.
        match ty {
            Ty::Unit => (),
            _ => linearize_phi(&mut label, *id, args, n, cfg, reachability, names, types, symtab, linearized),
        }
    }

    for instr in &block.instrs {
        if let Some(id) = instr.write_ssa() {
            if instr.declares().is_none() {
                let ty = types[&id.base_name()].clone();
                linearized.push(apply_label(&mut label, Instr::Decl(id.unssa(symtab, names), ty)))
            }
        }
        linearized.push(apply_label(&mut label, unssa_block_instr(instr, symtab, names)))
    }
}

pub fn linearize<B: BV>(instrs: Vec<Instr<Name, B>>, ret_ty: &Ty<Name>, symtab: &mut Symtab) -> Vec<Instr<Name, B>> {
    use LabeledInstr::*;

    let labeled = prune_labels(label_instrs(instrs));
    let mut cfg = CFG::new(&labeled);
    cfg.ssa();

    if let Ok(topo_order) = algo::toposort(&cfg.graph, None) {
        let reachability = compute_reachability(&cfg, &topo_order);
        let types = cfg.all_vars_typed(ret_ty);
        let mut linearized = Vec::new();
        let mut names = HashMap::new();
        let mut last_return = -1;

        for ix in cfg.graph.node_indices() {
            let node = &cfg.graph[ix];
            for instr in &node.instrs {
                if let Some(id) = instr.write_ssa() {
                    if id.base_name() == RETURN {
                        last_return = cmp::max(id.ssa_number(), last_return)
                    }
                }
            }
            for (id, _) in &node.phis {
                if id.base_name() == RETURN {
                    last_return = cmp::max(id.ssa_number(), last_return)
                }
            }
        }

        for ix in &topo_order {
            linearize_block(*ix, &cfg, &reachability, &mut names, &types, symtab, &mut linearized)
        }

        if last_return >= 0 {
            linearized.push(Unlabeled(Instr::Copy(
                Loc::Id(RETURN),
                Exp::Id(SSAName::new_ssa(RETURN, last_return).unssa(symtab, &mut names)),
            )))
        }
        linearized.push(Unlabeled(Instr::End));

        unlabel_instrs(linearized)
    } else {
        unlabel_instrs(labeled)
    }
}
