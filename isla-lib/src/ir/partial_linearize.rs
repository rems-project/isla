// BSD 2-Clause License
//
// Copyright (c) 2022 Alasdair Armstrong
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

use petgraph::algo::dominators::{self, Dominators};
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use std::collections::{HashMap, HashSet};

use super::linearize::*;
use super::source_loc::SourceLoc;
use super::ssa::*;
use super::*;

fn has_phi_child<B: BV>(cfg: &CFG<B>, ix: NodeIndex) -> bool {
    for child in cfg.graph.neighbors_directed(ix, Direction::Outgoing) {
        if !cfg.graph[child].phis.is_empty() {
            return true;
        }
    }
    false
}

fn insert_block_markers<B: BV>(cfg: &mut CFG<B>, symtab: &mut Symtab) -> HashMap<NodeIndex, SSAName> {
    let mut inits = Vec::new();
    let mut markers = HashMap::new();

    for ix in cfg.graph.node_indices() {
        if !has_phi_child(cfg, ix) {
            continue;
        };

        let marker = SSAName::new(symtab.gensym());
        markers.insert(ix, marker);
        cfg.graph[ix].instrs.push(BlockInstr::Copy(BlockLoc::Id(marker), Exp::Bool(true), SourceLoc::unknown()));

        let mut children = cfg.graph.neighbors_directed(ix, Direction::Outgoing).detach();
        let mut visited = HashSet::new();
        while let Some(child) = children.next_node(&cfg.graph) {
            if !visited.contains(&child) {
                cfg.graph[child].instrs.push(BlockInstr::Copy(
                    BlockLoc::Id(marker),
                    Exp::Bool(false),
                    SourceLoc::unknown(),
                ));
                visited.insert(child);
            }
        }

        inits.push(BlockInstr::Init(marker, Ty::Bool, Exp::Bool(false), SourceLoc::unknown()))
    }

    inits.append(&mut cfg.graph[cfg.root].instrs);
    cfg.graph[cfg.root].instrs = inits;

    markers
}

fn partial_linearize_phi<B: BV>(
    label: &mut Option<usize>,
    id: SSAName,
    args: &[SSAName],
    n: NodeIndex,
    cfg: &CFG<B>,
    block_markers: &HashMap<NodeIndex, SSAName>,
    names: &mut HashMap<SSAName, Name>,
    types: &HashMap<Name, Ty<Name>>,
    symtab: &mut Symtab,
    linearized: &mut Vec<LabeledInstr<B>>,
) {
    let mut conds: Vec<(usize, Exp<SSAName>)> = Vec::new();

    for edge in cfg.graph.edges_directed(n, Direction::Incoming) {
        let parent = edge.source();
        let marker = block_markers[&parent];

        let cond = cfg.graph[parent].terminator.jump_tree().unwrap().extract(edge.weight().1.path().unwrap());
        conds.push((edge.weight().0, short_circuit_and(Exp::Id(marker), cond)))
    }

    conds.sort_by(|(n, _), (m, _)| n.cmp(m));
    let path_conds: Vec<Exp<SSAName>> = conds.drain(..).map(|c| c.1).collect();

    if let Some((first, rest)) = args.split_first() {
        let ty = &types[&id.base_name()];
        ite_chain(label, 0, &path_conds, id.unssa_ex(symtab, names), *first, rest, ty, names, symtab, linearized)
    }
}

fn partial_linearize_block<B: BV>(
    n: NodeIndex,
    cfg: &CFG<B>,
    dominators: &Dominators<NodeIndex>,
    block_markers: &HashMap<NodeIndex, SSAName>,
    names: &mut HashMap<SSAName, Name>,
    types: &HashMap<Name, Ty<Name>>,
    symtab: &mut Symtab,
    linearized: &mut Vec<LabeledInstr<B>>,
) {
    let block = cfg.graph.node_weight(n).unwrap();
    let mut label = block.label;

    for (id, args) in &block.phis {
        let ty = &types[&id.base_name()];

        linearized
            .push(apply_label(&mut label, Instr::Decl(id.unssa(symtab, names), ty.clone(), SourceLoc::unknown())));

        // We never have to insert ites for phi functions with unit
        // types, and in fact cannot because unit is always concrete.
        match ty {
            Ty::Unit => (),
            _ => partial_linearize_phi(&mut label, *id, args, n, cfg, block_markers, names, types, symtab, linearized),
        }
    }

    for instr in &block.instrs {
        if let Some((id, prev_id)) = instr.write_ssa() {
            if instr.declares().is_none() {
                let ty = types[&id.base_name()].clone();
                let instr = match prev_id {
                    Some(prev_id) => Instr::Init(
                        id.unssa(symtab, names),
                        ty,
                        Exp::Id(prev_id.unssa_ex(symtab, names)),
                        SourceLoc::unknown(),
                    ),
                    None => Instr::Decl(id.unssa(symtab, names), ty, SourceLoc::unknown()),
                };
                linearized.push(apply_label(&mut label, instr))
            }
        }
        linearized.push(apply_label(&mut label, unssa_block_instr(instr, symtab, names)))
    }

    match &block.terminator {
        // A multi-jump terminator becomes a sequence of jump
        // instructions followed by a final goto instruction. Since
        // the condition for the final goto can be omitted, we sort
        // the conditions in the jump tree by their complexity so we
        // can omit the most complex one.
        Terminator::MultiJump(tree) => {
            let mut targets: Vec<(usize, Exp<SSAName>)> =
                tree.targets().drain(..).map(|target| (target, tree.condition_for(target))).collect();
            targets.sort_by(|(_, exp1), (_, exp2)| exp1.size_heuristic().cmp(&exp2.size_heuristic()));
            assert!(!targets.is_empty());

            for (target, exp) in &targets[0..targets.len() - 1] {
                linearized.push(apply_label(
                    &mut label,
                    Instr::Jump(unssa_exp(exp, symtab, names), *target, SourceLoc::unknown()),
                ))
            }

            linearized.push(apply_label(&mut label, Instr::Goto(targets[targets.len() - 1].0)))
        }

        // For an end terminator we need to find the last time the
        // RETURN variable was assigned to in the SSA graph. This must
        // either be in our node, or a strict dominator of our node.
        Terminator::End => {
            let mut last_return = None;

            'find_last_return: for ix in [n].iter().copied().chain(dominators.strict_dominators(n).unwrap()) {
                let node = &cfg.graph[ix];
                for instr in node.instrs.iter().rev() {
                    if let Some((id, _)) = instr.write_ssa() {
                        if id.base_name() == RETURN {
                            last_return = Some(id);
                            break 'find_last_return;
                        }
                    }
                }
                for (id, _) in &node.phis {
                    if id.base_name() == RETURN {
                        last_return = Some(*id);
                        break 'find_last_return;
                    }
                }
            }

            assert!(last_return.is_some());

            linearized.push(apply_label(
                &mut label,
                Instr::Copy(Loc::Id(RETURN), Exp::Id(last_return.unwrap().unssa(symtab, names)), SourceLoc::unknown()),
            ));
            linearized.push(apply_label(&mut label, Instr::End))
        }

        Terminator::Failure => linearized.push(apply_label(&mut label, Instr::Failure)),
        Terminator::Arbitrary => linearized.push(apply_label(&mut label, Instr::Arbitrary)),

        Terminator::Jump(_, _, _) | Terminator::Continue | Terminator::Goto(_) => {
            panic!("Invalid terminator in partial_linearize_block")
        }
    }
}

pub fn partial_linearize<B: BV>(
    instrs: Vec<Instr<Name, B>>,
    ret_ty: &Ty<Name>,
    symtab: &mut Symtab,
) -> Vec<Instr<Name, B>> {
    use LabeledInstr::*;

    let labeled = prune_labels(label_instrs(instrs));
    let mut cfg = CFG::new(&labeled);
    cfg.ssa();
    cfg.merge_control_flow();
    let block_markers = insert_block_markers(&mut cfg, symtab);
    let dominators = dominators::simple_fast(&cfg.graph, cfg.root);

    let types = cfg.all_vars_typed(ret_ty);

    let mut linearized = Vec::new();
    let mut names = HashMap::new();

    linearized.push(Unlabeled(Instr::Goto(cfg.graph[cfg.root].label.unwrap())));

    for ix in cfg.graph.node_indices() {
        partial_linearize_block(ix, &cfg, &dominators, &block_markers, &mut names, &types, symtab, &mut linearized)
    }

    unlabel_instrs(linearized)
}
