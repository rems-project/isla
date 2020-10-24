// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
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

//! This module provides a control flow graph type [CFG] for IR
//! analysis and transforms, and additionally supports conversion of
//! that CFG into single static assignment (SSA) form via
//! [CFG::ssa()].

use petgraph::algo::dominators::{self, Dominators};
use petgraph::graph::{Graph, NodeIndex};
use petgraph::{Directed, Direction};
use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use std::usize;

use super::*;
use crate::primop::{Binary, Unary, Variadic};

/// A [SSAName] is a [Name] augmented with an additional number. The
/// number is a signed integer, with the value `-1` representing a
/// name that does not have an SSA number (either because the CFG is
/// not in SSA form, or because it is a type name, function identifer,
/// or similar that does not need one in SSA form).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SSAName {
    name: Name,
    number: i32,
}

impl SSAName {
    pub fn new(name: Name) -> Self {
        SSAName { name, number: -1 }
    }

    pub fn new_ssa(name: Name, number: i32) -> Self {
        SSAName { name, number }
    }

    pub fn base_name(self) -> Name {
        self.name
    }

    fn ssa_number_mut(&mut self) -> &mut i32 {
        &mut self.number
    }

    pub fn ssa_number(self) -> i32 {
        self.number
    }

    pub(crate) fn unssa(self, symtab: &mut Symtab, generated: &mut HashMap<SSAName, Name>) -> Name {
        if self.number < 0 {
            self.name
        } else if let Some(name) = generated.get(&self) {
            *name
        } else {
            let gs = symtab.gensym();
            generated.insert(self, gs);
            gs
        }
    }

    fn write(self, output: &mut dyn Write, symtab: &Symtab) -> std::io::Result<()> {
        if self.number >= 0 {
            write!(output, "{}/{}", zencode::decode(symtab.to_str(self.name)), self.number)
        } else {
            write!(output, "{}", zencode::decode(symtab.to_str(self.name)))
        }
    }
}

pub(crate) fn unssa_ty(ty: &Ty<SSAName>) -> Ty<Name> {
    use Ty::*;
    match ty {
        I64 => I64,
        I128 => I128,
        AnyBits => AnyBits,
        Bits(n) => Bits(*n),
        Unit => Unit,
        Bool => Bool,
        Bit => Bit,
        String => String,
        Real => Real,
        Enum(id) => {
            assert!(id.number < 0);
            Enum(id.name)
        }
        Struct(id) => {
            assert!(id.number < 0);
            Struct(id.name)
        }
        Union(id) => {
            assert!(id.number < 0);
            Union(id.name)
        }
        Vector(ty) => Vector(Box::new(unssa_ty(ty))),
        FixedVector(n, ty) => FixedVector(*n, Box::new(unssa_ty(ty))),
        List(ty) => List(Box::new(unssa_ty(ty))),
        Ref(ty) => Ref(Box::new(unssa_ty(ty))),
    }
}

#[derive(Clone, Debug)]
pub enum BlockLoc {
    Id(SSAName),
    // Field locations contain the previous name so that we can update one field at a time
    Field(Box<BlockLoc>, SSAName, SSAName),
    Addr(Box<BlockLoc>),
}

impl BlockLoc {
    fn id(&self) -> SSAName {
        match self {
            BlockLoc::Id(id) => id.clone(),
            BlockLoc::Field(loc, _, _) | BlockLoc::Addr(loc) => loc.id(),
        }
    }

    fn ids(&self) -> (SSAName, Option<SSAName>) {
        match self {
            BlockLoc::Id(id) => (id.clone(), None),
            BlockLoc::Field(loc, base_id, _) => (loc.id(), Some(base_id.clone())),
            BlockLoc::Addr(loc) => (loc.id(), None),
        }
    }

    fn collect_variables<'a, 'b>(&'a mut self, vars: &'b mut Vec<Variable<'a, SSAName>>) {
        match self {
            BlockLoc::Id(id) => vars.push(Variable::Declaration(id)),
            BlockLoc::Field(loc, id, _) => {
                loc.collect_variables(vars);
                vars.push(Variable::Usage(id))
            }
            BlockLoc::Addr(loc) => loc.collect_variables(vars),
        }
    }
}

impl From<&Loc<Name>> for BlockLoc {
    fn from(loc: &Loc<Name>) -> Self {
        match loc {
            Loc::Id(id) => BlockLoc::Id(SSAName::new(*id)),
            Loc::Field(loc, field) => {
                let base_name = SSAName::new(loc.id());
                BlockLoc::Field(Box::new(Self::from(loc.as_ref())), base_name, SSAName::new(*field))
            }
            Loc::Addr(loc) => BlockLoc::Addr(Box::new(Self::from(loc.as_ref()))),
        }
    }
}

/// [BlockInstr] is the same as [Instr] but restricted to just
/// instructions that can appear in basic blocks, and with all names
/// replaced by [SSAName].
pub enum BlockInstr<B: BV> {
    Decl(SSAName, Ty<SSAName>),
    Init(SSAName, Ty<SSAName>, Exp<SSAName>),
    Copy(BlockLoc, Exp<SSAName>),
    Monomorphize(SSAName),
    Call(BlockLoc, bool, Name, Vec<Exp<SSAName>>),
    PrimopUnary(BlockLoc, Unary<B>, Exp<SSAName>),
    PrimopBinary(BlockLoc, Binary<B>, Exp<SSAName>, Exp<SSAName>),
    PrimopVariadic(BlockLoc, Variadic<B>, Vec<Exp<SSAName>>),
}

impl<B: BV> BlockInstr<B> {
    // Returns the written-to variable, and its previous name if it's a field access
    pub fn write_ssa(&self) -> Option<(SSAName, Option<SSAName>)> {
        use BlockInstr::*;
        match self {
            Decl(id, _) | Init(id, _, _) => Some((*id, None)),
            Copy(loc, _)
            | Call(loc, _, _, _)
            | PrimopUnary(loc, _, _)
            | PrimopBinary(loc, _, _, _)
            | PrimopVariadic(loc, _, _) => Some(loc.ids()),
            _ => None,
        }
    }

    pub fn write(&self) -> Option<Name> {
        self.write_ssa().map(|(id, _)| id.name)
    }

    pub fn declares(&self) -> Option<Name> {
        use BlockInstr::*;
        match self {
            Decl(id, _) | Init(id, _, _) => Some(id.name),
            _ => None,
        }
    }

    fn declares_typed(&self) -> Option<(Name, Ty<Name>)> {
        use BlockInstr::*;
        match self {
            Decl(id, ty) | Init(id, ty, _) => Some((id.name, unssa_ty(ty))),
            _ => None,
        }
    }

    fn collect_variables<'a, 'b>(&'a mut self, vars: &'b mut Vec<Variable<'a, SSAName>>) {
        use BlockInstr::*;
        match self {
            Decl(id, _) => vars.push(Variable::Declaration(id)),
            Init(id, _, exp) => {
                vars.push(Variable::Declaration(id));
                exp.collect_variables(vars)
            }
            Copy(loc, exp) => {
                loc.collect_variables(vars);
                exp.collect_variables(vars)
            }
            Monomorphize(id) => vars.push(Variable::Usage(id)),
            Call(loc, _, _, args) => {
                loc.collect_variables(vars);
                args.iter_mut().for_each(|exp| exp.collect_variables(vars))
            }
            PrimopUnary(loc, _, exp) => {
                loc.collect_variables(vars);
                exp.collect_variables(vars)
            }
            PrimopBinary(loc, _, lhs, rhs) => {
                loc.collect_variables(vars);
                lhs.collect_variables(vars);
                rhs.collect_variables(vars)
            }
            PrimopVariadic(loc, _, args) => {
                loc.collect_variables(vars);
                args.iter_mut().for_each(|exp| exp.collect_variables(vars))
            }
        }
    }

    fn variables(&mut self) -> Variables<'_, SSAName> {
        let mut vec = Vec::new();
        self.collect_variables(&mut vec);
        Variables::from_vec(vec)
    }
}

impl<B: BV> fmt::Debug for BlockInstr<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BlockInstr::*;
        match self {
            Decl(id, ty) => write!(f, "{:?} : {:?}", id, ty),
            Init(id, ty, exp) => write!(f, "{:?} : {:?} = {:?}", id, ty, exp),
            Copy(loc, exp) => write!(f, "{:?} = {:?}", loc, exp),
            Monomorphize(id) => write!(f, "mono {:?}", id),
            Call(loc, ext, id, args) => write!(f, "{:?} = {:?}<{:?}>({:?})", loc, id, ext, args),
            _ => write!(f, "primop"),
        }
    }
}

/// An instruction that can only occur at the end of a basic block.
#[derive(Debug)]
pub enum Terminator {
    Continue,
    Goto(usize),
    Jump(Exp<SSAName>, usize, String),
    Failure,
    Arbitrary,
    End,
}

impl Terminator {
    fn collect_variables<'a, 'b>(&'a mut self, vars: &'b mut Vec<Variable<'a, SSAName>>) {
        if let Terminator::Jump(exp, _, _) = self {
            exp.collect_variables(vars)
        }
    }

    fn variables(&mut self) -> Variables<'_, SSAName> {
        let mut vec = Vec::new();
        self.collect_variables(&mut vec);
        Variables::from_vec(vec)
    }
}

#[derive(Debug)]
pub struct Block<B: BV> {
    pub label: Option<usize>,
    pub phis: Vec<(SSAName, Vec<SSAName>)>,
    pub instrs: Vec<BlockInstr<B>>,
    pub terminator: Terminator,
}

impl<B: BV> Block<B> {
    fn insert_phi(&mut self, id: Name, num_preds: usize) {
        self.phis.push((SSAName::new(id), vec![SSAName::new(id); num_preds]))
    }

    fn rename(&mut self, counts: &mut HashMap<Name, i32>, stacks: &mut HashMap<Name, Vec<i32>>) {
        for (id, _) in self.phis.iter_mut() {
            let i = counts.entry(id.name).or_default();
            *i += 1;
            stacks.entry(id.name).or_default().push(*i);
            *id.ssa_number_mut() = *i;
        }

        for instr in self.instrs.iter_mut() {
            for variable_use in instr.variables() {
                match variable_use {
                    Variable::Declaration(id) => {
                        let i = counts.entry(id.name).or_default();
                        *i += 1;
                        stacks.entry(id.name).or_default().push(*i);
                        *id.ssa_number_mut() = *i
                    }
                    Variable::Usage(id) => {
                        if let Some(stack) = stacks.get(&id.name) {
                            let i = stack.last().expect("Empty stack when renaming variables");
                            *id.ssa_number_mut() = *i
                        }
                    }
                }
            }
        }

        for variable_use in self.terminator.variables() {
            if let Variable::Usage(id) = variable_use {
                if let Some(stack) = stacks.get(&id.name) {
                    let i = stack.last().expect("Empty stack when renaming variables");
                    *id.ssa_number_mut() = *i
                }
            }
        }
    }

    fn rename_phi_arg(&mut self, j: usize, stacks: &mut HashMap<Name, Vec<i32>>) {
        for (id, args) in self.phis.iter_mut() {
            let i = stacks.get(&id.name).and_then(|v| v.last()).expect("Empty stack when renaming phi arg");
            if *i != 0 {
                if !args.is_empty() {
                    *args[j].ssa_number_mut() = *i
                }
            } else {
                // A phi function that has variable x/0 is pointing to
                // an undeclared variable x, which implies that x has
                // gone out of scope, and so this phi function can be
                // pruned.
                *args = vec![]
            }
        }
    }
}

/// An edge between basic blocks in the control flow graph. The edge
/// corresponds to the [Terminator] of the node the edge comes from.
#[derive(Debug)]
pub enum Edge {
    /// True if the Jump expression was true, and the jump was taken.
    Jump(bool),
    Goto,
    Continue,
}

pub struct CFG<B: BV> {
    pub root: NodeIndex,
    pub graph: Graph<Block<B>, Edge, Directed>,
}

/// Takes the final instruction in a basic block, and returns the
/// appropriate terminator for that block.
fn to_terminator<B: BV>(instr: &Instr<Name, B>) -> Terminator {
    match instr {
        Instr::Goto(target) => Terminator::Goto(*target),
        Instr::Jump(cond, target, loc) => Terminator::Jump(block_exp(cond), *target, loc.clone()),
        Instr::Failure => Terminator::Failure,
        Instr::Arbitrary => Terminator::Arbitrary,
        Instr::End => Terminator::End,
        _ => Terminator::Continue,
    }
}

type TerminatorSplit<'a, B> = (&'a [LabeledInstr<B>], Option<usize>, Terminator, &'a [LabeledInstr<B>]);

fn split_terminator<B: BV>(instrs: &[LabeledInstr<B>]) -> Option<TerminatorSplit<'_, B>> {
    for (i, instr) in instrs.iter().enumerate() {
        match instr.strip_ref() {
            // Any labeled instruction after the first becomes the start of a new block
            _ if i > 0 && instr.is_labeled() => return Some((&instrs[0..i], None, Terminator::Continue, &instrs[i..])),
            Instr::Goto(_) | Instr::Jump(_, _, _) | Instr::Failure | Instr::Arbitrary | Instr::End => {
                return Some((&instrs[0..i], instr.label(), to_terminator(instr.strip_ref()), &instrs[(i + 1)..]))
            }
            _ => (),
        }
    }
    None
}

fn block_label<B: BV>(instrs: &[LabeledInstr<B>], terminator_label: Option<usize>) -> Option<usize> {
    match instrs.first() {
        None => terminator_label,
        Some(instr) => instr.label(),
    }
}

fn block_ty(ty: &Ty<Name>) -> Ty<SSAName> {
    use Ty::*;
    match ty {
        I64 => I64,
        I128 => I128,
        AnyBits => AnyBits,
        Bits(n) => Bits(*n),
        Unit => Unit,
        Bool => Bool,
        Bit => Bit,
        String => String,
        Real => Real,
        Enum(id) => Enum(SSAName::new(*id)),
        Struct(id) => Struct(SSAName::new(*id)),
        Union(id) => Union(SSAName::new(*id)),
        Vector(ty) => Vector(Box::new(block_ty(ty))),
        FixedVector(n, ty) => FixedVector(*n, Box::new(block_ty(ty))),
        List(ty) => List(Box::new(block_ty(ty))),
        Ref(ty) => Ref(Box::new(block_ty(ty))),
    }
}

fn block_exp(exp: &Exp<Name>) -> Exp<SSAName> {
    use Exp::*;
    match exp {
        Id(id) => Id(SSAName::new(*id)),
        Ref(reg) => Ref(SSAName::new(*reg)),
        Bool(b) => Bool(*b),
        Bits(bv) => Bits(*bv),
        String(s) => String(s.clone()),
        Unit => Unit,
        I64(n) => I64(*n),
        I128(n) => I128(*n),
        Undefined(ty) => Undefined(block_ty(ty)),
        Struct(s, fields) => {
            Struct(SSAName::new(*s), fields.iter().map(|(field, exp)| (SSAName::new(*field), block_exp(exp))).collect())
        }
        Kind(ctor, exp) => Kind(SSAName::new(*ctor), Box::new(block_exp(exp))),
        Unwrap(ctor, exp) => Unwrap(SSAName::new(*ctor), Box::new(block_exp(exp))),
        Field(exp, field) => Field(Box::new(block_exp(exp)), SSAName::new(*field)),
        Call(op, args) => Call(*op, args.iter().map(block_exp).collect()),
    }
}

fn block_instrs<B: BV>(instrs: &[LabeledInstr<B>]) -> Vec<BlockInstr<B>> {
    use BlockInstr::*;

    instrs
        .iter()
        .enumerate()
        .map(|(i, instr)| {
            // We should never have jump targets into the middle of a
            // basic block, so all instructions other than the first
            // should be unlabelled.
            assert!(i == 0 || instr.is_unlabeled());

            match instr.strip_ref() {
                Instr::Decl(v, ty) => Decl(SSAName::new(*v), block_ty(ty)),
                Instr::Init(v, ty, exp) => Init(SSAName::new(*v), block_ty(ty), block_exp(exp)),
                Instr::Copy(loc, exp) => Copy(BlockLoc::from(loc), block_exp(exp)),
                Instr::Monomorphize(v) => Monomorphize(SSAName::new(*v)),
                Instr::Call(loc, ext, f, args) => {
                    Call(BlockLoc::from(loc), *ext, *f, args.iter().map(block_exp).collect())
                }
                Instr::PrimopUnary(loc, fptr, exp) => PrimopUnary(BlockLoc::from(loc), *fptr, block_exp(exp)),
                Instr::PrimopBinary(loc, fptr, exp1, exp2) => {
                    PrimopBinary(BlockLoc::from(loc), *fptr, block_exp(exp1), block_exp(exp2))
                }
                Instr::PrimopVariadic(loc, fptr, args) => {
                    PrimopVariadic(BlockLoc::from(loc), *fptr, args.iter().map(block_exp).collect())
                }
                // All other cases should be terminators
                _ => panic!("Invalid block instruction {:?}", instr),
            }
        })
        .collect()
}

struct DominanceFrontiers {
    frontiers: Vec<HashSet<NodeIndex>>,
}

impl DominanceFrontiers {
    /// Dominance frontier algorithm from 'A Simple, Fast Dominance
    /// Algorithm' by Cooper et al.
    fn from_graph<N, E>(graph: &Graph<N, E>, doms: &Dominators<NodeIndex>) -> Self {
        let mut frontiers = vec![HashSet::new(); graph.node_count()];

        for b in graph.node_indices() {
            let mut predecessors = graph.neighbors_directed(b, Direction::Incoming);
            if let Some(first) = predecessors.next() {
                if let Some(second) = predecessors.next() {
                    for p in [first, second].iter().copied().chain(predecessors) {
                        let mut runner = p;
                        while runner != doms.immediate_dominator(b).unwrap() {
                            frontiers[runner.index()].insert(b);
                            runner = doms.immediate_dominator(runner).unwrap()
                        }
                    }
                }
            }
        }

        DominanceFrontiers { frontiers }
    }

    fn get(&self, n: NodeIndex) -> &HashSet<NodeIndex> {
        &self.frontiers[n.index()]
    }
}

struct DominatorTree {
    tree: HashMap<NodeIndex, Vec<NodeIndex>>,
}

impl DominatorTree {
    fn children(&self, n: NodeIndex) -> Option<&[NodeIndex]> {
        self.tree.get(&n).map(|v| &**v)
    }
}

impl<B: BV> CFG<B> {
    /// Construct a control flow graph from a slice of labeled
    /// instructions. Note that the set of labels should be pruned
    /// with [super::prune_labels], otherwise the control flow graph
    /// will end up containing redundant blocks.
    pub fn new(instrs: &[LabeledInstr<B>]) -> Self {
        let mut remaining = instrs;
        let mut graph = Graph::new();
        let mut block_indices: Vec<NodeIndex> = Vec::new();

        while let Some((before, terminator_label, terminator, after)) = split_terminator(remaining) {
            remaining = after;
            block_indices.push(graph.add_node(Block {
                label: block_label(before, terminator_label),
                phis: Vec::new(),
                instrs: block_instrs(before),
                terminator,
            }))
        }

        let mut targets: HashMap<usize, NodeIndex> = HashMap::new();

        for ix in graph.node_indices() {
            if let Some(label) = graph.node_weight(ix).unwrap().label {
                targets.insert(label, ix);
            }
        }

        // Consecutive blocks get fallthrough edges either for regular
        // control flow into a label (continue), or for jumps not
        // taken.
        for consecutive in block_indices.windows(2) {
            match *consecutive {
                [ix1, ix2] => match graph.node_weight(ix1).unwrap().terminator {
                    Terminator::Continue => {
                        graph.add_edge(ix1, ix2, Edge::Continue);
                    }
                    Terminator::Jump(_, _, _) => {
                        graph.add_edge(ix1, ix2, Edge::Jump(false));
                    }
                    _ => (),
                },
                _ => unreachable!(),
            }
        }

        for ix in &block_indices {
            match graph[*ix].terminator {
                Terminator::Jump(_, target, _) => {
                    let destination =
                        targets.get(&target).unwrap_or_else(|| panic!("No block found for jump target {}!", target));
                    graph.add_edge(*ix, *destination, Edge::Jump(true));
                }
                Terminator::Goto(target) => {
                    let destination =
                        targets.get(&target).unwrap_or_else(|| panic!("No block found for goto target {}!", target));
                    graph.add_edge(*ix, *destination, Edge::Goto);
                }
                _ => (),
            }
        }

        CFG { root: *block_indices.first().expect("Control flow graph has zero blocks!"), graph }
    }

    fn dominator_tree(&self, doms: &Dominators<NodeIndex>) -> DominatorTree {
        let mut tree: HashMap<_, Vec<_>> = HashMap::new();

        for ix in self.graph.node_indices() {
            if let Some(idom) = doms.immediate_dominator(ix) {
                tree.entry(idom).or_default().push(ix)
            }
        }

        DominatorTree { tree }
    }

    fn node_writes(&self) -> Vec<HashSet<Name>> {
        let mut writes = vec![HashSet::new(); self.graph.node_count()];

        for ix in self.graph.node_indices() {
            for instr in &self.graph.node_weight(ix).unwrap().instrs {
                if let Some(id) = instr.write() {
                    writes[ix.index()].insert(id);
                }
            }
        }

        writes
    }

    fn all_vars(&self) -> HashSet<Name> {
        let mut vars = HashSet::new();

        vars.insert(RETURN);

        for ix in self.graph.node_indices() {
            for instr in &self.graph[ix].instrs {
                if let Some(id) = instr.declares() {
                    vars.insert(id);
                }
            }
        }

        vars
    }

    /// Returns a HashMap of all variables declared in a CFG. Also
    /// includes the special RETURN variable which is used to signal
    /// the return value of a function, hence why the return type of
    /// the function is also passed as an argument.
    pub fn all_vars_typed(&self, ret_ty: &Ty<Name>) -> HashMap<Name, Ty<Name>> {
        let mut vars = HashMap::new();

        vars.insert(RETURN, ret_ty.clone());

        for ix in self.graph.node_indices() {
            for instr in &self.graph[ix].instrs {
                if let Some((id, ty)) = instr.declares_typed() {
                    vars.insert(id, ty);
                }
            }
        }

        vars
    }

    fn place_phi_functions(&mut self, frontiers: &DominanceFrontiers, all_vars: &HashSet<Name>) {
        let node_writes: Vec<HashSet<Name>> = self.node_writes();
        let mut needs_phi: HashMap<Name, HashSet<NodeIndex>> = HashMap::new();
        let mut defsites: HashMap<Name, HashSet<NodeIndex>> = HashMap::new();

        for ix in self.graph.node_indices() {
            for a in &node_writes[ix.index()] {
                defsites.entry(*a).or_default().insert(ix);
            }
        }

        for a in all_vars {
            let mut worklist: Vec<NodeIndex> = defsites.get_mut(a).unwrap().drain().collect();

            while !worklist.is_empty() {
                let n = worklist.pop().unwrap();

                for y in frontiers.get(n) {
                    if !needs_phi.entry(*a).or_default().contains(y) {
                        let num_preds = self.graph.edges_directed(*y, Direction::Incoming).count();
                        self.graph.node_weight_mut(*y).unwrap().insert_phi(*a, num_preds);
                        needs_phi.entry(*a).or_default().insert(*y);
                        if node_writes[y.index()].contains(a) {
                            worklist.push(*y)
                        }
                    }
                }
            }
        }
    }

    fn rename_node(
        &mut self,
        n: NodeIndex,
        dominator_tree: &DominatorTree,
        counts: &mut HashMap<Name, i32>,
        stacks: &mut HashMap<Name, Vec<i32>>,
    ) {
        self.graph[n].rename(counts, stacks);

        let succs: Vec<NodeIndex> = self.graph.neighbors_directed(n, Direction::Outgoing).collect();
        for succ in succs {
            let mut j = usize::MAX;
            for (k, pred) in self.graph.neighbors_directed(succ, Direction::Incoming).enumerate() {
                if pred == n {
                    j = k;
                    break;
                }
            }
            assert!(j != usize::MAX);

            self.graph[succ].rename_phi_arg(j, stacks)
        }

        if let Some(children) = dominator_tree.children(n) {
            for child in children {
                self.rename_node(*child, dominator_tree, counts, stacks)
            }
        }

        for instr in &self.graph.node_weight(n).unwrap().instrs {
            if let Some(name) = instr.write() {
                stacks.get_mut(&name).and_then(Vec::pop);
            }
        }
    }

    fn rename(&mut self, dominator_tree: &DominatorTree, all_vars: &HashSet<Name>) {
        let mut counts = HashMap::new();
        let mut stacks: HashMap<Name, Vec<i32>> = HashMap::new();

        for a in all_vars {
            stacks.insert(*a, vec![0]);
        }

        self.rename_node(self.root, dominator_tree, &mut counts, &mut stacks)
    }

    /// Put the CFG into single static assignment (SSA) form.
    pub fn ssa(&mut self) {
        let dominators = dominators::simple_fast(&self.graph, self.root);
        let dominator_tree = self.dominator_tree(&dominators);
        let frontiers = DominanceFrontiers::from_graph(&self.graph, &dominators);
        let all_vars: HashSet<Name> = self.all_vars();
        self.place_phi_functions(&frontiers, &all_vars);
        self.rename(&dominator_tree, &all_vars);
    }

    /// Generate a dot file of the CFG. For debugging.
    pub fn dot(&self, output: &mut dyn Write, symtab: &Symtab) -> std::io::Result<()> {
        writeln!(output, "digraph CFG {{")?;

        for ix in self.graph.node_indices() {
            let node = self.graph.node_weight(ix).unwrap();
            write!(output, "  n{} [shape=box;style=filled;label=\"", ix.index())?;
            for (id, args) in &node.phis {
                id.write(output, symtab)?;
                write!(output, " = Φ")?;
                for (i, arg) in args.iter().enumerate() {
                    if i == 0 {
                        write!(output, "(")?
                    } else {
                        write!(output, ", ")?
                    }
                    arg.write(output, symtab)?
                }
                write!(output, ")\\n")?;
            }
            writeln!(output, "\"]")?
        }

        for edge in self.graph.edge_indices() {
            if let Some((ix1, ix2)) = self.graph.edge_endpoints(edge) {
                writeln!(output, "  n{} -> n{}", ix1.index(), ix2.index())?
            }
        }

        writeln!(output, "}}")
    }
}
