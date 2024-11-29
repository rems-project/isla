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
use petgraph::graph::{EdgeIndex, Graph, NodeIndex};
use petgraph::visit::EdgeRef;
use petgraph::{Directed, Direction};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io::Write;
use std::usize;

use super::*;

use crate::primop::{Binary, Unary, Variadic};
use crate::source_loc::SourceLoc;

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

    pub(crate) fn unssa_orig(self, symtab: &mut Symtab) -> Name {
        assert!(self.number < 0, "{}/{}", zencode::decode(symtab.to_str(self.name)), self.number);
        self.name
    }

    pub(crate) fn unssa_ex(self, symtab: &mut Symtab, generated: &mut HashMap<SSAName, Name>) -> Name {
        if self.number < 0 {
            self.name
        } else if let Some(name) = generated.get(&self) {
            *name
        } else {
            panic!(
                "Name must have been generated previously {}/{}",
                zencode::decode(symtab.to_str(self.name)),
                self.number
            )
        }
    }

    fn write(self, output: &mut dyn Write, symtab: &Symtab) -> std::io::Result<()> {
        if self.number >= 0 {
            write!(output, "{}/{}", zencode::decode(symtab.to_str(self.name)), self.number)
        } else {
            write!(output, "{}_{:?}", zencode::decode(symtab.to_str(self.name)), self.name)
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
        Float(fpty) => Float(*fpty),
        RoundingMode => RoundingMode,
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
            BlockLoc::Id(id) => *id,
            BlockLoc::Field(loc, _, _) | BlockLoc::Addr(loc) => loc.id(),
        }
    }

    fn ids(&self) -> (SSAName, Option<SSAName>) {
        match self {
            BlockLoc::Id(id) => (*id, None),
            BlockLoc::Field(loc, base_id, _) => (loc.id(), Some(*base_id)),
            BlockLoc::Addr(loc) => (loc.id(), None),
        }
    }

    fn collect_variables<'a>(&'a mut self, vars: &mut Vec<Variable<'a, SSAName>>) {
        match self {
            BlockLoc::Id(id) => vars.push(Variable::Declaration(id)),
            BlockLoc::Field(loc, id, _) => {
                loc.collect_variables(vars);
                vars.push(Variable::Usage(id))
            }
            BlockLoc::Addr(loc) => loc.collect_variables(vars),
        }
    }

    fn output(&self, output: &mut dyn Write, symtab: &Symtab) -> std::io::Result<()> {
        match self {
            BlockLoc::Id(id) => id.write(output, symtab),
            _ => write!(output, "O"),
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
pub enum BlockInstr<B> {
    Decl(SSAName, Ty<SSAName>, SourceLoc),
    Init(SSAName, Ty<SSAName>, Exp<SSAName>, SourceLoc),
    Copy(BlockLoc, Exp<SSAName>, SourceLoc),
    Monomorphize(SSAName, SourceLoc),
    Call(BlockLoc, bool, Name, Vec<Exp<SSAName>>, SourceLoc),
    PrimopUnary(BlockLoc, Unary<B>, Exp<SSAName>, SourceLoc),
    PrimopBinary(BlockLoc, Binary<B>, Exp<SSAName>, Exp<SSAName>, SourceLoc),
    PrimopVariadic(BlockLoc, Variadic<B>, Vec<Exp<SSAName>>, SourceLoc),
}

impl<B: BV> BlockInstr<B> {
    // Returns the written-to variable, and its previous name if it's a field access
    pub fn write_ssa(&self) -> Option<(SSAName, Option<SSAName>)> {
        use BlockInstr::*;
        match self {
            Decl(id, _, _) | Init(id, _, _, _) => Some((*id, None)),
            Copy(loc, _, _)
            | Call(loc, _, _, _, _)
            | PrimopUnary(loc, _, _, _)
            | PrimopBinary(loc, _, _, _, _)
            | PrimopVariadic(loc, _, _, _) => Some(loc.ids()),
            _ => None,
        }
    }

    pub fn write(&self) -> Option<Name> {
        self.write_ssa().map(|(id, _)| id.name)
    }

    pub fn declares(&self) -> Option<Name> {
        use BlockInstr::*;
        match self {
            Decl(id, _, _) | Init(id, _, _, _) => Some(id.name),
            _ => None,
        }
    }

    fn declares_typed(&self) -> Option<(Name, Ty<Name>)> {
        use BlockInstr::*;
        match self {
            Decl(id, ty, _) | Init(id, ty, _, _) => Some((id.name, unssa_ty(ty))),
            _ => None,
        }
    }

    fn collect_variables<'a>(&'a mut self, vars: &mut Vec<Variable<'a, SSAName>>) {
        use BlockInstr::*;
        match self {
            Decl(id, _, _) => vars.push(Variable::Declaration(id)),
            Init(id, _, exp, _) => {
                vars.push(Variable::Declaration(id));
                exp.collect_variables(vars)
            }
            Copy(loc, exp, _) => {
                loc.collect_variables(vars);
                exp.collect_variables(vars)
            }
            Monomorphize(id, _) => vars.push(Variable::Usage(id)),
            Call(loc, _, _, args, _) => {
                loc.collect_variables(vars);
                args.iter_mut().for_each(|exp| exp.collect_variables(vars))
            }
            PrimopUnary(loc, _, exp, _) => {
                loc.collect_variables(vars);
                exp.collect_variables(vars)
            }
            PrimopBinary(loc, _, lhs, rhs, _) => {
                loc.collect_variables(vars);
                lhs.collect_variables(vars);
                rhs.collect_variables(vars)
            }
            PrimopVariadic(loc, _, args, _) => {
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

    pub fn is_pure(&self, symtab: &Symtab) -> bool {
        match self {
            BlockInstr::Call(_, _, f, _, _) => {
                if let Some(u) = symtab.get("zUnreachable") {
                    *f != u
                } else {
                    false
                }
            }
            _ => true,
        }
    }

    fn output(&self, output: &mut dyn Write, symtab: &Symtab) -> std::io::Result<()> {
        use BlockInstr::*;
        match self {
            Decl(id, _, _) => id.write(output, symtab),
            Init(id, _, _, _) => {
                id.write(output, symtab)?;
                write!(output, " = N")
            }
            Call(loc, _, _, _, _) => {
                loc.output(output, symtab)?;
                write!(output, " = C")
            }
            Copy(loc, _, _) => {
                loc.output(output, symtab)?;
                write!(output, " = P")
            }
            _ => write!(output, "I"),
        }
    }
}

impl<B: fmt::Debug> fmt::Debug for BlockInstr<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BlockInstr::*;
        match self {
            Decl(id, ty, _) => write!(f, "{:?} : {:?}", id, ty),
            Init(id, ty, exp, _) => write!(f, "{:?} : {:?} = {:?}", id, ty, exp),
            Copy(loc, exp, _) => write!(f, "{:?} = {:?}", loc, exp),
            Monomorphize(id, _) => write!(f, "mono {:?}", id),
            Call(loc, ext, id, args, _) => write!(f, "{:?} = {:?}<{:?}>({:?})", loc, id, ext, args),
            _ => write!(f, "primop"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum JumpTree {
    Goto(usize),
    Cond(Exp<SSAName>, Box<JumpTree>, Box<JumpTree>),
}

impl JumpTree {
    fn collect_variables<'a>(&'a mut self, vars: &mut Vec<Variable<'a, SSAName>>) {
        match self {
            JumpTree::Goto(_) => (),
            JumpTree::Cond(exp, lhs, rhs) => {
                exp.collect_variables(vars);
                lhs.collect_variables(vars);
                rhs.collect_variables(vars)
            }
        }
    }

    fn collect_targets(&self, targets: &mut HashSet<usize>) {
        match self {
            JumpTree::Goto(label) => {
                targets.insert(*label);
            }
            JumpTree::Cond(_, lhs, rhs) => {
                lhs.collect_targets(targets);
                rhs.collect_targets(targets)
            }
        }
    }

    pub fn targets(&self) -> Vec<usize> {
        let mut targets = HashSet::new();
        self.collect_targets(&mut targets);
        targets.drain().collect()
    }

    pub fn condition_for(&self, target: usize) -> Exp<SSAName> {
        match self {
            JumpTree::Goto(label) => Exp::Bool(*label == target),
            JumpTree::Cond(exp, lhs, rhs) => short_circuit_or(
                short_circuit_and(exp.clone(), lhs.condition_for(target)),
                short_circuit_and(exp.clone().bool_not(), rhs.condition_for(target)),
            ),
        }
    }

    fn insert(&mut self, mut path: JumpPath, subtree: JumpTree) {
        if let Some(left) = path.next() {
            match self {
                JumpTree::Cond(_, lhs, rhs) => {
                    if left {
                        lhs.insert(path, subtree)
                    } else {
                        rhs.insert(path, subtree)
                    }
                }
                JumpTree::Goto(_) => panic!("Invalid path"),
            }
        } else {
            match self {
                JumpTree::Goto(_) => *self = subtree,
                JumpTree::Cond(_, _, _) => panic!("Invalid path"),
            }
        }
    }

    pub(crate) fn extract(&self, mut path: JumpPath) -> Exp<SSAName> {
        if let Some(left) = path.next() {
            match self {
                JumpTree::Cond(exp, lhs, rhs) => {
                    if left {
                        short_circuit_and(exp.clone(), lhs.extract(path))
                    } else {
                        short_circuit_and(exp.clone().bool_not(), rhs.extract(path))
                    }
                }
                JumpTree::Goto(_) => panic!("Invalid path"),
            }
        } else {
            Exp::Bool(true)
        }
    }
}

#[derive(Clone, Debug)]
pub struct JumpPath {
    path: u64,
    depth: u8,
}

impl fmt::Display for JumpPath {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{:b}", self.depth, self.path)
    }
}

impl JumpPath {
    pub fn goto_path() -> Self {
        JumpPath { path: 0, depth: 0 }
    }

    pub fn true_path() -> Self {
        JumpPath { path: 1, depth: 1 }
    }

    pub fn false_path() -> Self {
        JumpPath { path: 0, depth: 1 }
    }

    pub fn append(&self, suffix: Self) -> Self {
        JumpPath { path: self.path | (suffix.path << self.depth), depth: self.depth + suffix.depth }
    }
}

impl Iterator for JumpPath {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.depth == 0 {
            None
        } else {
            let step = (self.path & 0b1) == 0b1;
            self.depth -= 1;
            self.path >>= 1;
            Some(step)
        }
    }
}

/// An instruction that can only occur at the end of a basic block.
#[derive(Debug)]
pub enum Terminator {
    Continue,
    Goto(usize),
    Jump(Exp<SSAName>, usize, SourceLoc),
    MultiJump(JumpTree),
    Exit(ExitCause, SourceLoc),
    Arbitrary,
    End,
}

impl Terminator {
    fn collect_variables<'a>(&'a mut self, vars: &mut Vec<Variable<'a, SSAName>>) {
        match self {
            Terminator::Jump(exp, _, _) => exp.collect_variables(vars),
            Terminator::MultiJump(tree) => tree.collect_variables(vars),
            _ => (),
        }
    }

    fn variables(&mut self) -> Variables<'_, SSAName> {
        let mut vec = Vec::new();
        self.collect_variables(&mut vec);
        Variables::from_vec(vec)
    }

    fn output(&self, output: &mut dyn Write, _symtab: &Symtab) -> std::io::Result<()> {
        use Terminator::*;
        match self {
            Continue => write!(output, "continue"),
            Goto(label) => write!(output, "goto {}", label),
            Jump(_, label, _) => write!(output, "jump {}", label),
            MultiJump(_) => write!(output, "multi"),
            Exit(cause, _) => write!(output, "exit {:?}", cause),
            Arbitrary => write!(output, "arbitrary"),
            End => write!(output, "end"),
        }
    }

    fn is_multi_jump(&self) -> bool {
        matches!(self, Terminator::MultiJump(_))
    }

    pub(crate) fn jump_tree(&self) -> Option<&JumpTree> {
        match self {
            Terminator::MultiJump(tree) => Some(tree),
            _ => None,
        }
    }

    fn jump_tree_mut(&mut self) -> Option<&mut JumpTree> {
        match self {
            Terminator::MultiJump(tree) => Some(tree),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct Block<B> {
    pub label: Option<usize>,
    pub phis: Vec<(SSAName, Vec<SSAName>)>,
    pub instrs: Vec<BlockInstr<B>>,
    pub terminator: Terminator,
}

impl<B: BV> Block<B> {
    fn insert_phi(&mut self, id: Name, num_preds: usize) {
        self.phis.push((SSAName::new(id), vec![SSAName::new(id); num_preds]))
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

    pub fn is_pure(&self, symtab: &Symtab) -> bool {
        !self.instrs.iter().any(|instr| !instr.is_pure(symtab))
    }
}

/// An edge between basic blocks in the control flow graph. The edge
/// corresponds to the [Terminator] of the node the edge comes from.
#[derive(Debug)]
pub enum Edge {
    /// True if the Jump expression was true, and the jump was taken.
    Jump(bool),
    MultiJump(JumpPath),
    Goto,
    Continue,
}

impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Edge::Jump(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            Edge::MultiJump(path) => path.fmt(f),
            Edge::Goto => write!(f, "goto"),
            Edge::Continue => write!(f, "continue"),
        }
    }
}

impl Edge {
    fn is_jump(&self, cond: bool) -> Option<bool> {
        match self {
            Edge::Jump(b) => Some(*b == cond),
            _ => None,
        }
    }

    pub(crate) fn path(&self) -> Option<JumpPath> {
        match self {
            Edge::MultiJump(path) => Some(path.clone()),
            _ => None,
        }
    }
}

pub struct CFG<B> {
    pub root: NodeIndex,
    pub graph: Graph<Block<B>, (usize, Edge), Directed>,
}

/// Takes the final instruction in a basic block, and returns the
/// appropriate terminator for that block.
fn to_terminator<B: BV>(instr: &Instr<Name, B>) -> Terminator {
    match instr {
        Instr::Goto(target) => Terminator::Goto(*target),
        Instr::Jump(cond, target, info) => Terminator::Jump(block_exp(cond), *target, *info),
        Instr::Exit(cause, info) => Terminator::Exit(*cause, *info),
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
            Instr::Goto(_) | Instr::Jump(_, _, _) | Instr::Exit(_, _) | Instr::Arbitrary | Instr::End => {
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
        Float(fpty) => Float(*fpty),
        RoundingMode => RoundingMode,
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
                Instr::Decl(v, ty, info) => Decl(SSAName::new(*v), block_ty(ty), *info),
                Instr::Init(v, ty, exp, info) => Init(SSAName::new(*v), block_ty(ty), block_exp(exp), *info),
                Instr::Copy(loc, exp, info) => Copy(BlockLoc::from(loc), block_exp(exp), *info),
                Instr::Monomorphize(v, info) => Monomorphize(SSAName::new(*v), *info),
                Instr::Call(loc, ext, f, args, info) => {
                    Call(BlockLoc::from(loc), *ext, *f, args.iter().map(block_exp).collect(), *info)
                }
                Instr::PrimopUnary(loc, fptr, exp, info) => {
                    PrimopUnary(BlockLoc::from(loc), *fptr, block_exp(exp), *info)
                }
                Instr::PrimopBinary(loc, fptr, exp1, exp2, info) => {
                    PrimopBinary(BlockLoc::from(loc), *fptr, block_exp(exp1), block_exp(exp2), *info)
                }
                Instr::PrimopVariadic(loc, fptr, args, info) => {
                    PrimopVariadic(BlockLoc::from(loc), *fptr, args.iter().map(block_exp).collect(), *info)
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
                        let mut runner = Some(p);
                        while runner.is_some() && runner != doms.immediate_dominator(b) {
                            frontiers[runner.unwrap().index()].insert(b);
                            runner = doms.immediate_dominator(runner.unwrap());
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
                        graph.add_edge(ix1, ix2, (0, Edge::Continue));
                    }
                    Terminator::Jump(_, _, _) => {
                        graph.add_edge(ix1, ix2, (0, Edge::Jump(false)));
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
                    graph.add_edge(*ix, *destination, (0, Edge::Jump(true)));
                }
                Terminator::Goto(target) => {
                    let destination =
                        targets.get(&target).unwrap_or_else(|| panic!("No block found for goto target {}!", target));
                    graph.add_edge(*ix, *destination, (0, Edge::Goto));
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
            if let Some(defsite) = defsites.get_mut(a) {
                let mut worklist: Vec<NodeIndex> = defsite.drain().collect();

                while let Some(n) = worklist.pop() {
                    for y in frontiers.get(n) {
                        if !needs_phi.entry(*a).or_default().contains(y) {
                            let num_preds = self.graph.edges_directed(*y, Direction::Incoming).count();
                            self.graph.node_weight_mut(*y).unwrap().insert_phi(*a, num_preds);
                            needs_phi.entry(*a).or_default().insert(*y);
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
        let old_stacks = stacks.clone();

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

        *stacks = old_stacks
    }

    fn rename(&mut self, dominator_tree: &DominatorTree, all_vars: &HashSet<Name>) {
        let mut counts = HashMap::new();
        let mut stacks: HashMap<Name, Vec<i32>> = HashMap::new();

        for a in all_vars {
            stacks.insert(*a, vec![0]);
        }

        self.rename_node(self.root, dominator_tree, &mut counts, &mut stacks)
    }

    fn fix_edge_numbers(&mut self) {
        for edge in self.graph.edge_indices() {
            if let Some((_, ix2)) = self.graph.edge_endpoints(edge) {
                let mut edge_number = 0;
                for (i, pred_edge) in self.graph.edges_directed(ix2, Direction::Incoming).enumerate() {
                    if pred_edge.id() == edge {
                        edge_number = i + 1;
                        break;
                    }
                }
                self.graph[edge].0 = edge_number
            }
        }
    }

    /// Put the CFG into single static assignment (SSA) form.
    pub fn ssa_with_dominators(&mut self) -> Dominators<NodeIndex> {
        let dominators = dominators::simple_fast(&self.graph, self.root);
        let dominator_tree = self.dominator_tree(&dominators);
        let frontiers = DominanceFrontiers::from_graph(&self.graph, &dominators);
        let all_vars: HashSet<Name> = self.all_vars();
        self.place_phi_functions(&frontiers, &all_vars);
        self.rename(&dominator_tree, &all_vars);
        self.fix_edge_numbers();
        dominators
    }

    pub fn ssa(&mut self) {
        self.ssa_with_dominators();
    }

    /// This function gives every block a label, and replaces Continue
    /// terminators with Goto terminators, and Continue edges with
    /// Goto edges.  This puts the graph into a slightly more
    /// consistent form that can be easier to work with. Returns the
    /// maximum label in the graph.
    ///
    /// # Panics
    ///
    /// Panics if the graph is malformed - when nodes with continue
    /// terminators have multiple children.
    pub fn label_every_block(&mut self) -> usize {
        let mut max_label = 0;

        for ix in self.graph.node_indices() {
            max_label = std::cmp::max(max_label, self.graph[ix].label.unwrap_or(0))
        }

        for ix in self.graph.node_indices() {
            if self.graph[ix].label.is_none() {
                max_label += 1;
                self.graph[ix].label = Some(max_label)
            }
        }

        for ix in self.graph.node_indices() {
            if let Terminator::Continue = self.graph[ix].terminator {
                let mut children = self.graph.neighbors_directed(ix, Direction::Outgoing);
                // A node with a continue terminator must have a
                // single child. Panic if the graph is malformed.
                let child = children.next().unwrap();
                assert!(children.next().is_none());

                let child_label = self.graph[child].label.unwrap();
                let edge = self.graph.find_edge(ix, child).unwrap();

                self.graph[edge].1 = Edge::Goto;
                self.graph[ix].terminator = Terminator::Goto(child_label)
            }
        }

        max_label
    }

    pub fn to_multi_jump(&mut self) {
        for ix in self.graph.node_indices() {
            match self.graph[ix].terminator {
                Terminator::Goto(label) => {
                    let mut children = self.graph.neighbors_directed(ix, Direction::Outgoing);
                    let child = children.next().unwrap();
                    assert!(children.next().is_none());
                    let edge = self.graph.find_edge(ix, child).unwrap();

                    self.graph[edge].1 = Edge::MultiJump(JumpPath::goto_path());
                    self.graph[ix].terminator = Terminator::MultiJump(JumpTree::Goto(label))
                }

                Terminator::Jump(ref exp, label, _) => {
                    let exp = exp.clone();

                    let mut children = self.graph.neighbors_directed(ix, Direction::Outgoing);
                    let child1 = children.next().unwrap();
                    let child2 = children.next().unwrap();
                    assert!(children.next().is_none());

                    let edge1 = self.graph.find_edge(ix, child1).unwrap();
                    let edge2 = self.graph.find_edge(ix, child2).unwrap();

                    let (true_edge, true_child, false_edge, false_child) =
                        if let Some(cond) = self.graph[edge1].1.is_jump(true) {
                            if cond {
                                (edge1, child1, edge2, child2)
                            } else {
                                (edge2, child2, edge1, child1)
                            }
                        } else {
                            panic!("Malformed jump terminator edges")
                        };

                    assert!(self.graph[true_child].label.unwrap() == label);

                    self.graph[true_edge].1 = Edge::MultiJump(JumpPath::true_path());
                    self.graph[false_edge].1 = Edge::MultiJump(JumpPath::false_path());

                    self.graph[ix].terminator = Terminator::MultiJump(JumpTree::Cond(
                        exp,
                        Box::new(JumpTree::Goto(self.graph[true_child].label.unwrap())),
                        Box::new(JumpTree::Goto(self.graph[false_child].label.unwrap())),
                    ))
                }

                _ => (),
            }
        }
    }

    fn merge_multi_jump(&mut self) -> bool {
        let mut remove: Option<(NodeIndex, Vec<EdgeIndex>, NodeIndex)> = None;

        for edge in self.graph.edge_indices() {
            if let Some((ix1, ix2)) = self.graph.edge_endpoints(edge) {
                let multi_parent = self.graph.neighbors_directed(ix2, Direction::Incoming).any(|parent| parent != ix1);

                if self.graph[ix1].terminator.is_multi_jump()
                    && self.graph[ix2].terminator.is_multi_jump()
                    && self.graph[ix2].instrs.is_empty()
                    && self.graph[ix2].phis.is_empty()
                    && !multi_parent
                {
                    let edges = self.graph.edges_connecting(ix1, ix2).map(|edge| edge.id()).collect();
                    remove = Some((ix1, edges, ix2));
                    break;
                }
            }
        }

        if let Some((ix1, edges, ix2)) = remove {
            for edge in edges {
                let path = self.graph[edge].1.path().unwrap();
                let tree = self.graph[ix2].terminator.jump_tree().unwrap().clone();
                self.graph[ix1].terminator.jump_tree_mut().unwrap().insert(path.clone(), tree);

                let mut next_edges = self.graph.neighbors_directed(ix2, Direction::Outgoing).detach();
                while let Some((next_edge, ix3)) = next_edges.next(&self.graph) {
                    let next_path = self.graph[next_edge].1.path().unwrap();
                    let edge_number = self.graph[next_edge].0;
                    self.graph.add_edge(ix1, ix3, (edge_number, Edge::MultiJump(path.append(next_path))));
                }
            }
            self.graph.remove_node(ix2);
            true
        } else {
            false
        }
    }

    pub fn merge_multi_jumps(&mut self) -> usize {
        let mut count = 0;
        loop {
            if !self.merge_multi_jump() {
                break;
            } else {
                count += 1
            }
        }
        count
    }

    /// Generate a dot file of the CFG. For debugging.
    pub fn dot(&self, output: &mut dyn Write, symtab: &Symtab) -> std::io::Result<()> {
        writeln!(output, "digraph CFG {{")?;

        for ix in self.graph.node_indices() {
            let node = &self.graph[ix];
            write!(
                output,
                "  n{} [shape=box;style=filled;color={};label=\"",
                ix.index(),
                if node.is_pure(symtab) { "green" } else { "red" }
            )?;
            if let Some(label) = node.label {
                write!(output, "{}:\\n", label)?
            }
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
            for instr in &node.instrs {
                instr.output(output, symtab)?;
                write!(output, "\\n")?
            }
            node.terminator.output(output, symtab)?;

            writeln!(output, "\\n\"];")?
        }

        for edge in self.graph.edge_indices() {
            if let Some((ix1, ix2)) = self.graph.edge_endpoints(edge) {
                writeln!(
                    output,
                    "  n{} -> n{} [label=\"{} {}\"];",
                    ix1.index(),
                    ix2.index(),
                    self.graph[edge].0,
                    self.graph[edge].1
                )?
            }
        }

        writeln!(output, "}}")
    }
}
