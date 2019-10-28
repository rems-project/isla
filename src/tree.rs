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

use std::sync::Arc;
use std::collections::HashMap;

mod smtlib {
    pub enum Ty {
        Bool,
        BitVec(u32)
    }

    pub enum Def {
        DeclareConst(u32, Ty)
    }
}

use smtlib::*;

enum Tree {
    Root,
    Branch {
        trace: Vec<smtlib::Def>,
        parent: Arc<Tree>
    }
}

struct Solver<'ctx> {
    ctx: &'ctx z3::Context,
    decls: HashMap<u32, z3::FuncDecl<'ctx>>,
    path: Tree,
}

impl<'ctx> Solver<'ctx> {
    fn interpret_type(&self, ty: &Ty) -> z3::Sort<'ctx> {
        match ty {
            Ty::Bool => z3::Sort::bool(self.ctx),
            Ty::BitVec(n) => z3::Sort::bitvector(self.ctx, *n)
        }
    }

    fn push(&mut self, def: Def) {
        match def {
            Def::DeclareConst(name, ty) => {
                self.decls.insert(name, z3::FuncDecl::new(
                    self.ctx,
                    name,
                    &[],
                    &self.interpret_type(&ty),
                ));
            }
        }
    }
}

fn replay_root() {}

fn replay_branch(trace: &[smtlib::Def]) {}

fn replay(path: &Tree) {
    match path {
        Tree::Root => replay_root(),
        Tree::Branch { trace, parent } => {
            replay(parent);
            replay_branch(trace)
        }
    }
}
