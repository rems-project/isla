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

use libc::c_int;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::Arc;
use z3_sys::*;

mod smtlib {
    use crate::ast;

    pub enum Ty {
        Bool,
        BitVec(u32),
    }

    pub enum Def {
        DeclareConst(u32, Ty),
        Assert(ast::Exp<u32>),
    }
}

use smtlib::*;

enum Tree {
    Root,
    Branch {
        trace: Vec<smtlib::Def>,
        parent: Arc<Tree>,
    },
}

struct Sort<'ctx> {
    sort: Z3_sort,
    _lifetime: PhantomData<&'ctx ()>,
}

struct Ast<'ctx> {
    ast: Z3_ast,
    _lifetime: PhantomData<&'ctx ()>,
}

struct Smt<'ctx> {
    ctx: Z3_context,
    solver: Z3_solver,
    path: Tree,
    _lifetime: PhantomData<&'ctx ()>,
}

fn smt_type<'ctx>(smt: &'ctx Smt<'ctx>, ty: &Ty) -> Sort<'ctx> {
    unsafe {
        match ty {
            Ty::Bool => Sort {
                sort: Z3_mk_bool_sort(smt.ctx),
                _lifetime: PhantomData,
            },
            Ty::BitVec(n) => Sort {
                sort: Z3_mk_bv_sort(smt.ctx, *n),
                _lifetime: PhantomData,
            },
        }
    }
}

impl<'ctx> Smt<'ctx> {
    fn push(&'ctx mut self, def: Def) {
        match def {
            Def::DeclareConst(name, ty) => unsafe {
                let sym = Z3_mk_int_symbol(self.ctx, name as c_int);
                ()
            },

            Def::Assert(exp) => (),
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
