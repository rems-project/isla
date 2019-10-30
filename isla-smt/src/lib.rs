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
use std::convert::TryInto;
use std::collections::HashMap;
use std::ptr;
use z3_sys::*;

mod smtlib {
    pub enum Ty {
        Bool,
        BitVec(u32),
    }

    pub enum Exp {
        Bits(Vec<bool>),
        Eq(Box<Exp>, Box<Exp>),
        Not(Box<Exp>),
        Var(u32),
    }

    pub enum Def {
        DeclareConst(u32, Ty),
        Assert(Exp),
    }
}

use smtlib::*;

pub struct Config {
    z3_cfg: Z3_config,
}

impl Config {
    pub fn new() -> Self {
        unsafe {
            Config {
                z3_cfg: Z3_mk_config(),
            }
        }
    }
}

impl Drop for Config {
    fn drop(&mut self) {
        unsafe { Z3_del_config(self.z3_cfg) }
    }
}

impl Default for Config {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Context {
    z3_ctx: Z3_context,
}

impl Context {
    pub fn new(cfg: Config) -> Self {
        unsafe {
            Context {
                z3_ctx: Z3_mk_context_rc(cfg.z3_cfg),
            }
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.z3_ctx) }
    }
}

struct Sort<'ctx> {
    z3_sort: Z3_sort,
    ctx: &'ctx Context,
}

impl<'ctx> Sort<'ctx> {
    fn new(ctx: &'ctx Context, ty: &Ty) -> Self {
        unsafe {
            match ty {
                Ty::Bool => {
                    let z3_sort = Z3_mk_bool_sort(ctx.z3_ctx);
                    Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
                    Sort { z3_sort, ctx }
                }
                Ty::BitVec(n) => {
                    let z3_sort = Z3_mk_bv_sort(ctx.z3_ctx, *n);
                    Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
                    Sort { z3_sort, ctx }
                }
            }
        }
    }
}

impl<'ctx> Drop for Sort<'ctx> {
    fn drop(&mut self) {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            Z3_dec_ref(ctx, Z3_sort_to_ast(ctx, self.z3_sort))
        }
    }
}

struct FuncDecl<'ctx> {
    z3_func_decl: Z3_func_decl,
    ctx: &'ctx Context,
}

impl<'ctx> FuncDecl<'ctx> {
    fn new(ctx: &'ctx Context, v: u32, ty: &Ty) -> Self {
        unsafe {
            let name = Z3_mk_int_symbol(ctx.z3_ctx, v as c_int);
            let z3_func_decl =
                Z3_mk_func_decl(ctx.z3_ctx, name, 0, ptr::null(), Sort::new(ctx, ty).z3_sort);
            Z3_inc_ref(ctx.z3_ctx, Z3_func_decl_to_ast(ctx.z3_ctx, z3_func_decl));
            FuncDecl { z3_func_decl, ctx }
        }
    }
}

impl<'ctx> Drop for FuncDecl<'ctx> {
    fn drop(&mut self) {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, self.z3_func_decl))
        }
    }
}

struct Ast<'ctx> {
    z3_ast: Z3_ast,
    ctx: &'ctx Context,
}

macro_rules! z3_unary_op {
    ($i:ident, $arg:ident) => {
        unsafe {
            let z3_ast = $i($arg.ctx.z3_ctx, $arg.z3_ast);
            Z3_inc_ref($arg.ctx.z3_ctx, z3_ast);
            Ast {
                z3_ast,
                ctx: $arg.ctx,
            }
        }
    };
}

macro_rules! z3_binary_op {
    ($i:ident, $lhs:ident, $rhs:ident) => {
        unsafe {
            let z3_ast = $i($lhs.ctx.z3_ctx, $lhs.z3_ast, $rhs.z3_ast);
            Z3_inc_ref($lhs.ctx.z3_ctx, z3_ast);
            Ast {
                z3_ast,
                ctx: $lhs.ctx,
            }
        }
    };
}

impl<'ctx> Ast<'ctx> {
    fn mk_constant(fd: &FuncDecl<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_app(fd.ctx.z3_ctx, fd.z3_func_decl, 0, ptr::null());
            Z3_inc_ref(fd.ctx.z3_ctx, z3_ast);
            Ast {
                z3_ast,
                ctx: fd.ctx,
            }
        }
    }

    fn mk_bv(ctx: &'ctx Context, sz: u32, bits: &[bool]) -> Self {
        unsafe {
            let z3_ast = Z3_mk_bv_numeral(ctx.z3_ctx, sz, bits.as_ptr());
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn mk_not(&self) -> Self {
        z3_unary_op!(Z3_mk_not, self)
    }

    fn mk_eq(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_eq, self, rhs)
    }

    fn mk_bvnot(&self, rhs: &Ast<'ctx>) -> Self {
        z3_unary_op!(Z3_mk_bvnot, self)
    }

    fn mk_bvredand(&self, rhs: &Ast<'ctx>) -> Self {
        z3_unary_op!(Z3_mk_bvredand, self)
    }

    fn mk_bvredor(&self, rhs: &Ast<'ctx>) -> Self {
        z3_unary_op!(Z3_mk_bvredor, self)
    }

    fn mk_bvand(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvand, self, rhs)
    }

    fn mk_bvor(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvor, self, rhs)
    }

    fn mk_bvxor(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvxor, self, rhs)
    }

    fn mk_bvnand(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvnand, self, rhs)
    }

    fn mk_bvnor(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvnor, self, rhs)
    }

    fn mk_bvxnor(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvxnor, self, rhs)
    }

    fn mk_bvneg(&self, rhs: &Ast<'ctx>) -> Self {
        z3_unary_op!(Z3_mk_bvneg, self)
    }

    fn mk_bvadd(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvadd, self, rhs)
    }

    fn mk_bvsub(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsub, self, rhs)
    }

    fn mk_bvmul(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvmul, self, rhs)
    }

    fn mk_bvudiv(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvudiv, self, rhs)
    }

    fn mk_bvsdiv(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsdiv, self, rhs)
    }

    fn mk_bvurem(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvurem, self, rhs)
    }

    fn mk_bvsrem(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsrem, self, rhs)
    }

    fn mk_bvsmod(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsmod, self, rhs)
    }

    fn mk_bvult(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvult, self, rhs)
    }

    fn mk_bvslt(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvslt, self, rhs)
    }

    fn mk_bvule(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvule, self, rhs)
    }

    fn mk_bvsle(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsle, self, rhs)
    }

    fn mk_bvuge(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvuge, self, rhs)
    }

    fn mk_bvsge(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsge, self, rhs)
    }

    fn mk_bvugt(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvugt, self, rhs)
    }

    fn mk_bvsgt(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvsgt, self, rhs)
    }
}

macro_rules! bv {
    ( $bv_string:expr ) => {
        {
            let mut vec = Vec::new();
            for c in $bv_string.chars().rev() {
                if c == '1' {
                    vec.push(true)
                } else if c == '0' {
                    vec.push(false)
                } else {
                    ()
                }
            };
            Bits(vec)
        }
    }
}

impl<'ctx> Drop for Ast<'ctx> {
    fn drop(&mut self) {
        unsafe { Z3_dec_ref(self.ctx.z3_ctx, self.z3_ast) }
    }
}

pub struct Solver<'ctx> {
    decls: HashMap<u32, FuncDecl<'ctx>>,
    z3_solver: Z3_solver,
    ctx: &'ctx Context,
}

impl<'ctx> Drop for Solver<'ctx> {
    fn drop(&mut self) {
        unsafe {
            Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_solver);
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SmtResult {
    Sat,
    Unsat,
    Unknown,
}

use SmtResult::*;

impl<'ctx> Solver<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        unsafe {
            let z3_solver = Z3_mk_simple_solver(ctx.z3_ctx);
            Z3_solver_inc_ref(ctx.z3_ctx, z3_solver);
            Solver {
                ctx,
                z3_solver,
                decls: HashMap::new(),
            }
        }
    }

    fn translate_exp(&mut self, exp: &Exp) -> Ast<'ctx> {
        match exp {
            Exp::Var(v) => match self.decls.get(v) {
                None => panic!("Could not get Z3 func_decl {}", *v),
                Some(fd) => Ast::mk_constant(fd),
            },

            Exp::Bits(bv) => Ast::mk_bv(self.ctx, bv.len().try_into().unwrap(), &bv),

            Exp::Not(exp) => Ast::mk_not(&self.translate_exp(exp)),

            Exp::Eq(lhs, rhs) => Ast::mk_eq(&self.translate_exp(lhs), &self.translate_exp(rhs)),
        }
    }

    fn assert(&mut self, exp: &Exp) {
        let ast = self.translate_exp(exp);
        unsafe {
            Z3_solver_assert(self.ctx.z3_ctx, self.z3_solver, ast.z3_ast);
        }
    }

    pub fn add(&mut self, def: &Def) {
        match def {
            Def::Assert(exp) => self.assert(exp),
            Def::DeclareConst(v, ty) => {
                let fd = FuncDecl::new(&self.ctx, *v, ty);
                self.decls.insert(*v, fd);
            }
        }
    }

    pub fn check_sat(&mut self) -> SmtResult {
        unsafe {
            let result = Z3_solver_check(self.ctx.z3_ctx, self.z3_solver);
            if result == Z3_L_TRUE {
                Sat
            } else if result == Z3_L_FALSE {
                Unsat
            } else {
                Unknown
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Def::*;
    use super::Exp::*;
    use super::SmtResult::*;
    use super::*;

    #[test]
    fn simple_solver() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::new(&ctx);
        solver.add(&DeclareConst(0, Ty::Bool));
        solver.add(&Assert(Var(0)));
        assert!(solver.check_sat() == Sat);
        solver.add(&Assert(Not(Box::new(Var(0)))));
        assert!(solver.check_sat() == Unsat);
    }

    #[test]
    fn bv_macro() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::new(&ctx);
        solver.add(&Assert(Eq(Box::new(bv!("0110")), Box::new(bv!("1001")))));
        assert!(solver.check_sat() == Unsat);
    }
}
