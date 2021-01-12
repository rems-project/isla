// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
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

//! This module defines an interface with the SMT solver, primarily
//! via the [Solver] type. It provides a safe abstraction over the
//! [z3_sys] crate. In addition, all the interaction with the SMT
//! solver is logged as a [Trace] in an SMTLIB-like format, expanded
//! with additional events marking e.g. memory events, the start and
//! end of processor cycles, etc (see the [Event] type). Points in
//! these traces can be snapshotted and shared between threads via the
//! [Checkpoint] type.

use libc::{c_int, c_uint};
use serde::{Deserialize, Serialize};
use z3_sys::*;

use std::collections::HashMap;
use std::convert::TryInto;
use std::error::Error;
use std::ffi::{CStr, CString};
use std::fmt;
use std::io::Write;
use std::mem;
use std::ptr;
use std::sync::Arc;

use crate::concrete::BV;
use crate::error::ExecError;
use crate::ir::{EnumMember, Name, Symtab, Val};
use crate::zencode;

/// A newtype wrapper for symbolic variables, which are `u32` under
/// the hood.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sym {
    pub(crate) id: u32,
}

impl Sym {
    pub fn from_u32(id: u32) -> Self {
        Sym { id }
    }
}

impl<B> Into<Result<Val<B>, ExecError>> for Sym {
    fn into(self) -> Result<Val<B>, ExecError> {
        Ok(Val::Symbolic(self))
    }
}

impl fmt::Display for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}

/// This module defines a subset of the SMTLIB format we use to
/// interact with the SMT solver, which mostly corresponds to the
/// theory of quantifier-free bitvectors and arrays.
pub mod smtlib {
    use super::Sym;
    use crate::ir::EnumMember;
    use std::collections::HashMap;
    use std::fmt;

    #[derive(Clone, Debug)]
    pub enum Ty {
        Bool,
        BitVec(u32),
        Enum(usize),
        Array(Box<Ty>, Box<Ty>),
    }

    impl fmt::Display for Ty {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            use Ty::*;
            match self {
                Bool => write!(f, "Bool"),
                BitVec(sz) => write!(f, "(_ BitVec {})", sz),
                Enum(e) => write!(f, "Enum{}", e),
                Array(dom, codom) => {
                    write!(f, "(Array ")?;
                    dom.fmt(f)?;
                    write!(f, " ")?;
                    codom.fmt(f)?;
                    write!(f, ")")
                }
            }
        }
    }

    #[derive(Clone, Debug)]
    pub enum Exp {
        Var(Sym),
        Bits(Vec<bool>),
        Bits64(u64, u32),
        Enum(EnumMember),
        Bool(bool),
        Eq(Box<Exp>, Box<Exp>),
        Neq(Box<Exp>, Box<Exp>),
        And(Box<Exp>, Box<Exp>),
        Or(Box<Exp>, Box<Exp>),
        Not(Box<Exp>),
        Bvnot(Box<Exp>),
        Bvand(Box<Exp>, Box<Exp>),
        Bvor(Box<Exp>, Box<Exp>),
        Bvxor(Box<Exp>, Box<Exp>),
        Bvnand(Box<Exp>, Box<Exp>),
        Bvnor(Box<Exp>, Box<Exp>),
        Bvxnor(Box<Exp>, Box<Exp>),
        Bvneg(Box<Exp>),
        Bvadd(Box<Exp>, Box<Exp>),
        Bvsub(Box<Exp>, Box<Exp>),
        Bvmul(Box<Exp>, Box<Exp>),
        Bvudiv(Box<Exp>, Box<Exp>),
        Bvsdiv(Box<Exp>, Box<Exp>),
        Bvurem(Box<Exp>, Box<Exp>),
        Bvsrem(Box<Exp>, Box<Exp>),
        Bvsmod(Box<Exp>, Box<Exp>),
        Bvult(Box<Exp>, Box<Exp>),
        Bvslt(Box<Exp>, Box<Exp>),
        Bvule(Box<Exp>, Box<Exp>),
        Bvsle(Box<Exp>, Box<Exp>),
        Bvuge(Box<Exp>, Box<Exp>),
        Bvsge(Box<Exp>, Box<Exp>),
        Bvugt(Box<Exp>, Box<Exp>),
        Bvsgt(Box<Exp>, Box<Exp>),
        Extract(u32, u32, Box<Exp>),
        ZeroExtend(u32, Box<Exp>),
        SignExtend(u32, Box<Exp>),
        Bvshl(Box<Exp>, Box<Exp>),
        Bvlshr(Box<Exp>, Box<Exp>),
        Bvashr(Box<Exp>, Box<Exp>),
        Concat(Box<Exp>, Box<Exp>),
        Ite(Box<Exp>, Box<Exp>, Box<Exp>),
        App(Sym, Vec<Exp>),
        Select(Box<Exp>, Box<Exp>),
        Store(Box<Exp>, Box<Exp>, Box<Exp>),
    }

    impl Exp {
        /// Recursivly apply the supplied function to each sub-expression in a bottom-up order
        pub fn modify<F>(&mut self, f: &F)
        where
            F: Fn(&mut Exp),
        {
            use Exp::*;
            match self {
                Var(_) | Bits(_) | Bits64(_, _) | Enum { .. } | Bool(_) => (),
                Not(exp) | Bvnot(exp) | Bvneg(exp) | Extract(_, _, exp) | ZeroExtend(_, exp) | SignExtend(_, exp) => {
                    exp.modify(f)
                }
                Eq(lhs, rhs)
                | Neq(lhs, rhs)
                | And(lhs, rhs)
                | Or(lhs, rhs)
                | Bvand(lhs, rhs)
                | Bvor(lhs, rhs)
                | Bvxor(lhs, rhs)
                | Bvnand(lhs, rhs)
                | Bvnor(lhs, rhs)
                | Bvxnor(lhs, rhs)
                | Bvadd(lhs, rhs)
                | Bvsub(lhs, rhs)
                | Bvmul(lhs, rhs)
                | Bvudiv(lhs, rhs)
                | Bvsdiv(lhs, rhs)
                | Bvurem(lhs, rhs)
                | Bvsrem(lhs, rhs)
                | Bvsmod(lhs, rhs)
                | Bvult(lhs, rhs)
                | Bvslt(lhs, rhs)
                | Bvule(lhs, rhs)
                | Bvsle(lhs, rhs)
                | Bvuge(lhs, rhs)
                | Bvsge(lhs, rhs)
                | Bvugt(lhs, rhs)
                | Bvsgt(lhs, rhs)
                | Bvshl(lhs, rhs)
                | Bvlshr(lhs, rhs)
                | Bvashr(lhs, rhs)
                | Concat(lhs, rhs) => {
                    lhs.modify(f);
                    rhs.modify(f);
                }
                Ite(cond, then_exp, else_exp) => {
                    cond.modify(f);
                    then_exp.modify(f);
                    else_exp.modify(f)
                }
                App(_, args) => {
                    for exp in args {
                        exp.modify(f)
                    }
                }
                Select(array, index) => {
                    array.modify(f);
                    index.modify(f);
                }
                Store(array, index, val) => {
                    array.modify(f);
                    index.modify(f);
                    val.modify(f);
                }
            };
            f(self)
        }

        /// Infer the type of an already well-formed SMTLIB expression
        pub fn infer(&self, tcx: &HashMap<Sym, Ty>, ftcx: &HashMap<Sym, (Vec<Ty>, Ty)>) -> Option<Ty> {
            use Exp::*;
            match self {
                Var(v) => tcx.get(v).map(Ty::clone),
                Bits(bv) => Some(Ty::BitVec(bv.len() as u32)),
                Bits64(_, sz) => Some(Ty::BitVec(*sz)),
                Enum(e) => Some(Ty::Enum(e.enum_id)),
                Bool(_)
                | Not(_)
                | Eq(_, _)
                | Neq(_, _)
                | And(_, _)
                | Or(_, _)
                | Bvult(_, _)
                | Bvslt(_, _)
                | Bvule(_, _)
                | Bvsle(_, _)
                | Bvuge(_, _)
                | Bvsge(_, _)
                | Bvugt(_, _)
                | Bvsgt(_, _) => Some(Ty::Bool),
                Bvnot(exp) | Bvneg(exp) => exp.infer(tcx, ftcx),
                Extract(i, j, _) => Some(Ty::BitVec((i - j) + 1)),
                ZeroExtend(ext, exp) | SignExtend(ext, exp) => match exp.infer(tcx, ftcx) {
                    Some(Ty::BitVec(sz)) => Some(Ty::BitVec(sz + ext)),
                    _ => None,
                },
                Bvand(lhs, _)
                | Bvor(lhs, _)
                | Bvxor(lhs, _)
                | Bvnand(lhs, _)
                | Bvnor(lhs, _)
                | Bvxnor(lhs, _)
                | Bvadd(lhs, _)
                | Bvsub(lhs, _)
                | Bvmul(lhs, _)
                | Bvudiv(lhs, _)
                | Bvsdiv(lhs, _)
                | Bvurem(lhs, _)
                | Bvsrem(lhs, _)
                | Bvsmod(lhs, _)
                | Bvshl(lhs, _)
                | Bvlshr(lhs, _)
                | Bvashr(lhs, _) => lhs.infer(tcx, ftcx),
                Concat(lhs, rhs) => match (lhs.infer(tcx, ftcx), rhs.infer(tcx, ftcx)) {
                    (Some(Ty::BitVec(lsz)), Some(Ty::BitVec(rsz))) => Some(Ty::BitVec(lsz + rsz)),
                    (_, _) => None,
                },
                Ite(_, then_exp, _) => then_exp.infer(tcx, ftcx),
                App(f, _) => ftcx.get(f).map(|x| x.1.clone()),
                Select(array, _) => match array.infer(tcx, ftcx) {
                    Some(Ty::Array(_, codom_ty)) => Some(*codom_ty),
                    _ => None,
                },
                Store(array, _, _) => array.infer(tcx, ftcx),
            }
        }
    }

    #[derive(Clone, Debug)]
    pub enum Def {
        DeclareConst(Sym, Ty),
        DeclareFun(Sym, Vec<Ty>, Ty),
        DefineConst(Sym, Exp),
        DefineEnum(Sym, usize),
        Assert(Exp),
    }
}

use smtlib::*;

/// Snapshot of interaction with underlying solver that can be
/// efficiently cloned and shared between threads.
#[derive(Clone, Default)]
pub struct Checkpoint<B> {
    num: usize,
    next_var: u32,
    pub trace: Arc<Option<Trace<B>>>,
}

impl<B> Checkpoint<B> {
    pub fn new() -> Self {
        Checkpoint { num: 0, next_var: 0, trace: Arc::new(None) }
    }

    pub fn trace(&self) -> &Option<Trace<B>> {
        &self.trace
    }
}

/// For the concurrency models, register accesses must be logged at a
/// subfield level granularity (e.g. for PSTATE in ARM ASL), which is
/// what the Accessor type is for.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum Accessor {
    Field(Name),
}

impl Accessor {
    pub fn to_string(&self, symtab: &Symtab) -> String {
        match self {
            Accessor::Field(name) => format!("(_ field |{}|)", zencode::decode(symtab.to_str(*name))),
        }
    }

    pub fn pretty(&self, buf: &mut dyn Write, symtab: &Symtab) -> Result<(), Box<dyn Error>> {
        match self {
            Accessor::Field(name) => write!(buf, ".{}", zencode::decode(symtab.to_str(*name)))?,
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum Event<B> {
    Smt(Def),
    Fork(u32, Sym, String),
    ReadReg(Name, Vec<Accessor>, Val<B>),
    WriteReg(Name, Vec<Accessor>, Val<B>),
    ReadMem { value: Val<B>, read_kind: Val<B>, address: Val<B>, bytes: u32, tag_value: Option<Val<B>>, kind: &'static str },
    WriteMem { value: Sym, write_kind: Val<B>, address: Val<B>, data: Val<B>, bytes: u32, tag_value: Option<Val<B>>, kind: &'static str },
    Branch { address: Val<B> },
    Barrier { barrier_kind: Val<B> },
    CacheOp { cache_op_kind: Val<B>, address: Val<B> },
    MarkReg { regs: Vec<Name>, mark: String },
    Cycle,
    Instr(Val<B>),
    Sleeping(Sym),
    SleepRequest,
    WakeupRequest,
}

impl<B: BV> Event<B> {
    pub fn is_smt(&self) -> bool {
        matches!(self, Event::Smt(_))
    }

    pub fn is_reg(&self) -> bool {
        matches!(self, Event::ReadReg(_, _, _) | Event::WriteReg(_, _, _) | Event::MarkReg { .. })
    }

    pub fn is_write_reg(&self) -> bool {
        matches!(self, Event::WriteReg(_, _, _))
    }

    pub fn is_cycle(&self) -> bool {
        matches!(self, Event::Cycle)
    }

    pub fn is_instr(&self) -> bool {
        matches!(self, Event::Instr(_))
    }

    pub fn is_branch(&self) -> bool {
        matches!(self, Event::Branch { .. })
    }

    pub fn is_barrier(&self) -> bool {
        matches!(self, Event::Barrier { .. })
    }

    pub fn is_fork(&self) -> bool {
        matches!(self, Event::Fork(_, _, _))
    }

    pub fn is_memory(&self) -> bool {
        matches!(self, Event::ReadMem { .. } | Event::WriteMem { .. } | Event::Barrier { .. } | Event::CacheOp { .. })
    }

    pub fn is_memory_read(&self) -> bool {
        matches!(self, Event::ReadMem { .. })
    }

    pub fn is_memory_write(&self) -> bool {
        matches!(self, Event::WriteMem { .. })
    }

    pub fn is_cache_op(&self) -> bool {
        matches!(self, Event::CacheOp { .. })
    }

    pub fn has_barrier_kind(&self, bk: usize) -> bool {
        match self {
            Event::Barrier { barrier_kind: Val::Enum(e) } => e.member == bk,
            _ => false,
        }
    }

    pub fn has_read_kind(&self, rk: usize) -> bool {
        match self {
            Event::ReadMem { read_kind: Val::Enum(e), .. } => e.member == rk,
            _ => false,
        }
    }

    pub fn has_write_kind(&self, wk: usize) -> bool {
        match self {
            Event::WriteMem { write_kind: Val::Enum(e), .. } => e.member == wk,
            _ => false,
        }
    }

    pub fn has_cache_op_kind(&self, ck: usize) -> bool {
        match self {
            Event::CacheOp { cache_op_kind: Val::Enum(e), .. } => e.member == ck,
            _ => false,
        }
    }
}

pub type EvPath<B> = Vec<Event<B>>;

/// Abstractly represents a sequence of events in such a way that
/// checkpoints can be created and shared.
#[derive(Debug)]
pub struct Trace<B> {
    checkpoints: usize,
    pub head: Vec<Event<B>>,
    pub tail: Arc<Option<Trace<B>>>,
}

impl<B: BV> Trace<B> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Trace { checkpoints: 0, head: Vec::new(), tail: Arc::new(None) }
    }

    pub fn checkpoint(&mut self, next_var: u32) -> Checkpoint<B> {
        let mut head = Vec::new();
        mem::swap(&mut self.head, &mut head);
        let tail = Arc::new(Some(Trace { checkpoints: self.checkpoints, head, tail: self.tail.clone() }));
        self.checkpoints += 1;
        self.tail = tail.clone();
        Checkpoint { num: self.checkpoints, trace: tail, next_var }
    }

    pub fn to_vec<'a>(&'a self) -> Vec<&'a Event<B>> {
        let mut vec: Vec<&'a Event<B>> = Vec::new();

        let mut current_head = &self.head;
        let mut current_tail = self.tail.as_ref();
        loop {
            for def in current_head.iter().rev() {
                vec.push(def)
            }
            match current_tail {
                Some(trace) => {
                    current_head = &trace.head;
                    current_tail = trace.tail.as_ref();
                }
                None => return vec,
            }
        }
    }
}

/// Config is a wrapper around the `Z3_config` type from the C
/// API. `Z3_del_config` is called when it is dropped.
pub struct Config {
    z3_cfg: Z3_config,
}

impl Config {
    pub fn new() -> Self {
        unsafe { Config { z3_cfg: Z3_mk_config() } }
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

impl Config {
    pub fn set_param_value(&mut self, id: &str, value: &str) {
        let id = CString::new(id).unwrap();
        let value = CString::new(value).unwrap();
        unsafe { Z3_set_param_value(self.z3_cfg, id.as_ptr(), value.as_ptr()) }
    }
}

pub fn global_set_param_value(id: &str, value: &str) {
    let id = CString::new(id).unwrap();
    let value = CString::new(value).unwrap();
    unsafe { Z3_global_param_set(id.as_ptr(), value.as_ptr()) }
}

/// Context is a wrapper around `Z3_context`.
pub struct Context {
    z3_ctx: Z3_context,
}

impl Context {
    pub fn new(cfg: Config) -> Self {
        unsafe { Context { z3_ctx: Z3_mk_context_rc(cfg.z3_cfg) } }
    }

    fn error(&self) -> ExecError {
        unsafe {
            let code = Z3_get_error_code(self.z3_ctx);
            let msg = Z3_get_error_msg(self.z3_ctx, code);
            let str: String = CStr::from_ptr(msg).to_string_lossy().to_string();
            ExecError::Z3Error(str)
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.z3_ctx) }
    }
}

struct Enum {
    sort: Z3_sort,
    size: usize,
    consts: Vec<Z3_func_decl>,
    testers: Vec<Z3_func_decl>,
}

struct Enums<'ctx> {
    enums: Vec<Enum>,
    ctx: &'ctx Context,
}

impl<'ctx> Enums<'ctx> {
    fn new(ctx: &'ctx Context) -> Self {
        Enums { enums: Vec::new(), ctx }
    }

    fn add_enum(&mut self, name: Sym, members: &[Sym]) {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            let size = members.len();

            let name = Z3_mk_int_symbol(ctx, name.id as c_int);
            let members: Vec<Z3_symbol> = members.iter().map(|m| Z3_mk_int_symbol(ctx, m.id as c_int)).collect();

            let mut consts = mem::ManuallyDrop::new(Vec::with_capacity(size));
            let mut testers = mem::ManuallyDrop::new(Vec::with_capacity(size));

            let sort = Z3_mk_enumeration_sort(
                ctx,
                name,
                size as c_uint,
                members.as_ptr(),
                consts.as_mut_ptr(),
                testers.as_mut_ptr(),
            );

            let consts = Vec::from_raw_parts(consts.as_mut_ptr(), size, size);
            let testers = Vec::from_raw_parts(testers.as_mut_ptr(), size, size);

            for i in 0..size {
                Z3_inc_ref(ctx, Z3_func_decl_to_ast(ctx, consts[i]));
                Z3_inc_ref(ctx, Z3_func_decl_to_ast(ctx, testers[i]))
            }
            Z3_inc_ref(ctx, Z3_sort_to_ast(ctx, sort));

            self.enums.push(Enum { sort, size, consts, testers })
        }
    }
}

impl<'ctx> Drop for Enums<'ctx> {
    fn drop(&mut self) {
        unsafe {
            let ctx = self.ctx.z3_ctx;
            for e in self.enums.drain(..) {
                for i in 0..e.size {
                    Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, e.consts[i]));
                    Z3_dec_ref(ctx, Z3_func_decl_to_ast(ctx, e.testers[i]))
                }
                Z3_dec_ref(ctx, Z3_sort_to_ast(ctx, e.sort))
            }
        }
    }
}

struct Sort<'ctx> {
    z3_sort: Z3_sort,
    ctx: &'ctx Context,
}

impl<'ctx> Sort<'ctx> {
    fn bitvec(ctx: &'ctx Context, sz: u32) -> Self {
        unsafe {
            let z3_sort = Z3_mk_bv_sort(ctx.z3_ctx, sz);
            Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
            Sort { z3_sort, ctx }
        }
    }

    fn new(ctx: &'ctx Context, enums: &Enums<'ctx>, ty: &Ty) -> Self {
        unsafe {
            match ty {
                Ty::Bool => {
                    let z3_sort = Z3_mk_bool_sort(ctx.z3_ctx);
                    Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
                    Sort { z3_sort, ctx }
                }
                Ty::BitVec(sz) => Self::bitvec(ctx, *sz),
                Ty::Enum(e) => {
                    let z3_sort = enums.enums[*e].sort;
                    Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort));
                    Sort { z3_sort, ctx }
                }
                Ty::Array(dom, codom) => {
                    let dom_s = Self::new(ctx, enums, dom);
                    let codom_s = Self::new(ctx, enums, codom);
                    let z3_sort = Z3_mk_array_sort(ctx.z3_ctx, dom_s.z3_sort, codom_s.z3_sort);
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
    fn new(ctx: &'ctx Context, v: Sym, enums: &Enums<'ctx>, arg_tys: &[Ty], ty: &Ty) -> Self {
        unsafe {
            let name = Z3_mk_int_symbol(ctx.z3_ctx, v.id as c_int);
            let arg_sorts: Vec<Sort> = arg_tys.iter().map(|ty| Sort::new(ctx, enums, ty)).collect();
            let arg_z3_sorts: Vec<Z3_sort> = arg_sorts.iter().map(|s| s.z3_sort).collect();
            let args: u32 = arg_sorts.len() as u32;
            let z3_func_decl =
                Z3_mk_func_decl(ctx.z3_ctx, name, args, arg_z3_sorts.as_ptr(), Sort::new(ctx, enums, ty).z3_sort);
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

impl<'ctx> Clone for Ast<'ctx> {
    fn clone(&self) -> Self {
        unsafe {
            let z3_ast = self.z3_ast;
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }
}

macro_rules! z3_unary_op {
    ($i:ident, $arg:ident) => {
        unsafe {
            let z3_ast = $i($arg.ctx.z3_ctx, $arg.z3_ast);
            Z3_inc_ref($arg.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: $arg.ctx }
        }
    };
}

macro_rules! z3_binary_op {
    ($i:ident, $lhs:ident, $rhs:ident) => {
        unsafe {
            let z3_ast = $i($lhs.ctx.z3_ctx, $lhs.z3_ast, $rhs.z3_ast);
            Z3_inc_ref($lhs.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: $lhs.ctx }
        }
    };
}

impl<'ctx> Ast<'ctx> {
    fn mk_constant(fd: &FuncDecl<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_app(fd.ctx.z3_ctx, fd.z3_func_decl, 0, ptr::null());
            Z3_inc_ref(fd.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: fd.ctx }
        }
    }

    fn mk_app(fd: &FuncDecl<'ctx>, args: &[Ast<'ctx>]) -> Self {
        unsafe {
            let z3_args: Vec<Z3_ast> = args.iter().map(|ast| ast.z3_ast).collect();
            let len = z3_args.len() as u32;
            let z3_ast = Z3_mk_app(fd.ctx.z3_ctx, fd.z3_func_decl, len, z3_args.as_ptr());
            Z3_inc_ref(fd.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: fd.ctx }
        }
    }

    fn mk_enum_member(enums: &Enums<'ctx>, enum_id: usize, member: usize) -> Self {
        unsafe {
            let func_decl = enums.enums[enum_id].consts[member];
            let z3_ast = Z3_mk_app(enums.ctx.z3_ctx, func_decl, 0, ptr::null());
            Z3_inc_ref(enums.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: enums.ctx }
        }
    }

    fn mk_bv_u64(ctx: &'ctx Context, sz: u32, bits: u64) -> Self {
        unsafe {
            let sort = Sort::bitvec(ctx, sz);
            let z3_ast = Z3_mk_unsigned_int64(ctx.z3_ctx, bits, sort.z3_sort);
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn mk_bv(ctx: &'ctx Context, sz: u32, bits: &[bool]) -> Self {
        unsafe {
            let z3_ast = Z3_mk_bv_numeral(ctx.z3_ctx, sz, bits.as_ptr());
            Z3_inc_ref(ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx }
        }
    }

    fn mk_bool(ctx: &'ctx Context, b: bool) -> Self {
        unsafe {
            let z3_ast = if b { Z3_mk_true(ctx.z3_ctx) } else { Z3_mk_false(ctx.z3_ctx) };
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

    fn mk_and(&self, rhs: &Ast<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_and(self.ctx.z3_ctx, 2, &[self.z3_ast, rhs.z3_ast] as *const Z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_or(&self, rhs: &Ast<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_or(self.ctx.z3_ctx, 2, &[self.z3_ast, rhs.z3_ast] as *const Z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn extract(&self, hi: u32, lo: u32) -> Self {
        unsafe {
            let z3_ast = Z3_mk_extract(self.ctx.z3_ctx, hi, lo, self.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn zero_extend(&self, i: u32) -> Self {
        unsafe {
            let z3_ast = Z3_mk_zero_ext(self.ctx.z3_ctx, i, self.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn sign_extend(&self, i: u32) -> Self {
        unsafe {
            let z3_ast = Z3_mk_sign_ext(self.ctx.z3_ctx, i, self.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn ite(&self, true_exp: &Ast<'ctx>, false_exp: &Ast<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_ite(self.ctx.z3_ctx, self.z3_ast, true_exp.z3_ast, false_exp.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn mk_bvnot(&self) -> Self {
        z3_unary_op!(Z3_mk_bvnot, self)
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

    fn mk_bvneg(&self) -> Self {
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

    fn mk_bvshl(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvshl, self, rhs)
    }

    fn mk_bvlshr(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvlshr, self, rhs)
    }

    fn mk_bvashr(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_bvashr, self, rhs)
    }

    fn mk_concat(&self, rhs: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_concat, self, rhs)
    }

    fn mk_select(&self, index: &Ast<'ctx>) -> Self {
        z3_binary_op!(Z3_mk_select, self, index)
    }

    fn mk_store(&self, index: &Ast<'ctx>, val: &Ast<'ctx>) -> Self {
        unsafe {
            let z3_ast = Z3_mk_store(self.ctx.z3_ctx, self.z3_ast, index.z3_ast, val.z3_ast);
            Z3_inc_ref(self.ctx.z3_ctx, z3_ast);
            Ast { z3_ast, ctx: self.ctx }
        }
    }

    fn get_bool_value(&self) -> Option<bool> {
        unsafe {
            match Z3_get_bool_value(self.ctx.z3_ctx, self.z3_ast) {
                Z3_L_TRUE => Some(true),
                Z3_L_FALSE => Some(false),
                _ => None,
            }
        }
    }

    fn get_numeral_u64(&self) -> Result<u64, ExecError> {
        let mut v: u64 = 0;
        unsafe {
            if Z3_get_numeral_uint64(self.ctx.z3_ctx, self.z3_ast, &mut v) {
                Ok(v)
            } else {
                Err(self.ctx.error())
            }
        }
    }
}

impl<'ctx> Drop for Ast<'ctx> {
    fn drop(&mut self) {
        unsafe { Z3_dec_ref(self.ctx.z3_ctx, self.z3_ast) }
    }
}

/// The Solver type handles all interaction with Z3. It mimics
/// interacting with Z3 via the subset of the SMTLIB 2.0 format we
/// care about.
///
/// For example:
/// ```
/// # use isla_lib::concrete::bitvector64::B64;
/// # use isla_lib::smt::smtlib::Exp::*;
/// # use isla_lib::smt::smtlib::Def::*;
/// # use isla_lib::smt::smtlib::*;
/// # use isla_lib::smt::*;
/// # let x = Sym::from_u32(0);
/// let cfg = Config::new();
/// let ctx = Context::new(cfg);
/// let mut solver = Solver::<B64>::new(&ctx);
/// // (declare-const v0 Bool)
/// solver.add(DeclareConst(x, Ty::Bool));
/// // (assert v0)
/// solver.add(Assert(Var(x)));
/// // (check-sat)
/// assert!(solver.check_sat() == SmtResult::Sat)
/// ```
///
/// The other thing the Solver type does is maintain a trace of
/// interactions with Z3, which can be checkpointed and replayed by
/// another solver. This `Checkpoint` type is safe to be sent between
/// threads.
///
/// For example:
/// ```
/// # use isla_lib::concrete::bitvector64::B64;
/// # use isla_lib::smt::smtlib::Exp::*;
/// # use isla_lib::smt::smtlib::Def::*;
/// # use isla_lib::smt::smtlib::*;
/// # use isla_lib::smt::*;
/// # let x = Sym::from_u32(0);
/// let point = {
///     let cfg = Config::new();
///     let ctx = Context::new(cfg);
///     let mut solver = Solver::<B64>::new(&ctx);
///     solver.add(DeclareConst(x, Ty::Bool));
///     solver.add(Assert(Var(x)));
///     solver.add(Assert(Not(Box::new(Var(x)))));
///     checkpoint(&mut solver)
/// };
/// let cfg = Config::new();
/// let ctx = Context::new(cfg);
/// let mut solver = Solver::from_checkpoint(&ctx, point);
/// assert!(solver.check_sat() == SmtResult::Unsat);
pub struct Solver<'ctx, B> {
    trace: Trace<B>,
    next_var: u32,
    cycles: i128,
    decls: HashMap<Sym, Ast<'ctx>>,
    func_decls: HashMap<Sym, FuncDecl<'ctx>>,
    enums: Enums<'ctx>,
    enum_map: HashMap<usize, usize>,
    z3_solver: Z3_solver,
    ctx: &'ctx Context,
}

impl<'ctx, B> Drop for Solver<'ctx, B> {
    fn drop(&mut self) {
        unsafe {
            Z3_solver_dec_ref(self.ctx.z3_ctx, self.z3_solver);
        }
    }
}

/// Interface for extracting information from Z3 models.
///
/// Model generation should be turned on in advance.  This is
/// currently Z3's default, but it's best to make sure:
///
/// ```
/// # use isla_lib::concrete::bitvector64::B64;
/// # use isla_lib::smt::smtlib::Exp::*;
/// # use isla_lib::smt::smtlib::Def::*;
/// # use isla_lib::smt::smtlib::*;
/// # use isla_lib::smt::*;
/// # let x = Sym::from_u32(0);
/// let mut cfg = Config::new();
/// cfg.set_param_value("model", "true");
/// let ctx = Context::new(cfg);
/// let mut solver = Solver::<B64>::new(&ctx);
/// solver.add(DeclareConst(x, Ty::BitVec(4)));
/// solver.add(Assert(Bvsgt(Box::new(Var(x)), Box::new(Bits(vec![false,false,true,false])))));
/// assert!(solver.check_sat() == SmtResult::Sat);
/// let mut model = Model::new(&solver);
/// let var0 = model.get_var(x).unwrap().unwrap();
/// ```
pub struct Model<'ctx, B> {
    z3_model: Z3_model,
    solver: &'ctx Solver<'ctx, B>,
    ctx: &'ctx Context,
}

impl<'ctx, B> Drop for Model<'ctx, B> {
    fn drop(&mut self) {
        unsafe {
            Z3_model_dec_ref(self.ctx.z3_ctx, self.z3_model);
        }
    }
}

// This implements Debug rather than Display because it displays the internal
// variable names (albeit with the same numbers that appear in the trace).
impl<'ctx, B> fmt::Debug for Model<'ctx, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe {
            let z3_string = CStr::from_ptr(Z3_model_to_string(self.ctx.z3_ctx, self.z3_model));
            write!(f, "{}", z3_string.to_string_lossy())
        }
    }
}

impl<'ctx, B: BV> Model<'ctx, B> {
    pub fn new(solver: &'ctx Solver<'ctx, B>) -> Self {
        unsafe {
            let z3_model = Z3_solver_get_model(solver.ctx.z3_ctx, solver.z3_solver);
            Z3_model_inc_ref(solver.ctx.z3_ctx, z3_model);
            Model { z3_model, solver, ctx: solver.ctx }
        }
    }

    #[allow(clippy::needless_range_loop)]
    fn get_large_bv(&mut self, ast: Ast, size: u32) -> Result<Vec<bool>, ExecError> {
        let mut i = 0;
        let size = size.try_into().unwrap();
        let mut result = vec![false; size];
        while i < size {
            let hi = std::cmp::min(size, i + 64);
            let hi32: u32 = hi.try_into().unwrap();
            let extract_ast = ast.extract(hi32 - 1, i.try_into().unwrap());
            let result_ast: Ast;

            unsafe {
                let mut result_z3_ast: Z3_ast = ptr::null_mut();
                if !Z3_model_eval(self.ctx.z3_ctx, self.z3_model, extract_ast.z3_ast, true, &mut result_z3_ast) {
                    return Err(self.ctx.error());
                }
                Z3_inc_ref(self.ctx.z3_ctx, result_z3_ast);
                result_ast = Ast { z3_ast: result_z3_ast, ctx: self.ctx };
            }
            let v = result_ast.get_numeral_u64()?;
            for j in i..hi {
                result[j] = (v >> (j - i) & 1) == 1;
            }
            i += 64;
        }
        Ok(result)
    }

    pub fn get_var(&mut self, var: Sym) -> Result<Option<Exp>, ExecError> {
        let var_ast = match self.solver.decls.get(&var) {
            None => return Err(ExecError::Type(format!("Unbound variable {:?}", &var))),
            Some(ast) => ast.clone(),
        };
        self.get_ast(var_ast)
    }

    pub fn get_exp(&mut self, exp: &Exp) -> Result<Option<Exp>, ExecError> {
        let ast = self.solver.translate_exp(exp);
        self.get_ast(ast)
    }

    // Requiring the model to be mutable as I expect Z3 will alter the underlying data
    fn get_ast(&mut self, var_ast: Ast) -> Result<Option<Exp>, ExecError> {
        unsafe {
            let z3_ctx = self.ctx.z3_ctx;
            let mut z3_ast: Z3_ast = ptr::null_mut();
            if !Z3_model_eval(z3_ctx, self.z3_model, var_ast.z3_ast, false, &mut z3_ast) {
                return Err(self.ctx.error());
            }
            Z3_inc_ref(z3_ctx, z3_ast);

            let ast = Ast { z3_ast, ctx: self.ctx };

            let sort = Z3_get_sort(z3_ctx, ast.z3_ast);
            Z3_inc_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, sort));
            let sort_kind = Z3_get_sort_kind(z3_ctx, sort);

            let result = if sort_kind == SortKind::BV && Z3_is_numeral_ast(z3_ctx, z3_ast) {
                let size = Z3_get_bv_sort_size(z3_ctx, sort);
                if size > 64 {
                    let v = self.get_large_bv(ast, size)?;
                    Ok(Some(Exp::Bits(v)))
                } else {
                    let result = ast.get_numeral_u64()?;
                    Ok(Some(Exp::Bits64(result, size)))
                }
            } else if sort_kind == SortKind::Bool && Z3_is_numeral_ast(z3_ctx, z3_ast) {
                Ok(Some(Exp::Bool(ast.get_bool_value().unwrap())))
            } else if sort_kind == SortKind::Bool || sort_kind == SortKind::BV {
                // Model did not need to assign an interpretation to this variable
                Ok(None)
            } else if sort_kind == SortKind::Datatype {
                let func_decl = Z3_get_app_decl(z3_ctx, Z3_to_app(z3_ctx, z3_ast));
                Z3_inc_ref(z3_ctx, Z3_func_decl_to_ast(z3_ctx, func_decl));

                let mut result = Ok(None);

                // Scan all enumerations to find the enum_id (which is
                // the index in the enums vector) and member number.
                'outer: for (enum_id, enumeration) in self.solver.enums.enums.iter().enumerate() {
                    for (i, member) in enumeration.consts.iter().enumerate() {
                        if Z3_is_eq_func_decl(z3_ctx, func_decl, *member) {
                            result = Ok(Some(Exp::Enum(EnumMember { enum_id, member: i })));
                            break 'outer;
                        }
                    }
                }

                Z3_dec_ref(z3_ctx, Z3_func_decl_to_ast(z3_ctx, func_decl));
                result
            } else {
                Err(ExecError::Type("get_ast".to_string()))
            };

            Z3_dec_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, sort));
            result
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SmtResult {
    Sat,
    Unsat,
    Unknown,
}

use SmtResult::*;

impl SmtResult {
    pub fn is_sat(self) -> Result<bool, ExecError> {
        match self {
            Sat => Ok(true),
            Unsat => Ok(false),
            Unknown => Err(ExecError::Z3Unknown),
        }
    }

    pub fn is_unsat(self) -> Result<bool, ExecError> {
        match self {
            Sat => Ok(false),
            Unsat => Ok(true),
            Unknown => Err(ExecError::Z3Unknown),
        }
    }

    pub fn is_unknown(self) -> bool {
        self == Unknown
    }
}

static QFAUFBV_STR: &[u8] = b"qfaufbv\0";

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub fn new(ctx: &'ctx Context) -> Self {
        unsafe {
            let mut major: c_uint = 0;
            let mut minor: c_uint = 0;
            let mut build: c_uint = 0;
            let mut revision: c_uint = 0;
            Z3_get_version(&mut major, &mut minor, &mut build, &mut revision);

            // The QF_AUFBV solver has good performance on our problems, but we need to initialise it
            // using a tactic rather than the logic name to ensure that the enumerations are supported,
            // otherwise Z3 may crash.
            let qfaufbv_tactic = Z3_mk_tactic(ctx.z3_ctx, CStr::from_bytes_with_nul_unchecked(QFAUFBV_STR).as_ptr());
            Z3_tactic_inc_ref(ctx.z3_ctx, qfaufbv_tactic);
            let z3_solver = Z3_mk_solver_from_tactic(ctx.z3_ctx, qfaufbv_tactic);
            Z3_solver_inc_ref(ctx.z3_ctx, z3_solver);

            Solver {
                ctx,
                z3_solver,
                next_var: 0,
                cycles: 0,
                trace: Trace::new(),
                decls: HashMap::new(),
                func_decls: HashMap::new(),
                enums: Enums::new(ctx),
                enum_map: HashMap::new(),
            }
        }
    }

    pub fn fresh(&mut self) -> Sym {
        let n = self.next_var;
        self.next_var += 1;
        Sym { id: n }
    }

    fn translate_exp(&self, exp: &Exp) -> Ast<'ctx> {
        use Exp::*;
        match exp {
            Var(v) => match self.decls.get(v) {
                None => panic!("Could not get Z3 func_decl {}", *v),
                Some(ast) => ast.clone(),
            },
            Bits(bv) => Ast::mk_bv(self.ctx, bv.len().try_into().unwrap(), &bv),
            Bits64(bv, len) => Ast::mk_bv_u64(self.ctx, *len, *bv),
            Enum(e) => Ast::mk_enum_member(&self.enums, e.enum_id, e.member),
            Bool(b) => Ast::mk_bool(self.ctx, *b),
            Not(exp) => Ast::mk_not(&self.translate_exp(exp)),
            Eq(lhs, rhs) => Ast::mk_eq(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Neq(lhs, rhs) => Ast::mk_not(&Ast::mk_eq(&self.translate_exp(lhs), &self.translate_exp(rhs))),
            And(lhs, rhs) => Ast::mk_and(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Or(lhs, rhs) => Ast::mk_or(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvnot(exp) => Ast::mk_bvnot(&self.translate_exp(exp)),
            Bvand(lhs, rhs) => Ast::mk_bvand(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvor(lhs, rhs) => Ast::mk_bvor(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvxor(lhs, rhs) => Ast::mk_bvxor(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvnand(lhs, rhs) => Ast::mk_bvnand(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvnor(lhs, rhs) => Ast::mk_bvnor(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvxnor(lhs, rhs) => Ast::mk_bvxnor(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvneg(exp) => Ast::mk_bvneg(&self.translate_exp(exp)),
            Bvadd(lhs, rhs) => Ast::mk_bvadd(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsub(lhs, rhs) => Ast::mk_bvsub(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvmul(lhs, rhs) => Ast::mk_bvmul(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvudiv(lhs, rhs) => Ast::mk_bvudiv(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsdiv(lhs, rhs) => Ast::mk_bvsdiv(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvurem(lhs, rhs) => Ast::mk_bvurem(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsrem(lhs, rhs) => Ast::mk_bvsrem(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsmod(lhs, rhs) => Ast::mk_bvsmod(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvult(lhs, rhs) => Ast::mk_bvult(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvslt(lhs, rhs) => Ast::mk_bvslt(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvule(lhs, rhs) => Ast::mk_bvule(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsle(lhs, rhs) => Ast::mk_bvsle(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvuge(lhs, rhs) => Ast::mk_bvuge(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsge(lhs, rhs) => Ast::mk_bvsge(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvugt(lhs, rhs) => Ast::mk_bvugt(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvsgt(lhs, rhs) => Ast::mk_bvsgt(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Extract(hi, lo, bv) => self.translate_exp(bv).extract(*hi, *lo),
            ZeroExtend(i, bv) => self.translate_exp(bv).zero_extend(*i),
            SignExtend(i, bv) => self.translate_exp(bv).sign_extend(*i),
            Bvshl(lhs, rhs) => Ast::mk_bvshl(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvlshr(lhs, rhs) => Ast::mk_bvlshr(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Bvashr(lhs, rhs) => Ast::mk_bvashr(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Concat(lhs, rhs) => Ast::mk_concat(&self.translate_exp(lhs), &self.translate_exp(rhs)),
            Ite(cond, t, f) => self.translate_exp(cond).ite(&self.translate_exp(t), &self.translate_exp(f)),
            App(f, args) => {
                let args_ast: Vec<_> = args.iter().map(|arg| self.translate_exp(arg)).collect();
                match self.func_decls.get(f) {
                    None => panic!("Could not get Z3 func_decl {}", *f),
                    Some(fd) => Ast::mk_app(&fd, &args_ast),
                }
            }
            Select(array, index) => Ast::mk_select(&self.translate_exp(array), &self.translate_exp(index)),
            Store(array, index, val) => {
                Ast::mk_store(&self.translate_exp(array), &self.translate_exp(index), &self.translate_exp(val))
            }
        }
    }

    fn assert(&mut self, exp: &Exp) {
        let ast = self.translate_exp(exp);
        unsafe {
            Z3_solver_assert(self.ctx.z3_ctx, self.z3_solver, ast.z3_ast);
        }
    }

    pub fn get_enum(&mut self, size: usize) -> usize {
        match self.enum_map.get(&size) {
            Some(enum_id) => *enum_id,
            None => {
                let name = self.fresh();
                self.add(Def::DefineEnum(name, size));
                self.enums.enums.len() - 1
            }
        }
    }

    fn add_internal(&mut self, def: &Def) {
        match &def {
            Def::Assert(exp) => self.assert(exp),
            Def::DeclareConst(v, ty) => {
                let fd = FuncDecl::new(&self.ctx, *v, &self.enums, &[], ty);
                self.decls.insert(*v, Ast::mk_constant(&fd));
            }
            Def::DeclareFun(v, arg_tys, result_ty) => {
                let fd = FuncDecl::new(&self.ctx, *v, &self.enums, arg_tys, result_ty);
                self.func_decls.insert(*v, fd);
            }
            Def::DefineConst(v, exp) => {
                let ast = self.translate_exp(exp);
                self.decls.insert(*v, ast);
            }
            Def::DefineEnum(name, size) => {
                let members: Vec<Sym> = (0..*size).map(|_| self.fresh()).collect();
                self.enums.add_enum(*name, &members);
                self.enum_map.insert(*size, self.enums.enums.len() - 1);
            }
        }
    }

    pub fn length(&mut self, v: Sym) -> Option<u32> {
        match self.decls.get(&v) {
            Some(ast) => unsafe {
                let z3_ctx = self.ctx.z3_ctx;
                let z3_sort = Z3_get_sort(z3_ctx, ast.z3_ast);
                Z3_inc_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                if Z3_get_sort_kind(z3_ctx, z3_sort) == SortKind::BV {
                    let sz = Z3_get_bv_sort_size(z3_ctx, z3_sort);
                    Z3_dec_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                    Some(sz)
                } else {
                    Z3_dec_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                    None
                }
            },
            None => None,
        }
    }

    pub fn is_bitvector(&mut self, v: Sym) -> bool {
        match self.decls.get(&v) {
            Some(ast) => unsafe {
                let z3_ctx = self.ctx.z3_ctx;
                let z3_sort = Z3_get_sort(z3_ctx, ast.z3_ast);
                Z3_inc_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                let result = Z3_get_sort_kind(z3_ctx, z3_sort) == SortKind::BV;
                Z3_dec_ref(z3_ctx, Z3_sort_to_ast(z3_ctx, z3_sort));
                result
            },
            None => false,
        }
    }

    pub fn add(&mut self, def: Def) {
        self.add_internal(&def);
        self.trace.head.push(Event::Smt(def))
    }

    pub fn declare_const(&mut self, ty: Ty) -> Sym {
        let sym = self.fresh();
        self.add(Def::DeclareConst(sym, ty));
        sym
    }

    pub fn define_const(&mut self, exp: Exp) -> Sym {
        let sym = self.fresh();
        self.add(Def::DefineConst(sym, exp));
        sym
    }

    pub fn assert_eq(&mut self, lhs: Exp, rhs: Exp) {
        self.add(Def::Assert(Exp::Eq(Box::new(lhs), Box::new(rhs))))
    }

    pub fn cycle_count(&mut self) {
        self.cycles += 1;
        self.add_event(Event::Cycle)
    }

    pub fn get_cycle_count(&self) -> i128 {
        self.cycles
    }

    fn add_event_internal(&mut self, event: &Event<B>) {
        if let Event::Smt(def) = event {
            self.add_internal(def)
        };
    }

    pub fn add_event(&mut self, event: Event<B>) {
        self.add_event_internal(&event);
        self.trace.head.push(event)
    }

    fn replay(&mut self, num: usize, trace: Arc<Option<Trace<B>>>) {
        // Some extra work would be required to replay on top of
        // another trace, so until we need to do that we'll check it's
        // empty:
        assert!(self.trace.checkpoints == 0 && self.trace.head.is_empty());
        let mut checkpoints: Vec<&[Event<B>]> = Vec::with_capacity(num);
        let mut next = &*trace;
        loop {
            match next {
                None => break,
                Some(tr) => {
                    checkpoints.push(&tr.head);
                    next = &*tr.tail
                }
            }
        }
        assert!(checkpoints.len() == num);
        for events in checkpoints.iter().rev() {
            for event in *events {
                self.add_event_internal(&event)
            }
        }
        self.trace.checkpoints = num;
        self.trace.tail = trace
    }

    pub fn from_checkpoint(ctx: &'ctx Context, Checkpoint { num, next_var, trace }: Checkpoint<B>) -> Self {
        let mut solver = Solver::new(ctx);
        solver.replay(num, trace);
        solver.next_var = next_var;
        solver
    }

    pub fn check_sat_with(&mut self, exp: &Exp) -> SmtResult {
        let ast = self.translate_exp(exp);
        unsafe {
            let result = Z3_solver_check_assumptions(self.ctx.z3_ctx, self.z3_solver, 1, &ast.z3_ast);
            if result == Z3_L_TRUE {
                Sat
            } else if result == Z3_L_FALSE {
                Unsat
            } else {
                Unknown
            }
        }
    }

    pub fn trace(&self) -> &Trace<B> {
        &self.trace
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

    pub fn dump_solver(&mut self, filename: &str) {
        let mut file = std::fs::File::create(filename).expect("Failed to open solver dump file");
        unsafe {
            let s = Z3_solver_to_string(self.ctx.z3_ctx, self.z3_solver);
            let cs = CStr::from_ptr(s);
            file.write_all(cs.to_bytes()).expect("Failed to write solver dump");
        }
    }

    pub fn dump_solver_with(&mut self, filename: &str, exp: &Exp) {
        let mut file = std::fs::File::create(filename).expect("Failed to open solver dump file");
        unsafe {
            let s = Z3_solver_to_string(self.ctx.z3_ctx, self.z3_solver);
            let cs = CStr::from_ptr(s);
            file.write_all(cs.to_bytes()).expect("Failed to write solver dump");
            writeln!(file, "{}", self.exp_to_str(exp)).expect("Failed to write exp");
        }
    }

    pub fn exp_to_str(&mut self, exp: &Exp) -> String {
        let ast = self.translate_exp(exp);
        let cs;
        unsafe {
            let s = Z3_ast_to_string(ast.ctx.z3_ctx, ast.z3_ast);
            cs = CStr::from_ptr(s);
        }
        cs.to_string_lossy().to_string()
    }
}

pub fn checkpoint<B: BV>(solver: &mut Solver<B>) -> Checkpoint<B> {
    solver.trace.checkpoint(solver.next_var)
}

/// This function just calls Z3_finalize_memory(). It's useful because
/// by calling it before we exit, we can check whether we are leaking
/// memory while interacting with Z3 objects.
///
/// # Safety
///
/// Shoud only be called just before exiting.
pub unsafe fn finalize_solver() {
    Z3_finalize_memory()
}

#[cfg(test)]
mod tests {
    use crate::concrete::bitvector64::B64;

    use super::Def::*;
    use super::Exp::*;
    use super::*;

    macro_rules! bv {
        ( $bv_string:expr ) => {{
            let mut vec = Vec::new();
            for c in $bv_string.chars().rev() {
                if c == '1' {
                    vec.push(true)
                } else if c == '0' {
                    vec.push(false)
                } else {
                    ()
                }
            }
            Bits(vec)
        }};
    }

    fn var(id: u32) -> Exp {
        Var(Sym::from_u32(id))
    }

    #[test]
    fn bv_macro() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(Assert(Eq(Box::new(bv!("0110")), Box::new(bv!("1001")))));
        assert!(solver.check_sat() == Unsat);
    }

    #[test]
    fn get_const() {
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(DeclareConst(Sym::from_u32(0), Ty::BitVec(4)));
        solver.add(DeclareConst(Sym::from_u32(1), Ty::BitVec(1)));
        solver.add(DeclareConst(Sym::from_u32(2), Ty::BitVec(5)));
        solver.add(DeclareConst(Sym::from_u32(3), Ty::BitVec(5)));
        solver.add(DeclareConst(Sym::from_u32(4), Ty::BitVec(257)));
        solver.add(Assert(Eq(Box::new(bv!("0110")), Box::new(var(0)))));
        solver.add(Assert(Eq(Box::new(var(2)), Box::new(var(3)))));
        let big_bv = Box::new(SignExtend(251, Box::new(Bits(vec![true, false, false, true, false, true]))));
        solver.add(Assert(Eq(Box::new(var(4)), big_bv)));
        assert!(solver.check_sat() == Sat);
        let (v0, v2, v3, v4);
        {
            let mut model = Model::new(&solver);
            v0 = model.get_var(Sym::from_u32(0)).unwrap().unwrap();
            assert!(model.get_var(Sym::from_u32(1)).unwrap().is_none());
            v2 = model.get_var(Sym::from_u32(2)).unwrap().unwrap();
            v3 = model.get_var(Sym::from_u32(3)).unwrap().unwrap();
            v4 = model.get_var(Sym::from_u32(4)).unwrap().unwrap();
        }
        solver.add(Assert(Eq(Box::new(var(0)), Box::new(v0))));
        solver.add(Assert(Eq(Box::new(var(2)), Box::new(v2))));
        solver.add(Assert(Eq(Box::new(var(3)), Box::new(v3))));
        solver.add(Assert(Eq(Box::new(var(4)), Box::new(v4))));
        match solver.check_sat() {
            Sat => (),
            _ => panic!("Round-trip failed, trace {:?}", solver.trace()),
        }
    }

    #[test]
    fn get_enum_const() {
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let e = solver.get_enum(3);
        let v0 = solver.declare_const(Ty::Enum(e));
        let v1 = solver.declare_const(Ty::Enum(e));
        let v2 = solver.declare_const(Ty::Enum(e));
        solver.assert_eq(Var(v0), Var(v1));
        assert!(solver.check_sat() == Sat);
        let (m0, m1) = {
            let mut model = Model::new(&solver);
            assert!(model.get_var(v2).unwrap().is_none());
            (model.get_var(v0).unwrap().unwrap(), model.get_var(v1).unwrap().unwrap())
        };
        solver.assert_eq(Var(v0), m0);
        solver.assert_eq(Var(v1), m1);
        match solver.check_sat() {
            Sat => (),
            _ => panic!("Round-trip failed, trace {:?}", solver.trace()),
        }
    }

    #[test]
    fn smt_func() {
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(DeclareFun(Sym::from_u32(0), vec![Ty::BitVec(2), Ty::BitVec(4)], Ty::BitVec(8)));
        solver.add(DeclareConst(Sym::from_u32(1), Ty::BitVec(8)));
        solver.add(DeclareConst(Sym::from_u32(2), Ty::BitVec(2)));
        solver
            .add(Assert(Eq(Box::new(App(Sym::from_u32(0), vec![bv!("10"), bv!("0110")])), Box::new(bv!("01011011")))));
        solver.add(Assert(Eq(Box::new(App(Sym::from_u32(0), vec![var(2), bv!("0110")])), Box::new(var(1)))));
        solver.add(Assert(Eq(Box::new(var(2)), Box::new(bv!("10")))));
        assert!(solver.check_sat() == Sat);
        let mut model = Model::new(&solver);
        let val = model.get_var(Sym::from_u32(1)).unwrap().unwrap();
        assert!(match val {
            Bits64(0b01011011, 8) => true,
            _ => false,
        });
    }

    #[test]
    fn array() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        solver.add(DeclareConst(Sym::from_u32(0), Ty::Array(Box::new(Ty::BitVec(3)), Box::new(Ty::BitVec(4)))));
        solver.add(DeclareConst(Sym::from_u32(1), Ty::BitVec(3)));
        solver.add(Assert(Neq(
            Box::new(Select(
                Box::new(Store(Box::new(var(0)), Box::new(var(1)), Box::new(bv!("0101")))),
                Box::new(var(1)),
            )),
            Box::new(bv!("0101")),
        )));
        assert!(solver.check_sat() == Unsat);
    }
}
