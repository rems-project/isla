// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
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

use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::fmt;

use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::error::ExecError;
use isla_lib::executor::LocalFrame;
use isla_lib::ir;
use isla_lib::ir::{Name, Val};
use isla_lib::log;
use isla_lib::memory::{Memory, Region};
use isla_lib::primop::Primops;
use isla_lib::smt::{checkpoint, smtlib, Checkpoint, Config, Context, Model, SmtResult::Sat, Solver, Sym};
use isla_lib::source_loc::SourceLoc;

use super::{table_address, Index, PageAttrs, PageTables, S1PageAttrs, S2PageAttrs, UpdateWalk, VirtualAddress};
use crate::litmus::{self, Litmus};

pub enum SetupParseError {
    Lex { pos: usize },
}

impl fmt::Display for SetupParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SetupParseError::*;
        match self {
            Lex { pos } => write!(f, "Lexical error at position: {}", pos),
        }
    }
}

#[derive(Debug)]
pub enum SetupError {
    VariableNotFound(String),
    FunctionNotFound(String),
    MappingFailure,
    Nesting(String),
    DuplicateTables(String),
    MissingTableAddress(String),
    NoS1Tables,
    NoS2Tables,
    NoOption(String),
    Type(String),
    WalkError(String),
    AddressError(String),
    Exec(ExecError),
    BadPageAttrsField { stage: usize, field: String, bits: String },
    Arity { name: String, got: usize, expected: usize },
}

impl fmt::Display for SetupError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SetupError::*;
        match self {
            VariableNotFound(var) => write!(f, "Variable not found: {}", var),
            FunctionNotFound(func) => write!(f, "Function not found: {}", func),
            MappingFailure => write!(f, "Could not create page table mapping"),
            Nesting(name) => write!(f, "Nested table description {} can only contain table constraints", name),
            DuplicateTables(name) => write!(f, "Page tables {} already exist", name),
            MissingTableAddress(name) => write!(f, "Require an address argument to declare new page tables {}", name),
            NoS1Tables => write!(f, "No current stage 1 table"),
            NoS2Tables => write!(f, "No current stage 2 table"),
            NoOption(name) => write!(f, "Unrecognised option {}", name),
            WalkError(err) => write!(f, "Error while walking translation table: {}", err),
            AddressError(err) => write!(f, "Error while generating addresses: {}", err),
            Type(desc) => write!(f, "{}", desc),
            Exec(err) => write!(f, "{}", err),
            BadPageAttrsField { stage, field, bits } => {
                write!(f, "Bad attribute field {} = {} for stage {} descriptor", field, bits, stage)
            }
            Arity { name, got, expected } => {
                write!(f, "Function {} got {} arguments, expected {}", name, got, expected)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Walk {
    stage1: Option<UpdateWalk>,
    stage2: Option<UpdateWalk>,
}

#[derive(Clone, Debug)]
pub enum TVal {
    VA(VirtualAddress),
    IPA(VirtualAddress),
    PA(u64),
    TPA(u64),
    I128(i128),
    Invalid,
    Raw(u64),
    Walk(Walk),
}

impl fmt::Display for TVal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TVal::VA(va) => write!(f, "va(0x{:x})", va.bits()),
            TVal::IPA(ipa) => write!(f, "ipa(0x{:x})", ipa.bits()),
            TVal::PA(pa) => write!(f, "pa(0x{:x})", pa),
            TVal::TPA(pa) => write!(f, "tpa(0x{:x})", pa),
            TVal::I128(n) => write!(f, "{}", n),
            TVal::Invalid => write!(f, "invalid"),
            TVal::Raw(n) => write!(f, "raw(0x{:x})", n),
            TVal::Walk(w) => write!(f, "walk({:?})", w),
        }
    }
}

impl TVal {
    fn as_pa(&self) -> Result<u64, SetupError> {
        if let TVal::PA(pa) = self {
            Ok(*pa)
        } else {
            Err(SetupError::Type("Physical address required".to_string()))
        }
    }

    fn to_u64(&self) -> Result<u64, SetupError> {
        match self {
            TVal::VA(va) => Ok(va.bits()),
            TVal::IPA(ipa) => Ok(ipa.bits()),
            TVal::PA(pa) => Ok(*pa),
            TVal::TPA(pa) => Ok(*pa),
            TVal::I128(n) => {
                u64::try_from(*n).map_err(|_| SetupError::Type(format!("{} cannot be converted to u64", n)))
            }
            TVal::Invalid => Ok(0),
            TVal::Raw(n) => Ok(*n),
            TVal::Walk(_) => Err(SetupError::Type("Walk cannot be converted to u64".to_string())),
        }
    }

    fn is_address(&self) -> bool {
        matches!(self, TVal::VA(_) | TVal::IPA(_) | TVal::PA(_) | TVal::TPA(_))
    }

    fn translate<B: BV>(
        &self,
        s1_level0: Option<Index>,
        s2_level0: Option<Index>,
        memory: &Memory<B>,
        solver: &mut Solver<B>,
    ) -> Result<u64, SetupError> {
        use SetupError::*;
        let pa = match self {
            TVal::VA(va) => {
                let s1_level0 = s1_level0.ok_or(SetupError::NoS1Tables)?;
                let s2_level0 = s2_level0.ok_or(SetupError::NoS2Tables)?;
                let ipa = litmus::exp::pa(
                    vec![Val::Bits(B::from_u64(va.bits())), Val::Bits(B::from_u64(table_address(s1_level0)))],
                    litmus::exp::KwArgs::new(),
                    memory,
                    solver,
                )
                .map_err(|err| WalkError(format!("{}", err)))?;
                litmus::exp::pa_u64(
                    vec![ipa, Val::Bits(B::from_u64(table_address(s2_level0)))],
                    litmus::exp::KwArgs::new(),
                    memory,
                    solver,
                )
                .map_err(|err| WalkError(format!("{}", err)))?
            }

            TVal::IPA(ipa) => {
                let s2_level0 = s2_level0.ok_or(SetupError::NoS2Tables)?;
                litmus::exp::pa_u64(
                    vec![Val::Bits(B::from_u64(ipa.bits())), Val::Bits(B::from_u64(table_address(s2_level0)))],
                    litmus::exp::KwArgs::new(),
                    memory,
                    solver,
                )
                .map_err(|err| WalkError(format!("{}", err)))?
            }

            TVal::PA(pa) => *pa,

            addr => return Err(Type(format!("Location {:?} must be an address", addr))),
        };
        Ok(pa)
    }
}

#[derive(Debug)]
struct SetupOptions {
    default_tables: bool,
    self_map: bool,
}

impl Default for SetupOptions {
    fn default() -> Self {
        SetupOptions { default_tables: true, self_map: true }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Stage {
    S1,
    S2,
}

impl Stage {
    fn memory_kind(self) -> &'static str {
        match self {
            Stage::S1 => "stage 1",
            Stage::S2 => "stage 2",
        }
    }

    fn page_size<B>(self, isa_config: &ISAConfig<B>) -> u64 {
        match self {
            Stage::S1 => isa_config.page_size,
            Stage::S2 => isa_config.s2_page_size,
        }
    }
}

#[derive(Debug)]
struct Ctx<B> {
    vars: HashMap<String, TVal>,
    current_s1_tables: usize,
    current_s2_tables: usize,
    all_tables: Vec<(Index, PageTables<B>, Stage)>,
    named_tables: HashMap<String, usize>,
    s1_parents: Vec<usize>,
    s2_parents: Vec<usize>,
    maybe_mapped: HashSet<u64>,
}

// To map a page table into another, we need a mutable reference to
// the destination table, and an immutable reference to the source
// table. Rust's borrow checker won't be happy if we try to do this
// naively, so this struct and the associated get_map_into method for
// Ctx exist to facilitate this.
struct MapInto<'a, B> {
    src_tables: &'a PageTables<B>,
    src_stage: Stage,
    dest_level0: Index,
    dest_tables: &'a mut PageTables<B>,
    dest_stage: Stage,
}

impl<B> Ctx<B> {
    fn s1_tables(&mut self) -> Result<&mut PageTables<B>, SetupError> {
        self.all_tables.get_mut(self.current_s1_tables).ok_or(SetupError::NoS1Tables).map(|t| &mut t.1)
    }

    fn s2_tables(&mut self) -> Result<&mut PageTables<B>, SetupError> {
        self.all_tables.get_mut(self.current_s2_tables).ok_or(SetupError::NoS2Tables).map(|t| &mut t.1)
    }

    fn get_tables_mut(&mut self, i: usize) -> (Index, &mut PageTables<B>, Stage) {
        self.all_tables.get_mut(i).map(|t| (t.0, &mut t.1, t.2)).unwrap()
    }

    fn get_map_into(&mut self, src: usize, dest: usize) -> MapInto<'_, B> {
        assert!(src != dest);

        let (left, right) = self.all_tables.split_at_mut(dest);
        let (mid, right) = right.split_at_mut(1);

        let dest_info = &mut mid[0];
        let src_info = if src < dest { &left[src] } else { &right[src - (dest + 1)] };

        MapInto {
            src_tables: &src_info.1,
            src_stage: src_info.2,
            dest_level0: dest_info.0,
            dest_tables: &mut dest_info.1,
            dest_stage: dest_info.2,
        }
    }

    fn s1_level0(&self) -> Result<Index, SetupError> {
        self.all_tables.get(self.current_s1_tables).ok_or(SetupError::NoS1Tables).map(|t| t.0)
    }

    fn s2_level0(&self) -> Result<Index, SetupError> {
        self.all_tables.get(self.current_s2_tables).ok_or(SetupError::NoS2Tables).map(|t| t.0)
    }

    fn have_s1(&self) -> bool {
        self.current_s1_tables != usize::MAX
    }

    fn have_s2(&self) -> bool {
        self.current_s2_tables != usize::MAX
    }

    fn push_existing(&mut self, stage: Stage, tables_id: usize) {
        match stage {
            Stage::S1 => {
                if self.have_s1() {
                    self.s1_parents.push(self.current_s1_tables);
                }
                self.current_s1_tables = tables_id;
            }
            Stage::S2 => {
                if self.have_s2() {
                    self.s2_parents.push(self.current_s2_tables);
                }
                self.current_s2_tables = tables_id;
            }
        }
    }

    fn push_new(&mut self, name: &str, stage: Stage, level0: Index, tables: PageTables<B>) -> usize {
        let tables_id = self.all_tables.len();
        match stage {
            Stage::S1 => {
                if self.have_s1() {
                    self.s1_parents.push(self.current_s1_tables);
                }
                self.current_s1_tables = tables_id;
            }
            Stage::S2 => {
                if self.have_s2() {
                    self.s2_parents.push(self.current_s2_tables);
                }
                self.current_s2_tables = tables_id;
            }
        }
        self.all_tables.push((level0, tables, stage));

        self.named_tables.insert(name.to_string(), tables_id);
        tables_id
    }

    fn pop(&mut self, stage: Stage) {
        match stage {
            Stage::S1 => {
                let tables_id = self.s1_parents.pop().unwrap_or(usize::MAX);
                self.current_s1_tables = tables_id
            }
            Stage::S2 => {
                let tables_id = self.s2_parents.pop().unwrap_or(usize::MAX);
                self.current_s2_tables = tables_id
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Exp {
    Id(String),
    I128(i128),
    Hex(String),
    Bin(String),
    App(String, Vec<Exp>),
}

fn single_argument<'a>(name: &str, args: &'a [TVal]) -> Result<&'a TVal, SetupError> {
    if args.len() == 1 {
        Ok(&args[0])
    } else {
        Err(SetupError::Type(format!("{} expects a single argument", name)))
    }
}

// Address type conversion functions

fn primop_va_to_pa<B: BV>(args: &[TVal], _: &Ctx<B>) -> Result<TVal, SetupError> {
    if let TVal::VA(va) = single_argument("va_to_pa", args)? {
        Ok(TVal::PA(va.bits()))
    } else {
        Err(SetupError::Type("va_to_pa expects a virtual address argument".to_string()))
    }
}

fn primop_pa_to_va<B: BV>(args: &[TVal], _: &Ctx<B>) -> Result<TVal, SetupError> {
    if let TVal::PA(pa) = single_argument("pa_to_va", args)? {
        Ok(TVal::VA(VirtualAddress::from_u64(*pa)))
    } else {
        Err(SetupError::Type("pa_to_va expects a physical address argument".to_string()))
    }
}

fn primop_va_to_ipa<B: BV>(args: &[TVal], _: &Ctx<B>) -> Result<TVal, SetupError> {
    if let TVal::VA(va) = single_argument("va_to_ipa", args)? {
        Ok(TVal::IPA(*va))
    } else {
        Err(SetupError::Type("va_to_ipa expects a virtual address argument".to_string()))
    }
}

fn primop_ipa_to_va<B: BV>(args: &[TVal], _: &Ctx<B>) -> Result<TVal, SetupError> {
    if let TVal::IPA(ipa) = single_argument("ipa_to_va", args)? {
        Ok(TVal::VA(*ipa))
    } else {
        Err(SetupError::Type("ipa_to_va expects an intermediate physical address argument".to_string()))
    }
}

fn primop_pa_to_ipa<B: BV>(args: &[TVal], _: &Ctx<B>) -> Result<TVal, SetupError> {
    if let TVal::PA(pa) = single_argument("pa_to_ipa", args)? {
        Ok(TVal::IPA(VirtualAddress::from_u64(*pa)))
    } else {
        Err(SetupError::Type("pa_to_ipa expects a physical address argument".to_string()))
    }
}

fn primop_ipa_to_pa<B: BV>(args: &[TVal], _: &Ctx<B>) -> Result<TVal, SetupError> {
    if let TVal::IPA(ipa) = single_argument("ipa_to_pa", args)? {
        Ok(TVal::PA(ipa.bits()))
    } else {
        Err(SetupError::Type("ipa_to_pa expects an intermediate physical address argument".to_string()))
    }
}

fn primop_table<B: BV>(args: &[TVal], _: &Ctx<B>) -> Result<TVal, SetupError> {
    Ok(TVal::TPA(single_argument("table", args)?.to_u64()?))
}

fn primop_desc<B: BV>(args: &[TVal], _: &Ctx<B>) -> Result<TVal, SetupError> {
    Ok(TVal::Raw(single_argument("raw", args)?.to_u64()?))
}

fn primop_walk_table(level: u64, args: &[TVal]) -> Result<TVal, SetupError> {
    match single_argument("tableN", args)? {
        TVal::Walk(w) => match w {
            Walk { stage1: None, stage2: None } => Err(SetupError::Type("empty walk in tableN".to_string())),
            Walk { stage1: Some(w), stage2: None } => Ok(TVal::PA(w.table(level))),
            Walk { stage1: None, stage2: Some(w) } => Ok(TVal::PA(w.table(level))),
            Walk { stage1: Some(w), stage2: Some(_) } => Ok(TVal::PA(w.table(level))),
        },
        _ => Err(SetupError::Type("tableN expects a table walk argument".to_string())),
    }
}

fn primop_walk_pte(level: u64, args: &[TVal]) -> Result<TVal, SetupError> {
    match single_argument("pteN", args)? {
        TVal::Walk(w) => match w {
            Walk { stage1: None, stage2: None } => Err(SetupError::Type("empty walk in pteN".to_string())),
            Walk { stage1: Some(w), stage2: None } => Ok(TVal::PA(w.pte(level))),
            Walk { stage1: None, stage2: Some(w) } => Ok(TVal::PA(w.pte(level))),
            Walk { stage1: Some(w), stage2: Some(_) } => Ok(TVal::PA(w.pte(level))),
        },
        _ => Err(SetupError::Type("pteN expects a table walk argument".to_string())),
    }
}

fn primop_walk_s2table(level: u64, args: &[TVal]) -> Result<TVal, SetupError> {
    match single_argument("s2tableN", args)? {
        TVal::Walk(w) => match w {
            Walk { stage1: _, stage2: None } => Err(SetupError::Type("No stage 2 information in s2tableN".to_string())),
            Walk { stage1: _, stage2: Some(w) } => Ok(TVal::PA(w.table(level))),
        },
        _ => Err(SetupError::Type("s2tableN expects a table walk argument".to_string())),
    }
}

fn primop_walk_s2pte(level: u64, args: &[TVal]) -> Result<TVal, SetupError> {
    match single_argument("s2pteN", args)? {
        TVal::Walk(w) => match w {
            Walk { stage1: _, stage2: None } => Err(SetupError::Type("No stage 2 information in s2pteN".to_string())),
            Walk { stage1: _, stage2: Some(w) } => Ok(TVal::PA(w.pte(level))),
        },
        _ => Err(SetupError::Type("s2pteN expects a table walk argument".to_string())),
    }
}

impl Exp {
    fn subst(&self, args: &HashMap<String, &Exp>) -> Exp {
        match self {
            Exp::Id(name) => match args.get(name) {
                Some(exp) => (*exp).clone(),
                None => Exp::Id(name.clone()),
            },

            Exp::I128(n) => Exp::I128(*n),

            Exp::Hex(hex) => Exp::Hex(hex.clone()),

            Exp::Bin(bin) => Exp::Bin(bin.clone()),

            Exp::App(f, xs) => {
                let xs = xs.iter().map(|x| x.subst(args)).collect();
                Exp::App(f.clone(), xs)
            }
        }
    }

    fn eval_as_constraint<B: BV, A>(
        &self,
        vars: &HashMap<String, (Sym, A)>,
        table_vars: &HashMap<String, TVal>,
        functions: &HashMap<String, (&[String], &Exp)>,
        primops: &Primops<B>,
        frame: &mut LocalFrame<B>,
        solver: &mut Solver<B>,
    ) -> Result<Val<B>, SetupError> {
        use SetupError::*;
        match self {
            Exp::Id(name) => {
                if let Some((v, _)) = vars.get(name) {
                    Ok(Val::Symbolic(*v))
                } else if let Some(v) = table_vars.get(name) {
                    Ok(Val::Bits(B::from_u64(v.to_u64()?)))
                } else {
                    Err(VariableNotFound(name.to_string()))
                }
            }

            Exp::I128(n) => Ok(Val::I128(*n)),

            Exp::Hex(s) | Exp::Bin(s) => match B::from_str(s) {
                Some(bv) => Ok(Val::Bits(bv)),
                None => Err(Type("Hexadecimal string too long".to_string())),
            },

            Exp::App(f, args) if functions.contains_key(f) => {
                let (params, body) = functions.get(f).unwrap();

                if args.len() != params.len() {
                    return Err(Arity { name: f.clone(), got: args.len(), expected: params.len() });
                }

                let mut subst_args: HashMap<String, &Exp> = HashMap::new();
                for (param, arg) in params.iter().zip(args.iter()) {
                    subst_args.insert(param.clone(), arg);
                }

                body.subst(&subst_args).eval_as_constraint(vars, table_vars, functions, primops, frame, solver)
            }

            Exp::App(f, args) => {
                let mut args: Vec<Val<B>> = args
                    .iter()
                    .map(|exp| exp.eval_as_constraint(vars, table_vars, functions, primops, frame, solver))
                    .collect::<Result<_, _>>()?;

                if let Some(unop) = primops.unary.get(f) {
                    if args.len() != 1 {
                        return Err(Arity { name: f.clone(), got: 1, expected: args.len() });
                    };
                    return unop(args.pop().unwrap(), solver, SourceLoc::unknown()).map_err(Exec);
                }

                if let Some(binop) = primops.binary.get(f) {
                    if args.len() != 2 {
                        return Err(Arity { name: f.clone(), got: 2, expected: args.len() });
                    };
                    let arg2 = args.pop().unwrap();
                    let arg1 = args.pop().unwrap();
                    return binop(arg1, arg2, solver, SourceLoc::unknown()).map_err(Exec);
                }

                if let Some(varop) = primops.variadic.get(f) {
                    return varop(args, solver, frame, SourceLoc::unknown()).map_err(Exec);
                }

                Err(FunctionNotFound(f.clone()))
            }
        }
    }

    fn eval<B: BV>(&self, ctx: &Ctx<B>) -> Result<TVal, SetupError> {
        use SetupError::*;
        match self {
            Exp::Id(name) => match ctx.vars.get(name) {
                Some(v) => {
                    log!(log::MEMORY, &format!("lookup {} -> {}", name, v));
                    Ok(v.clone())
                }
                None => Err(VariableNotFound(name.to_string())),
            },

            Exp::I128(n) => Ok(TVal::I128(*n)),

            Exp::Hex(hex) => u64::from_str_radix(&hex[2..], 16)
                .map(TVal::PA)
                .map_err(|_| AddressError(format!("Hexadecimal value {} is not a valid physical address", hex))),

            Exp::Bin(bin) => u64::from_str_radix(&bin[2..], 2)
                .map(TVal::PA)
                .map_err(|_| AddressError(format!("Binary value {} is not a valid physical address", bin))),

            Exp::App(f, args) => {
                let args: Vec<TVal> = args.iter().map(|exp| exp.eval(ctx)).collect::<Result<_, _>>()?;
                if f == "va_to_pa" {
                    primop_va_to_pa(&args, ctx)
                } else if f == "pa_to_va" {
                    primop_pa_to_va(&args, ctx)
                } else if f == "ipa_to_va" {
                    primop_ipa_to_va(&args, ctx)
                } else if f == "va_to_ipa" {
                    primop_va_to_ipa(&args, ctx)
                } else if f == "pa_to_ipa" {
                    primop_pa_to_ipa(&args, ctx)
                } else if f == "ipa_to_pa" {
                    primop_ipa_to_pa(&args, ctx)
                } else if f == "table" {
                    primop_table(&args, ctx)
                } else if f == "raw" {
                    primop_desc(&args, ctx)
                } else if let Some(level) = f.strip_prefix("table") {
                    let level = level
                        .parse::<u64>()
                        .map_err(|e| SetupError::Type(format!("Failed to parse tableN suffix {}: {}", level, e)))?;
                    primop_walk_table(level, &args)
                } else if let Some(level) = f.strip_prefix("pte") {
                    let level = level
                        .parse::<u64>()
                        .map_err(|e| SetupError::Type(format!("Failed to parse pteN suffix {}: {}", level, e)))?;
                    primop_walk_pte(level, &args)
                } else if let Some(level) = f.strip_prefix("s2table") {
                    let level = level
                        .parse::<u64>()
                        .map_err(|e| SetupError::Type(format!("Failed to parse s2tableN suffix {}: {}", level, e)))?;
                    primop_walk_s2table(level, &args)
                } else if let Some(level) = f.strip_prefix("s2pte") {
                    let level = level
                        .parse::<u64>()
                        .map_err(|e| SetupError::Type(format!("Failed to parse s2pteN suffix {}: {}", level, e)))?;
                    primop_walk_s2pte(level, &args)
                } else {
                    Err(FunctionNotFound(f.to_string()))
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum AddressConstraint {
    Physical(u64, Vec<String>),
    Intermediate(u64, Vec<String>),
    Virtual(u64, Vec<String>),
    Assertion(Exp),
    Function(String, Vec<String>, Exp),
}

#[derive(Debug)]
pub enum Attrs {
    Default(Vec<(String, String)>),
    Code,
    Stages(Box<Attrs>, Box<Attrs>),
}

fn with_fields<B: BV, A: PageAttrs>(mut attrs: A, stage: usize, fields: &[(String, String)]) -> Result<A, SetupError> {
    for (field, bits) in fields.iter() {
        if let Some(bits) = B::from_str(bits) {
            if attrs.set_field(field, bits).is_none() {
                return Err(SetupError::BadPageAttrsField { stage, field: field.to_string(), bits: bits.to_string() });
            }
        } else {
            return Err(SetupError::BadPageAttrsField { stage, field: field.to_string(), bits: bits.to_string() });
        }
    }
    Ok(attrs)
}

impl Attrs {
    fn stage1<B: BV>(&self) -> Result<S1PageAttrs, SetupError> {
        match self {
            Attrs::Default(fields) => with_fields::<B, _>(S1PageAttrs::default(), 1, fields),
            Attrs::Code => Ok(S1PageAttrs::code()),
            Attrs::Stages(s1, _) => s1.stage1::<B>(),
        }
    }

    fn stage2<B: BV>(&self) -> Result<S2PageAttrs, SetupError> {
        match self {
            Attrs::Default(fields) => with_fields::<B, _>(S2PageAttrs::default(), 2, fields),
            Attrs::Code => Ok(S2PageAttrs::code()),
            Attrs::Stages(_, s2) => s2.stage2::<B>(),
        }
    }
}

#[derive(Debug)]
pub enum TableConstraint {
    IdentityMap(Exp, Attrs, u64, Option<String>),
    MapsTo(Exp, Exp, Attrs, u64, Option<String>),
    MaybeMapsTo(Exp, Exp, Attrs, u64, Option<String>),
}

#[derive(Debug)]
pub enum Constraint {
    Option(String, bool),
    Address(AddressConstraint),
    Table(TableConstraint),
    Initial(Exp, Exp),
    Nested(Stage, String, Option<Exp>, Vec<Constraint>),
}

fn identity_map<B: BV>(addr: TVal, attrs: &Attrs, level: u64, ctx: &mut Ctx<B>) -> Result<Walk, SetupError> {
    use SetupError::*;
    log!(log::MEMORY, &format!("identity {}", addr));

    Ok(match addr {
        TVal::VA(va) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk = ctx
                .s1_tables()?
                .identity_map(s1_level0, va.bits(), attrs.stage1::<B>()?, level)
                .ok_or(MappingFailure)?;
            Walk { stage1: Some(s1_walk), stage2: None }
        }

        TVal::IPA(ipa) => {
            let s2_level0 = ctx.s2_level0()?;
            let s2_walk = ctx
                .s2_tables()?
                .identity_map(s2_level0, ipa.bits(), attrs.stage2::<B>()?, level)
                .ok_or(MappingFailure)?;
            Walk { stage1: None, stage2: Some(s2_walk) }
        }

        TVal::PA(pa) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk =
                ctx.s1_tables()?.identity_map(s1_level0, pa, attrs.stage1::<B>()?, level).ok_or(MappingFailure)?;
            let s2_walk = if ctx.have_s2() {
                let s2_level0 = ctx.s2_level0()?;
                Some(ctx.s2_tables()?.identity_map(s2_level0, pa, attrs.stage2::<B>()?, level).ok_or(MappingFailure)?)
            } else {
                None
            };
            Walk { stage1: Some(s1_walk), stage2: s2_walk }
        }

        addr => return Err(Type(format!("Type error creating identity mapping for {}: Expected addresses", addr))),
    })
}

fn maps_to<B: BV>(from: TVal, to: TVal, attrs: &Attrs, level: u64, ctx: &mut Ctx<B>) -> Result<Walk, SetupError> {
    use SetupError::*;
    log!(log::MEMORY, &format!("{} |-> {}", from, to));

    Ok(match (from, to) {
        /* va -> pa, va -> ipa, ipa -> pa */
        (TVal::VA(va), TVal::PA(pa)) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk =
                ctx.s1_tables()?.map(s1_level0, va, pa, false, attrs.stage1::<B>()?, level).ok_or(MappingFailure)?;
            let s2_walk = if ctx.have_s2() {
                let s2_level0 = ctx.s2_level0()?;
                Some(ctx.s2_tables()?.identity_map(s2_level0, pa, attrs.stage2::<B>()?, level).ok_or(MappingFailure)?)
            } else {
                None
            };
            Walk { stage1: Some(s1_walk), stage2: s2_walk }
        }

        (TVal::VA(va), TVal::IPA(ipa)) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk = ctx
                .s1_tables()?
                .map(s1_level0, va, ipa.bits(), false, attrs.stage1::<B>()?, level)
                .ok_or(MappingFailure)?;
            Walk { stage1: Some(s1_walk), stage2: None }
        }

        (TVal::IPA(ipa), TVal::PA(pa)) => {
            let s2_level0 = ctx.s2_level0()?;
            let s2_walk =
                ctx.s2_tables()?.map(s2_level0, ipa, pa, false, attrs.stage2::<B>()?, level).ok_or(MappingFailure)?;
            Walk { stage1: None, stage2: Some(s2_walk) }
        }

        /* va/ipa -> tpa */
        (TVal::VA(va), TVal::TPA(pa)) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk =
                ctx.s1_tables()?.map(s1_level0, va, pa, true, attrs.stage1::<B>()?, level).ok_or(MappingFailure)?;
            Walk { stage1: Some(s1_walk), stage2: None }
        }

        (TVal::IPA(ipa), TVal::TPA(pa)) => {
            let s2_level0 = ctx.s2_level0()?;
            let s2_walk =
                ctx.s2_tables()?.map(s2_level0, ipa, pa, true, attrs.stage2::<B>()?, level).ok_or(MappingFailure)?;
            Walk { stage1: None, stage2: Some(s2_walk) }
        }

        /* va/ipa -> invalid */
        (TVal::VA(va), TVal::Invalid) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk = ctx.s1_tables()?.invalid(s1_level0, va, level).ok_or(MappingFailure)?;
            Walk { stage1: Some(s1_walk), stage2: None }
        }

        (TVal::IPA(ipa), TVal::Invalid) => {
            let s2_level0 = ctx.s2_level0()?;
            let s2_walk = ctx.s2_tables()?.invalid(s2_level0, ipa, level).ok_or(MappingFailure)?;
            Walk { stage1: None, stage2: Some(s2_walk) }
        }

        (from, to) => return Err(Type(format!("Type error creating mapping {} |-> {}: Expected addresses", from, to))),
    })
}

fn _maybe_maps_to<B: BV>(
    from: TVal,
    to: TVal,
    attrs: &Attrs,
    level: u64,
    ctx: &mut Ctx<B>,
) -> Result<Walk, SetupError> {
    use SetupError::*;
    log!(log::MEMORY, &format!("{} ?-> {}", from, to));

    Ok(match (from, to) {
        /* va -> pa, va -> ipa, ipa -> pa */
        (TVal::VA(va), TVal::PA(pa)) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk = ctx
                .s1_tables()?
                .maybe_map(s1_level0, va, pa, false, attrs.stage1::<B>()?, level)
                .ok_or(MappingFailure)?;
            let s2_walk = if ctx.have_s2() {
                let s2_level0 = ctx.s2_level0()?;
                Some(ctx.s2_tables()?.identity_map(s2_level0, pa, attrs.stage2::<B>()?, level).ok_or(MappingFailure)?)
            } else {
                None
            };
            Walk { stage1: Some(s1_walk), stage2: s2_walk }
        }

        (TVal::VA(va), TVal::IPA(ipa)) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk = ctx
                .s1_tables()?
                .maybe_map(s1_level0, va, ipa.bits(), false, attrs.stage1::<B>()?, level)
                .ok_or(MappingFailure)?;
            Walk { stage1: Some(s1_walk), stage2: None }
        }

        (TVal::IPA(ipa), TVal::PA(pa)) => {
            let s2_level0 = ctx.s2_level0()?;
            let s2_walk = ctx
                .s2_tables()?
                .maybe_map(s2_level0, ipa, pa, false, attrs.stage2::<B>()?, level)
                .ok_or(MappingFailure)?;
            Walk { stage1: None, stage2: Some(s2_walk) }
        }

        /* va/ipa -> tpa */
        (TVal::VA(va), TVal::TPA(pa)) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk = ctx
                .s1_tables()?
                .maybe_map(s1_level0, va, pa, true, attrs.stage1::<B>()?, level)
                .ok_or(MappingFailure)?;
            Walk { stage1: Some(s1_walk), stage2: None }
        }

        (TVal::IPA(ipa), TVal::TPA(pa)) => {
            let s2_level0 = ctx.s2_level0()?;
            let s2_walk = ctx
                .s2_tables()?
                .maybe_map(s2_level0, ipa, pa, true, attrs.stage2::<B>()?, level)
                .ok_or(MappingFailure)?;
            Walk { stage1: None, stage2: Some(s2_walk) }
        }

        /* va/ipa -> invalid */
        (TVal::VA(va), TVal::Invalid) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk = ctx.s1_tables()?.maybe_invalid(s1_level0, va, level).ok_or(MappingFailure)?;
            Walk { stage1: Some(s1_walk), stage2: None }
        }

        (TVal::IPA(ipa), TVal::Invalid) => {
            let s2_level0 = ctx.s2_level0()?;
            let s2_walk = ctx.s2_tables()?.maybe_invalid(s2_level0, ipa, level).ok_or(MappingFailure)?;
            Walk { stage1: None, stage2: Some(s2_walk) }
        }

        /* va/ipa -> raw */
        (TVal::VA(va), TVal::Raw(desc)) => {
            let s1_level0 = ctx.s1_level0()?;
            let s1_walk = ctx.s1_tables()?.maybe_raw_desc(s1_level0, va, level, desc).ok_or(MappingFailure)?;
            Walk { stage1: Some(s1_walk), stage2: None }
        }

        (TVal::IPA(ipa), TVal::Raw(desc)) => {
            let s2_level0 = ctx.s2_level0()?;
            let s2_walk = ctx.s2_tables()?.maybe_raw_desc(s2_level0, ipa, level, desc).ok_or(MappingFailure)?;
            Walk { stage1: None, stage2: Some(s2_walk) }
        }

        (from, to) => return Err(Type(format!("Type error creating mapping {} |-> {}: Expected addresses", from, to))),
    })
}

fn maybe_maps_to<B: BV>(from: TVal, to: TVal, attrs: &Attrs, level: u64, ctx: &mut Ctx<B>) -> Result<Walk, SetupError> {
    let r = _maybe_maps_to(from, to, attrs, level, ctx);

    if let Ok(w) = &r {
        if let Some(s1) = &w.stage1 {
            for p in &s1.updated {
                ctx.maybe_mapped.insert(*p);
            }
        }
        if let Some(s2) = &w.stage2 {
            for p in &s2.updated {
                ctx.maybe_mapped.insert(*p);
            }
        }
    }

    r
}

impl TableConstraint {
    fn eval<B: BV>(&self, ctx: &mut Ctx<B>) -> Result<(), SetupError> {
        use TableConstraint::*;

        let (name, walk) = match self {
            IdentityMap(addr_exp, attrs, level, name) => {
                let addr = addr_exp.eval(ctx)?;
                (name, identity_map(addr, attrs, *level, ctx)?)
            }

            MapsTo(from_exp, to_exp, attrs, level, name) => {
                let from = from_exp.eval(ctx)?;
                let to = to_exp.eval(ctx)?;
                (name, maps_to(from, to, attrs, *level, ctx)?)
            }

            MaybeMapsTo(from_exp, to_exp, attrs, level, name) => {
                let from = from_exp.eval(ctx)?;
                let to = to_exp.eval(ctx)?;
                (name, maybe_maps_to(from, to, attrs, *level, ctx)?)
            }
        };

        if let Some(name) = name {
            ctx.vars.insert(name.clone(), TVal::Walk(walk));
        }

        Ok(())
    }
}

fn u64_to_va(addr: u64) -> TVal {
    TVal::VA(VirtualAddress::from_u64(addr))
}

fn u64_to_ipa(addr: u64) -> TVal {
    TVal::IPA(VirtualAddress::from_u64(addr))
}

fn eval_address_constraints<B: BV>(
    constraints: &[Constraint],
    table_vars: &mut HashMap<String, TVal>,
    isa_config: &ISAConfig<B>,
) -> Result<(), SetupError> {
    use smtlib::Def::*;
    use smtlib::Exp::*;
    use smtlib::Ty;
    use AddressConstraint::*;
    use SetupError::*;

    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::<B>::new(&ctx);

    let mut vars = HashMap::new();
    let primops = Primops::default();
    let mut functions = HashMap::new();
    let mut dummy_frame = LocalFrame::new(Name::from_u32(u32::MAX), &[], &ir::Ty::Unit, None, &[]);

    for constraint in constraints {
        if let Constraint::Address(ac) = constraint {
            match ac {
                Virtual(alignment, addrs) | Intermediate(alignment, addrs) | Physical(alignment, addrs) => {
                    for addr in addrs {
                        let v = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
                        // Require that address is in the range [base, top)
                        solver.add(Assert(Bvuge(
                            Box::new(Var(v)),
                            Box::new(Bits64(B64::from_u64(isa_config.symbolic_addr_base))),
                        )));
                        solver.add(Assert(Bvult(
                            Box::new(Var(v)),
                            Box::new(Bits64(B64::from_u64(isa_config.symbolic_addr_top))),
                        )));

                        // Minimum alignment requirement based on address stride
                        let alignment =
                            Bvsub(Box::new(Bits64(B64::from_u64(*alignment))), Box::new(Bits64(B64::from_u64(1))));
                        solver.add(Assert(Eq(
                            Box::new(Bvand(Box::new(Var(v)), Box::new(alignment))),
                            Box::new(Bits64(B64::from_u64(0))),
                        )));

                        if matches!(ac, Virtual(_, _)) {
                            vars.insert(addr.clone(), (v, u64_to_va as fn(u64) -> TVal));
                        } else if matches!(ac, Intermediate(_, _)) {
                            vars.insert(addr.clone(), (v, u64_to_ipa as fn(u64) -> TVal));
                        } else {
                            vars.insert(addr.clone(), (v, TVal::PA as fn(u64) -> TVal));
                        }
                    }

                    // Ensure all addresses generated for one declaration are disjoint
                    for (i, addr1) in addrs.iter().enumerate() {
                        for addr2 in &addrs[i + 1..] {
                            let addr1 = vars.get(addr1).unwrap().0;
                            let addr2 = vars.get(addr2).unwrap().0;
                            solver.add(Assert(Neq(Box::new(Var(addr1)), Box::new(Var(addr2)))));
                        }
                    }
                }

                Assertion(exp) => {
                    match exp.eval_as_constraint(
                        &vars,
                        table_vars,
                        &functions,
                        &primops,
                        &mut dummy_frame,
                        &mut solver,
                    )? {
                        Val::Symbolic(b) => solver.add(smtlib::Def::Assert(smtlib::Exp::Var(b))),
                        Val::Bool(true) => (),
                        Val::Bool(false) => {
                            return Err(AddressError(
                                "Address constraint is guaranteed to be unsatisfiable".to_string(),
                            ))
                        }
                        _ => return Err(Type("Address constraint did not evaluate to a boolean value".to_string())),
                    }
                }

                Function(name, params, body) => {
                    if functions.insert(name.clone(), (params, body)).is_some() {
                        return Err(AddressError(format!("Function {} has been defined twice", name)));
                    }
                }
            }
        }
    }

    if solver.check_sat(SourceLoc::unknown()) != Sat {
        return Err(AddressError("No satisfiable set of addresses".to_string()));
    }

    let mut model = Model::new(&solver);
    for (name, (sym, to_val)) in vars {
        let value = model.get_var(sym).map_err(|err| AddressError(format!("{}", err)))?.unwrap();
        match value {
            Bits64(bv) => {
                log!(log::MEMORY, &format!("{} = {}", name, bv));
                table_vars.insert(name.clone(), to_val(bv.lower_u64()));
            }
            _ => {
                return Err(AddressError(format!("Address value {:?} was not a bitvector in satisfiable model", value)))
            }
        }
    }

    Ok(())
}

fn map_code<B: BV>(
    tables_id: usize,
    ctx: &mut Ctx<B>,
    num_threads: usize,
    isa_config: &ISAConfig<B>,
) -> Result<(), SetupError> {
    let (level0, tables, stage) = ctx.get_tables_mut(tables_id);

    // We map each thread's code into each new set of page tables
    for i in 0..num_threads {
        let addr = isa_config.thread_base + (i as u64 * isa_config.page_size);
        let _ = match stage {
            Stage::S1 => tables.identity_map(level0, addr, S1PageAttrs::code(), 3).ok_or(SetupError::MappingFailure)?,
            Stage::S2 => tables.identity_map(level0, addr, S2PageAttrs::code(), 3).ok_or(SetupError::MappingFailure)?,
        };
    }

    Ok(())
}

fn map_tables<B: BV>(
    src_tables_id: usize,
    dest_tables_id: usize,
    ctx: &mut Ctx<B>,
    isa_config: &ISAConfig<B>,
) -> Result<(), SetupError> {
    log!(log::MEMORY, &format!("Map table {} into {}", src_tables_id, dest_tables_id));

    if src_tables_id == dest_tables_id {
        let (level0, tables, stage) = ctx.get_tables_mut(dest_tables_id);

        let mut page = tables.range().start;
        while page < tables.range().end {
            let _ = match stage {
                Stage::S1 => {
                    tables.identity_map(level0, page, S1PageAttrs::default(), 3).ok_or(SetupError::MappingFailure)?
                }
                Stage::S2 => {
                    tables.identity_map(level0, page, S2PageAttrs::default(), 3).ok_or(SetupError::MappingFailure)?
                }
            };
            page += stage.page_size(isa_config)
        }
    } else {
        let MapInto { src_tables, src_stage, dest_level0, dest_tables, dest_stage } =
            ctx.get_map_into(src_tables_id, dest_tables_id);

        let mut page = src_tables.range().start;
        while page < src_tables.range().end {
            let _ = match dest_stage {
                Stage::S1 => dest_tables
                    .identity_map(dest_level0, page, S1PageAttrs::default(), 3)
                    .ok_or(SetupError::MappingFailure)?,
                Stage::S2 => dest_tables
                    .identity_map(dest_level0, page, S2PageAttrs::default(), 3)
                    .ok_or(SetupError::MappingFailure)?,
            };
            page += src_stage.page_size(isa_config)
        }
    }
    Ok(())
}

fn eval_table_constraints<B: BV>(
    constraints: &[Constraint],
    options: &SetupOptions,
    ctx: &mut Ctx<B>,
    num_threads: usize,
    isa_config: &ISAConfig<B>,
) -> Result<Vec<(TVal, TVal)>, SetupError> {
    let mut initials = Vec::new();

    for constraint in constraints {
        match constraint {
            Constraint::Option(_, _) => (),
            Constraint::Address(_) => (),
            Constraint::Table(tc) => tc.eval(ctx)?,
            Constraint::Initial(addr_exp, exp) => {
                let addr = addr_exp.eval(ctx)?;
                let val = exp.eval(ctx)?;
                initials.push((addr, val))
            }
            Constraint::Nested(stage, name, addr_exp, constraints) => {
                // First check that we only have nested table constraints
                if constraints
                    .iter()
                    .any(|c| matches!(c, Constraint::Option(_, _) | Constraint::Address(_) | Constraint::Initial(_, _)))
                {
                    return Err(SetupError::Nesting(name.clone()));
                }

                let (src_tables_id, is_new) = if let Some(i) = ctx.named_tables.get(name).copied() {
                    if addr_exp.is_some() {
                        return Err(SetupError::DuplicateTables(name.clone()));
                    }
                    ctx.push_existing(*stage, i);
                    (i, false)
                } else {
                    let addr = addr_exp
                        .as_ref()
                        .ok_or_else(|| SetupError::MissingTableAddress(name.clone()))?
                        .eval(ctx)?
                        .as_pa()?;

                    ctx.vars.insert(name.clone(), TVal::TPA(addr));

                    let mut tables = PageTables::<B>::new(stage.memory_kind(), addr);
                    let level0 = tables.alloc();
                    (ctx.push_new(name, *stage, level0, tables), true)
                };

                let _ = eval_table_constraints(constraints, options, ctx, num_threads, isa_config)?;

                // Map the thread code before mapping tables into each other
                map_code(src_tables_id, ctx, num_threads, isa_config)?;

                // Map the new tables into parents, and into itself if required
                let mut dest_tables_ids: Vec<usize> =
                    ctx.s1_parents.iter().copied().chain(ctx.s2_parents.iter().copied()).collect();
                match stage {
                    Stage::S1 if ctx.have_s2() => dest_tables_ids.push(ctx.current_s2_tables),
                    Stage::S2 if ctx.have_s1() => dest_tables_ids.push(ctx.current_s1_tables),
                    _ => (),
                };
                if options.self_map && is_new {
                    dest_tables_ids.push(src_tables_id)
                }

                for dest_tables_id in dest_tables_ids.iter().copied() {
                    map_tables(src_tables_id, dest_tables_id, ctx, isa_config)?
                }

                ctx.pop(*stage)
            }
        }
    }

    Ok(initials)
}

fn eval_options(constraints: &[Constraint]) -> Result<SetupOptions, SetupError> {
    let mut options = SetupOptions::default();

    for constraint in constraints {
        if let Constraint::Option(name, b) = constraint {
            if name == "default_tables" {
                options.default_tables = *b
            } else if name == "self_map" {
                options.self_map = *b
            } else {
                return Err(SetupError::NoOption(name.clone()));
            }
        }
    }

    Ok(options)
}

fn eval_initial_constraints<B: BV>(
    constraints: &[(TVal, TVal)],
    s1_level0: Option<Index>,
    s2_level0: Option<Index>,
    memory: &Memory<B>,
    solver: &mut Solver<B>,
) -> Result<HashMap<u64, u64>, SetupError> {
    let mut initial_physical_addrs = HashMap::new();

    for (addr, val) in constraints {
        let pa = addr.translate(s1_level0, s2_level0, memory, solver)?;
        initial_physical_addrs.insert(pa, val.to_u64()?);
    }

    Ok(initial_physical_addrs)
}

pub struct PageTableSetup<B> {
    pub memory_checkpoint: Checkpoint<B>,
    pub all_addrs: HashMap<String, u64>,
    pub physical_addrs: HashMap<String, u64>,
    pub initial_physical_addrs: HashMap<u64, u64>,
    pub tables: HashMap<String, (u64, &'static str)>,
    pub maybe_mapped: HashSet<u64>,
}

/// Create page tables in memory from a litmus file
pub fn armv8_litmus_page_tables<B: BV>(
    memory: &mut Memory<B>,
    litmus: &Litmus<B>,
    isa_config: &ISAConfig<B>,
) -> Result<PageTableSetup<B>, SetupError> {
    let vars: HashMap<String, TVal> =
        litmus.symbolic_addrs.iter().map(|(v, addr)| (v.clone(), TVal::VA(VirtualAddress::from_u64(*addr)))).collect();

    armv8_page_tables(memory, vars, litmus.threads.len(), &litmus.page_table_setup, isa_config)
}

pub fn armv8_page_tables<B: BV>(
    memory: &mut Memory<B>,
    mut vars: HashMap<String, TVal>,
    num_threads: usize,
    page_table_setup: &[Constraint],
    isa_config: &ISAConfig<B>,
) -> Result<PageTableSetup<B>, SetupError> {
    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::<B>::new(&ctx);

    let options = eval_options(page_table_setup)?;

    vars.insert("invalid".to_string(), TVal::Invalid);
    eval_address_constraints::<B>(page_table_setup, &mut vars, isa_config)?;

    let (mut ctx, map_into): (_, Vec<(usize, usize)>) = if options.default_tables {
        // Create default page tables for both stage 1 and stage 2 address translation
        let mut s1_tables = PageTables::new("stage 1", isa_config.page_table_base);
        let mut s2_tables = PageTables::new("stage 2", isa_config.s2_page_table_base);

        let s1_level0 = s1_tables.alloc();
        let s2_level0 = s2_tables.alloc();

        let mut named_tables = HashMap::new();
        named_tables.insert("s1_default".to_string(), 0);
        named_tables.insert("s2_default".to_string(), 1);

        (
            Ctx {
                vars,
                current_s1_tables: 0,
                current_s2_tables: 1,
                all_tables: vec![(s1_level0, s1_tables, Stage::S1), (s2_level0, s2_tables, Stage::S2)],
                named_tables,
                s1_parents: Vec::new(),
                s2_parents: Vec::new(),
                maybe_mapped: HashSet::new(),
            },
            vec![(0, 0), (0, 1), (1, 0), (1, 1)],
        )
    } else {
        (
            Ctx {
                vars,
                current_s1_tables: usize::MAX,
                current_s2_tables: usize::MAX,
                all_tables: Vec::new(),
                named_tables: HashMap::new(),
                s1_parents: Vec::new(),
                s2_parents: Vec::new(),
                maybe_mapped: HashSet::new(),
            },
            Vec::new(),
        )
    };

    let initial_constraints = eval_table_constraints(page_table_setup, &options, &mut ctx, num_threads, isa_config)?;

    if options.default_tables {
        for tables_id in 0..ctx.all_tables.len() {
            map_code(tables_id, &mut ctx, num_threads, isa_config)?
        }
    }

    // Map the tables specified by src_tables_id into the tables specified by dest_tables_id
    for (src_tables_id, dest_tables_id) in map_into.iter().copied() {
        map_tables(src_tables_id, dest_tables_id, &mut ctx, isa_config)?
    }

    let s1_level0 = ctx.s1_level0().ok();
    let s2_level0 = ctx.s2_level0().ok();
    let tables: HashMap<String, (u64, &'static str)> = ctx
        .named_tables
        .iter()
        .map(|(name, idx)| {
            let (_, ptable, stage) = ctx.all_tables.get(*idx).unwrap();
            (name.clone(), (ptable.base_addr, stage.memory_kind()))
        })
        .collect();

    for (_, tables, _) in ctx.all_tables.drain(..) {
        memory.add_region(Region::Custom(tables.range(), Box::new(tables.freeze())))
    }

    let initial_physical_addrs =
        eval_initial_constraints(&initial_constraints, s1_level0, s2_level0, memory, &mut solver)?;

    let physical_addrs: HashMap<String, u64> = ctx
        .vars
        .iter()
        .filter(|(_, v)| v.is_address())
        .map(|(name, v)| (name.clone(), v.translate(s1_level0, s2_level0, memory, &mut solver).unwrap_or(0)))
        .collect();

    let all_addrs: HashMap<String, u64> =
        ctx.vars.drain().filter(|(_, v)| v.is_address()).map(|(name, v)| (name, v.to_u64().unwrap())).collect();

    let maybe_mapped: HashSet<u64> = ctx.maybe_mapped;

    Ok(PageTableSetup {
        memory_checkpoint: checkpoint(&mut solver),
        all_addrs,
        physical_addrs,
        initial_physical_addrs,
        tables,
        maybe_mapped,
    })
}
