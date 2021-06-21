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

use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;

use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::error::ExecError;
use isla_lib::executor::LocalFrame;
use isla_lib::ir::source_loc::SourceLoc;
use isla_lib::ir::{Name, Val};
use isla_lib::log;
use isla_lib::memory::{Memory, Region};
use isla_lib::primop::Primops;
use isla_lib::smt::{checkpoint, smtlib, Checkpoint, Config, Context, Model, SmtResult::Sat, Solver, Sym};

use super::{table_address, L012Index, PageTables, S1PageAttrs, S2PageAttrs, VirtualAddress};
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
    Type(String),
    WalkError(String),
    AddressError(String),
    Exec(ExecError),
    Arity { name: String, got: usize, expected: usize },
}

impl fmt::Display for SetupError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SetupError::*;
        match self {
            VariableNotFound(var) => write!(f, "Variable not found: {}", var),
            FunctionNotFound(func) => write!(f, "Function not found: {}", func),
            MappingFailure => write!(f, "Could not create page table mapping"),
            WalkError(err) => write!(f, "Error while walking translation table: {}", err),
            AddressError(err) => write!(f, "Error while generating addresses: {}", err),
            Type(desc) => write!(f, "{}", desc),
            Exec(err) => write!(f, "{}", err),
            Arity { name, got, expected } => {
                write!(f, "Function {} got {} arguments, expected {}", name, got, expected)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum TVal {
    VA(VirtualAddress),
    IPA(VirtualAddress),
    PA(u64),
    I128(i128),
    Invalid,
}

impl TVal {
    fn to_u64(&self) -> Result<u64, SetupError> {
        match self {
            TVal::VA(va) => Ok(va.bits()),
            TVal::IPA(ipa) => Ok(ipa.bits()),
            TVal::PA(pa) => Ok(*pa),
            TVal::I128(n) => {
                u64::try_from(*n).map_err(|_| SetupError::Type(format!("{} cannot be converted to u64", n)))
            }
            TVal::Invalid => Ok(0),
        }
    }

    fn is_address(&self) -> bool {
        matches!(self, TVal::VA(_) | TVal::IPA(_) | TVal::PA(_))
    }

    fn translate<B: BV>(
        &self,
        s1_level0: L012Index,
        s2_level0: L012Index,
        memory: &Memory<B>,
        solver: &mut Solver<B>,
    ) -> Result<u64, SetupError> {
        use SetupError::*;
        let pa = match self {
            TVal::VA(va) => {
                let ipa = litmus::exp::pa(
                    vec![Val::Bits(B::from_u64(va.bits())), Val::Bits(B::from_u64(table_address(s1_level0)))],
                    memory,
                    solver,
                )
                .map_err(|err| WalkError(format!("{}", err)))?;
                litmus::exp::pa_u64(vec![ipa, Val::Bits(B::from_u64(table_address(s2_level0)))], memory, solver)
                    .map_err(|err| WalkError(format!("{}", err)))?
            }
            TVal::IPA(ipa) => litmus::exp::pa_u64(
                vec![Val::Bits(B::from_u64(ipa.bits())), Val::Bits(B::from_u64(table_address(s2_level0)))],
                memory,
                solver,
            )
            .map_err(|err| WalkError(format!("{}", err)))?,
            TVal::PA(pa) => *pa,
            addr => return Err(Type(format!("Location {:?} must be an address", addr))),
        };
        Ok(pa)
    }
}

struct Ctx<'tbl, B> {
    vars: HashMap<String, TVal>,
    s1_tables: RefCell<&'tbl mut PageTables<B>>,
    s2_tables: RefCell<&'tbl mut PageTables<B>>,
    s1_level0: L012Index,
    s2_level0: L012Index,
}

#[derive(Clone)]
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
        functions: &HashMap<String, (&[String], &Exp)>,
        primops: &Primops<B>,
        frame: &mut LocalFrame<B>,
        solver: &mut Solver<B>,
    ) -> Result<Val<B>, SetupError> {
        use SetupError::*;
        match self {
            Exp::Id(name) => match vars.get(name) {
                Some((v, _)) => Ok(Val::Symbolic(*v)),
                None => Err(VariableNotFound(name.to_string())),
            },

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

                body.subst(&subst_args).eval_as_constraint(vars, functions, primops, frame, solver)
            }

            Exp::App(f, args) => {
                let mut args: Vec<Val<B>> = args
                    .iter()
                    .map(|exp| exp.eval_as_constraint(vars, functions, primops, frame, solver))
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
                Some(v) => Ok(v.clone()),
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
                } else {
                    Err(FunctionNotFound(f.to_string()))
                }
            }
        }
    }
}

pub enum AddressConstraint {
    Physical(Vec<String>),
    Intermediate(Vec<String>),
    Virtual(Vec<String>),
    Assertion(Exp),
    Function(String, Vec<String>, Exp),
}

pub enum Attrs {
    Default,
    Code,
}

impl Attrs {
    fn stage1(&self) -> S1PageAttrs {
        match self {
            Attrs::Default => S1PageAttrs::default(),
            Attrs::Code => S1PageAttrs::code(),
        }
    }

    fn stage2(&self) -> S2PageAttrs {
        match self {
            Attrs::Default => S2PageAttrs::default(),
            Attrs::Code => S2PageAttrs::code(),
        }
    }
}

pub enum TableConstraint {
    IdentityMap(Exp, Attrs),
    MapsTo(Exp, Exp, Attrs),
    MaybeMapsTo(Exp, Exp, Attrs),
}

pub enum Constraint {
    Address(AddressConstraint),
    Table(TableConstraint),
    Initial(Exp, Exp),
}

fn identity_map<B: BV>(addr: TVal, attrs: &Attrs, ctx: &Ctx<B>) -> Result<(), SetupError> {
    use SetupError::*;
    log!(log::MEMORY, &format!("identity {:?}", addr));

    match addr {
        TVal::VA(va) => {
            ctx.s1_tables.borrow_mut().identity_map(ctx.s2_level0, va.bits(), attrs.stage1()).ok_or(MappingFailure)?;
            ctx.s2_tables.borrow_mut().identity_map(ctx.s2_level0, va.bits(), attrs.stage2()).ok_or(MappingFailure)?;
        }

        TVal::IPA(ipa) => {
            ctx.s2_tables.borrow_mut().identity_map(ctx.s2_level0, ipa.bits(), attrs.stage2()).ok_or(MappingFailure)?;
        }

        TVal::PA(pa) => {
            ctx.s1_tables.borrow_mut().identity_map(ctx.s2_level0, pa, attrs.stage1()).ok_or(MappingFailure)?;
            ctx.s2_tables.borrow_mut().identity_map(ctx.s2_level0, pa, attrs.stage2()).ok_or(MappingFailure)?;
        }

        addr => return Err(Type(format!("Type error creating identity mapping for {:?}: Expected addresses", addr))),
    }

    Ok(())
}

fn maps_to<B: BV>(from: TVal, to: TVal, attrs: &Attrs, ctx: &Ctx<B>) -> Result<(), SetupError> {
    use SetupError::*;
    log!(log::MEMORY, &format!("{:?} |-> {:?}", from, to));

    match (from, to) {
        (TVal::VA(va), TVal::PA(pa)) => {
            ctx.s1_tables.borrow_mut().map(ctx.s1_level0, va, pa, attrs.stage1()).ok_or(MappingFailure)?;
            ctx.s2_tables.borrow_mut().identity_map(ctx.s2_level0, pa, attrs.stage2()).ok_or(MappingFailure)?;
        }

        (TVal::VA(va), TVal::IPA(ipa)) => {
            ctx.s1_tables.borrow_mut().map(ctx.s1_level0, va, ipa.bits(), attrs.stage1()).ok_or(MappingFailure)?;
        }

        (TVal::IPA(ipa), TVal::PA(pa)) => {
            ctx.s2_tables.borrow_mut().map(ctx.s2_level0, ipa, pa, attrs.stage1()).ok_or(MappingFailure)?;
        }

        (TVal::VA(va), TVal::Invalid) => {
            ctx.s1_tables.borrow_mut().invalid(ctx.s1_level0, va).ok_or(MappingFailure)?;
        }

        (TVal::IPA(ipa), TVal::Invalid) => {
            ctx.s2_tables.borrow_mut().invalid(ctx.s2_level0, ipa).ok_or(MappingFailure)?;
        }

        (from, to) => {
            return Err(Type(format!("Type error creating mapping {:?} |-> {:?}: Expected addresses", from, to)))
        }
    }

    Ok(())
}

fn maybe_maps_to<B: BV>(from: TVal, to: TVal, attrs: &Attrs, ctx: &Ctx<B>) -> Result<(), SetupError> {
    use SetupError::*;
    log!(log::MEMORY, &format!("{:?} ?-> {:?}", from, to));

    match (from, to) {
        (TVal::VA(va), TVal::PA(pa)) => {
            ctx.s1_tables.borrow_mut().maybe_map(ctx.s1_level0, va, pa, attrs.stage1()).ok_or(MappingFailure)?;
            ctx.s2_tables.borrow_mut().identity_map(ctx.s2_level0, pa, attrs.stage2()).ok_or(MappingFailure)?;
        }

        (TVal::VA(va), TVal::IPA(ipa)) => {
            ctx.s1_tables
                .borrow_mut()
                .maybe_map(ctx.s1_level0, va, ipa.bits(), attrs.stage1())
                .ok_or(MappingFailure)?;
        }

        (TVal::IPA(ipa), TVal::PA(pa)) => {
            ctx.s2_tables.borrow_mut().maybe_map(ctx.s2_level0, ipa, pa, attrs.stage1()).ok_or(MappingFailure)?;
        }

        (TVal::VA(va), TVal::Invalid) => {
            ctx.s1_tables.borrow_mut().maybe_invalid(ctx.s1_level0, va).ok_or(MappingFailure)?;
        }

        (TVal::IPA(ipa), TVal::Invalid) => {
            ctx.s2_tables.borrow_mut().maybe_invalid(ctx.s2_level0, ipa).ok_or(MappingFailure)?;
        }

        (from, to) => {
            return Err(Type(format!("Type error creating mapping {:?} |-> {:?}: Expected addresses", from, to)))
        }
    }

    Ok(())
}

impl TableConstraint {
    fn eval<B: BV>(&self, ctx: &Ctx<B>) -> Result<(), SetupError> {
        use TableConstraint::*;

        match self {
            IdentityMap(addr_exp, attrs) => {
                let addr = addr_exp.eval(ctx)?;
                identity_map(addr, attrs, ctx)
            }

            MapsTo(from_exp, to_exp, attrs) => {
                let from = from_exp.eval(ctx)?;
                let to = to_exp.eval(ctx)?;
                maps_to(from, to, attrs, ctx)
            }

            MaybeMapsTo(from_exp, to_exp, attrs) => {
                let from = from_exp.eval(ctx)?;
                let to = to_exp.eval(ctx)?;
                maybe_maps_to(from, to, attrs, ctx)
            }
        }
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
    let mut dummy_frame = LocalFrame::new(Name::from_u32(u32::MAX), &[], None, &[]);

    for constraint in constraints {
        if let Constraint::Address(ac) = constraint {
            match ac {
                Virtual(addrs) | Intermediate(addrs) | Physical(addrs) => {
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
                        let alignment = Bvsub(
                            Box::new(Bits64(B64::from_u64(isa_config.symbolic_addr_stride))),
                            Box::new(Bits64(B64::from_u64(1))),
                        );
                        solver.add(Assert(Eq(
                            Box::new(Bvand(Box::new(Var(v)), Box::new(alignment))),
                            Box::new(Bits64(B64::from_u64(0))),
                        )));

                        if matches!(ac, Virtual(_)) {
                            vars.insert(addr.clone(), (v, u64_to_va as fn(u64) -> TVal));
                        } else if matches!(ac, Intermediate(_)) {
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
                    match exp.eval_as_constraint(&vars, &functions, &primops, &mut dummy_frame, &mut solver)? {
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

    if solver.check_sat() != Sat {
        return Err(AddressError("No satisfiable set of addresses".to_string()));
    }

    let mut model = Model::new(&solver);
    for (name, (sym, to_val)) in vars {
        let value = model.get_var(sym).map_err(|err| AddressError(format!("{}", err)))?.unwrap();
        match value {
            Bits64(bv) => {
                table_vars.insert(name.clone(), to_val(bv.lower_u64()));
            }
            _ => {
                return Err(AddressError(format!("Address value {:?} was not a bitvector in satisfiable model", value)))
            }
        }
    }

    Ok(())
}

fn eval_table_constraints<B: BV>(constraints: &[Constraint], ctx: &Ctx<B>) -> Result<Vec<(TVal, TVal)>, SetupError> {
    let mut initials = Vec::new();

    for constraint in constraints {
        match constraint {
            Constraint::Address(_) => (),
            Constraint::Table(tc) => tc.eval(ctx)?,
            Constraint::Initial(addr_exp, exp) => {
                let addr = addr_exp.eval(ctx)?;
                let val = exp.eval(ctx)?;
                initials.push((addr, val))
            }
        }
    }

    Ok(initials)
}

fn eval_initial_constraints<B: BV>(
    constraints: &[(TVal, TVal)],
    s1_level0: L012Index,
    s2_level0: L012Index,
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
    pub physical_addrs: HashMap<String, u64>,
    pub initial_physical_addrs: HashMap<u64, u64>,
}

/// Create page tables in memory from a litmus file
pub fn armv8_litmus_page_tables<B: BV>(
    memory: &mut Memory<B>,
    litmus: &Litmus<B>,
    isa_config: &ISAConfig<B>,
) -> Result<PageTableSetup<B>, SetupError> {
    let vars: HashMap<String, TVal> =
        litmus.symbolic_addrs.iter().map(|(v, addr)| (v.clone(), TVal::VA(VirtualAddress::from_u64(*addr)))).collect();

    armv8_page_tables(memory, vars, litmus.assembled.len(), &litmus.page_table_setup, isa_config)
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

    // Create page tables for both stage 1 and stage 2 address translation
    let mut s1_tables = PageTables::new("stage 1", isa_config.page_table_base);
    let mut s2_tables = PageTables::new("stage 2", isa_config.s2_page_table_base);

    let s1_level0 = s1_tables.alloc();
    let s2_level0 = s2_tables.alloc();

    // We map each thread's code into both levels of page tables
    for i in 0..num_threads {
        let addr = isa_config.thread_base + (i as u64 * isa_config.page_size);
        s1_tables.identity_map(s1_level0, addr, S1PageAttrs::code()).unwrap();
        s2_tables.identity_map(s2_level0, addr, S2PageAttrs::code()).unwrap()
    }

    vars.insert("invalid".to_string(), TVal::Invalid);
    eval_address_constraints::<B>(page_table_setup, &mut vars, isa_config)?;

    let ctx = Ctx {
        vars,
        s1_tables: RefCell::new(&mut s1_tables),
        s2_tables: RefCell::new(&mut s2_tables),
        s1_level0,
        s2_level0,
    };

    let initial_constraints = eval_table_constraints(page_table_setup, &ctx)?;

    let mut addrs: HashMap<String, TVal> = ctx.vars;

    // Map the stage 2 tables into the stage 2 mapping
    let mut page = isa_config.s2_page_table_base;
    while page < s2_tables.range().end {
        s2_tables.identity_map(s2_level0, page, S2PageAttrs::default());
        page += isa_config.s2_page_size
    }

    // Map the stage 1 tables into the stage 1 and stage 2 mappings
    page = isa_config.page_table_base;
    while page < s1_tables.range().end {
        s1_tables.identity_map(s1_level0, page, S1PageAttrs::default());
        s2_tables.identity_map(s2_level0, page, S2PageAttrs::default());
        page += isa_config.page_size
    }

    memory.add_region(Region::Custom(s1_tables.range(), Box::new(s1_tables.freeze())));
    memory.add_region(Region::Custom(s2_tables.range(), Box::new(s2_tables.freeze())));

    let initial_physical_addrs =
        eval_initial_constraints(&initial_constraints, s1_level0, s2_level0, memory, &mut solver)?;

    let physical_addrs: HashMap<String, u64> = addrs
        .drain()
        .filter(|(_, v)| v.is_address())
        .map(|(name, v)| (name, v.translate(s1_level0, s2_level0, memory, &mut solver).unwrap_or(0)))
        .collect();

    Ok(PageTableSetup { memory_checkpoint: checkpoint(&mut solver), physical_addrs, initial_physical_addrs })
}
