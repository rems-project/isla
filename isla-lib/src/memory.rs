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

//! The memory is split up into various regions defined by a half-open
//! range between two addresses [base, top). This is done because we
//! want to give different semantics to various parts of memory,
//! e.g. program memory should be concrete, whereas the memory used
//! for loads and stores in litmus tests need to be totally symbolic
//! so the bevhaior can be imposed later as part of the concurrency
//! model.

use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use std::ops::Range;
use std::sync::Arc;

use crate::bitvector::BV;
use crate::error::ExecError;
use crate::ir;
use crate::ir::Val;
use crate::log;
use crate::probe;
use crate::smt::smtlib::{bits64, Def, Exp};
use crate::smt::{Event, Model, ModelVal, ReadOpts, SmtResult, Solver, Sym, WriteOpts};
use crate::source_loc::SourceLoc;

/// For now, we assume that we only deal with 64-bit architectures.
pub type Address = u64;

pub trait CustomRegion<B> {
    fn read(
        &self,
        read_kind: Val<B>,
        address: Address,
        bytes: u32,
        solver: &mut Solver<B>,
        tag: bool,
    ) -> Result<Val<B>, ExecError>;

    fn write(
        &mut self,
        write_kind: Val<B>,
        address: Address,
        data: Val<B>,
        solver: &mut Solver<B>,
        tag: Option<Val<B>>,
    ) -> Result<Val<B>, ExecError>;

    fn initial_value(&self, address: Address, bytes: u32) -> Option<B>;

    /// Return a static string denoting the 'kind' or 'name' of memory
    /// this custom region is representing, e.g. "device" or
    /// "page_table". This information is only used for display
    /// purposes, and has no semantic meaning.
    fn region_name(&self) -> &'static str;

    /// Trait objects (`dyn T`) are in general not cloneable, so we
    /// require a method that allows us to implement clone ourselves
    /// for types containing `Box<dyn T>`. The implementation will
    /// nearly always be just `Box::new(self.clone())`.
    fn clone_dyn(&self) -> Box<dyn Send + Sync + CustomRegion<B>>;
}

pub enum Region<B> {
    /// A region with a symbolic value constrained by a symbolic
    /// variable generated by an arbitrary function. The region should
    /// return a bitvector variable representing the whole region, so
    /// in practice this should be used for small regions of memory.
    Constrained(Range<Address>, Arc<dyn Send + Sync + Fn(&mut Solver<B>) -> Sym>),
    /// A region of arbitrary symbolic locations
    Symbolic(Range<Address>),
    /// A read only region of arbitrary symbolic locations intended for code
    SymbolicCode(Range<Address>),
    /// A region of concrete read-only memory
    Concrete(Range<Address>, HashMap<Address, u8>),
    /// A custom region
    Custom(Range<Address>, Box<dyn Send + Sync + CustomRegion<B>>),
}

impl<B> Clone for Region<B> {
    fn clone(&self) -> Self {
        use Region::*;
        match self {
            Constrained(r, contents) => Constrained(r.clone(), contents.clone()),
            Symbolic(r) => Symbolic(r.clone()),
            SymbolicCode(r) => SymbolicCode(r.clone()),
            Concrete(r, contents) => Concrete(r.clone(), contents.clone()),
            Custom(r, contents) => Custom(r.clone(), contents.clone_dyn()),
        }
    }
}

pub enum SmtKind {
    ReadData,
    ReadInstr,
    WriteData,
}

impl<B> fmt::Debug for Region<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Region::*;
        match self {
            Constrained(r, _) => write!(f, "Constrained({:?}, <closure>)", r),
            Symbolic(r) => write!(f, "Symbolic({:?})", r),
            SymbolicCode(r) => write!(f, "SymbolicCode({:?})", r),
            Concrete(r, locs) => write!(f, "Concrete({:?}, {:?})", r, locs),
            Custom(r, _) => write!(f, "Custom({:?}, <trait object>)", r),
        }
    }
}

impl<B> Region<B> {
    fn region_name(&self) -> &'static str {
        match self {
            Region::Constrained(_, _) => "constrained",
            Region::Symbolic(_) => "symbolic",
            Region::SymbolicCode(_) => "symbolic code",
            Region::Concrete(_, _) => "concrete",
            Region::Custom(_, contents) => contents.region_name(),
        }
    }

    pub fn region_range(&self) -> &Range<Address> {
        match self {
            Region::Constrained(r, _) => r,
            Region::Symbolic(r) => r,
            Region::SymbolicCode(r) => r,
            Region::Concrete(r, _) => r,
            Region::Custom(r, _) => r,
        }
    }
}

// Optional client interface.  At the time of writing this is only
// used by the test generation to enforce sequential memory, so we
// jump through a few hoops to avoid other clients seeing it.  If it
// was used more generally then it would be better to parametrise the
// Memory struct instead.

pub trait MemoryCallbacks<B>: fmt::Debug + MemoryCallbacksClone<B> + Send + Sync {
    #[allow(clippy::too_many_arguments)]
    fn symbolic_read(
        &self,
        regions: &[Region<B>],
        solver: &mut Solver<B>,
        value: &Val<B>,
        read_kind: &Val<B>,
        address: &Val<B>,
        bytes: u32,
        tag: &Option<Val<B>>,
        opts: &ReadOpts,
    );
    #[allow(clippy::too_many_arguments)]
    fn symbolic_write(
        &mut self,
        regions: &[Region<B>],
        solver: &mut Solver<B>,
        value: Sym,
        write_kind: &Val<B>,
        address: &Val<B>,
        data: &Val<B>,
        bytes: u32,
        tag: &Option<Val<B>>,
        opts: &WriteOpts,
    );
    fn symbolic_write_tag(
        &mut self,
        regions: &[Region<B>],
        solver: &mut Solver<B>,
        value: Sym,
        write_kind: &Val<B>,
        address: &Val<B>,
        tag: &Val<B>,
    );
}

pub trait MemoryCallbacksClone<B> {
    fn clone_box(&self) -> Box<dyn MemoryCallbacks<B>>;
}

impl<B, T> MemoryCallbacksClone<B> for T
where
    T: 'static + MemoryCallbacks<B> + Clone,
{
    fn clone_box(&self) -> Box<dyn MemoryCallbacks<B>> {
        Box::new(self.clone())
    }
}

impl<B> Clone for Box<dyn MemoryCallbacks<B>> {
    fn clone(&self) -> Box<dyn MemoryCallbacks<B>> {
        self.clone_box()
    }
}

fn make_bv_bit_pair<B>(left: Val<B>, right: Val<B>) -> Val<B> {
    let mut fields = HashMap::default();
    fields.insert(ir::BV_BIT_LEFT, left);
    fields.insert(ir::BV_BIT_RIGHT, right);
    Val::Struct(fields)
}

#[derive(Clone, Debug, Default)]
pub struct Memory<B> {
    regions: Vec<Region<B>>,
    client_info: Option<Box<dyn MemoryCallbacks<B>>>,
}

static DEFAULT_REGION_NAME: &str = "default";

enum Overlap {
    Unique(u64),
    NoOverlap,
}

impl<B: BV> Memory<B> {
    pub fn new() -> Self {
        Memory { regions: Vec::new(), client_info: None }
    }

    pub fn regions(&self) -> &[Region<B>] {
        &self.regions
    }

    pub fn region_name_at(&self, addr: Address) -> &'static str {
        for region in &self.regions {
            if region.region_range().contains(&addr) {
                return region.region_name();
            }
        }
        DEFAULT_REGION_NAME
    }

    pub fn log(&self) {
        for region in &self.regions {
            match region {
                Region::Constrained(range, _) => {
                    log!(log::MEMORY, &format!("Memory range: [0x{:x}, 0x{:x}) constrained", range.start, range.end))
                }
                Region::Symbolic(range) => {
                    log!(log::MEMORY, &format!("Memory range: [0x{:x}, 0x{:x}) symbolic", range.start, range.end))
                }
                Region::SymbolicCode(range) => {
                    log!(log::MEMORY, &format!("Memory range: [0x{:x}, 0x{:x}) symbolic code", range.start, range.end))
                }
                Region::Concrete(range, _) => {
                    log!(log::MEMORY, &format!("Memory range: [0x{:x}, 0x{:x}) concrete", range.start, range.end))
                }
                Region::Custom(range, contents) => log!(
                    log::MEMORY,
                    &format!(
                        "Memory range: [0x{:x}, 0x{:x}) custom {}",
                        range.start,
                        range.end,
                        contents.region_name()
                    )
                ),
            }
        }
    }

    pub fn in_custom_region(&self, addr: Address) -> Option<&dyn CustomRegion<B>> {
        for region in &self.regions {
            match region {
                Region::Custom(range, mem) if range.contains(&addr) => return Some(mem.as_ref()),
                _ => (),
            }
        }
        None
    }

    pub fn add_region(&mut self, region: Region<B>) {
        self.regions.push(region)
    }

    pub fn add_symbolic_region(&mut self, range: Range<Address>) {
        self.regions.push(Region::Symbolic(range))
    }

    pub fn add_symbolic_code_region(&mut self, range: Range<Address>) {
        self.regions.push(Region::SymbolicCode(range))
    }

    pub fn add_concrete_region(&mut self, range: Range<Address>, contents: HashMap<Address, u8>) {
        self.regions.push(Region::Concrete(range, contents))
    }

    pub fn add_zero_region(&mut self, range: Range<Address>) {
        self.regions.push(Region::Concrete(range, HashMap::new()))
    }

    pub fn set_client_info(&mut self, info: Box<dyn MemoryCallbacks<B>>) {
        self.client_info = Some(info);
    }

    pub fn write_byte(&mut self, address: Address, byte: u8) {
        for region in &mut self.regions {
            match region {
                Region::Concrete(range, contents) if range.contains(&address) => {
                    contents.insert(address, byte);
                    return;
                }
                _ => (),
            }
        }
        self.regions.push(Region::Concrete(address..address, vec![(address, byte)].into_iter().collect()))
    }

    fn read_initial_byte(&self, address: Address) -> Result<u8, ExecError> {
        use Region::*;
        for region in &self.regions {
            match region {
                Constrained(range, _) | Symbolic(range) | SymbolicCode(range) if range.contains(&address) => {
                    return Err(ExecError::BadRead("Symbolic initial byte"))
                }
                Concrete(range, contents) if range.contains(&address) => {
                    return Ok(contents.get(&address).copied().unwrap_or(0))
                }
                Custom(range, contents) if range.contains(&address) => {
                    return contents
                        .initial_value(address, 1)
                        .map(B::lower_u8)
                        .ok_or(ExecError::BadRead("Read of initial byte from custom region failed"))
                }
                _ => (),
            }
        }
        Err(ExecError::BadRead("Symbolic initial byte (no region)"))
    }

    pub fn read_initial(&self, address: Address, bytes: u32) -> Result<Val<B>, ExecError> {
        let mut byte_vec: Vec<u8> = Vec::with_capacity(bytes as usize);
        for i in address..(address + u64::from(bytes)) {
            byte_vec.push(self.read_initial_byte(i)?)
        }

        reverse_endianness(&mut byte_vec);

        if byte_vec.len() <= 8 {
            Ok(Val::Bits(B::from_bytes(&byte_vec)))
        } else {
            Err(ExecError::BadRead("Initial read greater than 8 bytes"))
        }
    }

    // Checks that a symbolic address does not overlap with any
    // concrete regions of memory. If it does, then we won't know what
    // value should be returned.
    fn check_concrete_overlap(
        &self,
        address: Sym,
        error: ExecError,
        solver: &mut Solver<B>,
    ) -> Result<Overlap, ExecError> {
        use Exp::*;
        use SmtResult::*;

        let mut region_constraints = Vec::new();

        let addr_size = solver.length(address).unwrap_or_else(|| panic!("address is not a bitvector"));

        for region in &self.regions {
            if !matches!(region, Region::Symbolic(_) | Region::SymbolicCode(_)) {
                let Range { start, end } = region.region_range();

                region_constraints.push(And(
                    Box::new(Bvule(Box::new(bits64(*start, addr_size)), Box::new(Var(address)))),
                    Box::new(Bvult(Box::new(Var(address)), Box::new(bits64(*end, addr_size)))),
                ))
            }
        }

        if let Some(r) = region_constraints.pop() {
            let constraint = region_constraints.drain(..).fold(r, |r1, r2| Or(Box::new(r1), Box::new(r2)));
            match solver.check_sat_with(&constraint, SourceLoc::unknown()) {
                Sat => {
                    let sat_address = {
                        let mut model = Model::new(solver);
                        let ModelVal::Exp(Bits64(sat_address)) = model.get_var(address)? else {
                            return Err(ExecError::Z3Error(
                                "No bitvector address variable found in model during check_concrete_overlap"
                                    .to_string(),
                            ));
                        };
                        sat_address
                    };
                    // Check if the satisifiable address in the
                    // concrete region is actually unique, in which
                    // case the caller could choose to treat it as a
                    // concrete value.
                    let uniqueness_constraint = Neq(Box::new(Var(address)), Box::new(Bits64(sat_address)));
                    match solver.check_sat_with(&uniqueness_constraint, SourceLoc::unknown()) {
                        Unsat => Ok(Overlap::Unique(sat_address.lower_u64())),
                        Unknown => Err(ExecError::Z3Unknown),
                        Sat => {
                            log!(log::MEMORY, &format!("Overlapping satisfiable address: {:x}", sat_address));
                            probe::taint_info(log::MEMORY, address, None, solver);
                            Err(error)
                        }
                    }
                }
                Unknown => Err(ExecError::Z3Unknown),
                Unsat => Ok(Overlap::NoOverlap),
            }
        } else {
            // There are no concrete regions
            Ok(Overlap::NoOverlap)
        }
    }

    /// Read from the memory region determined by the address. If the address is symbolic the read
    /// value is always also symbolic. The number of bytes must be concrete otherwise will return a
    /// SymbolicLength error.
    ///
    /// # Panics
    ///
    /// Panics if the number of bytes to read is concrete but does not fit
    /// in a u32, which should never be the case.
    pub fn read(
        &self,
        read_kind: Val<B>,
        address: Val<B>,
        bytes: Val<B>,
        solver: &mut Solver<B>,
        tag: bool,
        opts: ReadOpts,
    ) -> Result<Val<B>, ExecError> {
        log!(log::MEMORY, &format!("Read: {:?} {:?} {:?} {:?}", read_kind, address, bytes, tag));

        if let Val::I128(bytes) = bytes.widen_int() {
            let bytes = u32::try_from(bytes).expect("Bytes did not fit in u32 in memory read");

            match address {
                Val::Bits(concrete_addr) => {
                    for region in &self.regions {
                        match region {
                            Region::Constrained(range, generator) if range.contains(&concrete_addr.lower_u64()) => {
                                return read_constrained(
                                    range,
                                    generator.as_ref(),
                                    read_kind,
                                    concrete_addr.lower_u64(),
                                    bytes,
                                    solver,
                                    tag,
                                    opts,
                                    region.region_name(),
                                )
                            }

                            Region::Symbolic(range) if range.contains(&concrete_addr.lower_u64()) => {
                                return self.read_symbolic(
                                    read_kind,
                                    address,
                                    bytes,
                                    solver,
                                    tag,
                                    opts,
                                    region.region_name(),
                                )
                            }

                            Region::SymbolicCode(range) if range.contains(&concrete_addr.lower_u64()) => {
                                return self.read_symbolic(
                                    read_kind,
                                    address,
                                    bytes,
                                    solver,
                                    tag,
                                    opts,
                                    region.region_name(),
                                )
                            }

                            Region::Concrete(range, contents) if range.contains(&concrete_addr.lower_u64()) => {
                                return read_concrete(
                                    contents,
                                    read_kind,
                                    concrete_addr.lower_u64(),
                                    bytes,
                                    solver,
                                    tag,
                                    opts,
                                    region.region_name(),
                                )
                            }

                            Region::Custom(range, contents) if range.contains(&concrete_addr.lower_u64()) => {
                                return contents.read(read_kind, concrete_addr.lower_u64(), bytes, solver, tag)
                            }

                            _ => continue,
                        }
                    }

                    if opts.is_ifetch {
                        Err(ExecError::BadRead("Attempted to fetch instruction from default memory"))
                    } else {
                        self.read_symbolic(read_kind, address, bytes, solver, tag, opts, DEFAULT_REGION_NAME)
                    }
                }

                Val::Symbolic(symbolic_addr) => {
                    // If the symbolic address overlaps a concrete
                    // region, but actually only has a single unique
                    // satisfiable value, then we can recursively call
                    // read again with that satisfiable value.
                    match self.check_concrete_overlap(
                        symbolic_addr,
                        ExecError::BadRead("Possible symbolic address overlap"),
                        solver,
                    )? {
                        Overlap::Unique(concrete_addr) => self.read(
                            read_kind,
                            Val::Bits(B::new(concrete_addr, 64)),
                            Val::I128(bytes as i128),
                            solver,
                            tag,
                            opts,
                        ),
                        Overlap::NoOverlap => {
                            self.read_symbolic(read_kind, address, bytes, solver, tag, opts, DEFAULT_REGION_NAME)
                        }
                    }
                }

                _ => Err(ExecError::Type("Non bitvector address in read".to_string(), SourceLoc::unknown())),
            }
        } else {
            Err(ExecError::SymbolicLength("read_symbolic", SourceLoc::unknown()))
        }
    }

    pub fn write(
        &mut self,
        write_kind: Val<B>,
        address: Val<B>,
        data: Val<B>,
        solver: &mut Solver<B>,
        tag: Option<Val<B>>,
        opts: WriteOpts,
    ) -> Result<Val<B>, ExecError> {
        log!(log::MEMORY, &format!("Write: {:?} {:?} {:?} {:?}", write_kind, address, data, tag));

        match address {
            Val::Bits(concrete_addr) => {
                for region in self.regions.iter_mut() {
                    match region {
                        Region::Custom(range, contents) if range.contains(&concrete_addr.lower_u64()) => {
                            return contents.write(write_kind, concrete_addr.lower_u64(), data, solver, tag)
                        }

                        _ => continue,
                    }
                }

                self.write_symbolic(write_kind, address, data, solver, tag, opts, DEFAULT_REGION_NAME)
            }

            Val::Symbolic(symbolic_addr) => {
                self.check_concrete_overlap(
                    symbolic_addr,
                    ExecError::BadWrite("possible symbolic address overlap"),
                    solver,
                )?;
                self.write_symbolic(write_kind, address, data, solver, tag, opts, DEFAULT_REGION_NAME)
            }

            _ => Err(ExecError::Type("Non bitvector address in write".to_string(), SourceLoc::unknown())),
        }
    }

    pub fn write_tag(
        &mut self,
        write_kind: Val<B>,
        address: Val<B>,
        tag: Val<B>,
        solver: &mut Solver<B>,
    ) -> Result<Val<B>, ExecError> {
        log!(log::MEMORY, &format!("Write tag: {:?} {:?} {:?}", write_kind, address, tag));

        self.write_symbolic_tag(write_kind, address, tag, solver)
    }

    /// The simplest read is to symbolically read a memory location. In
    /// that case we just return a fresh SMT bitvector of the appropriate
    /// size, and add a ReadMem event to the trace. For this we need the
    /// number of bytes to be non-symbolic.
    fn read_symbolic(
        &self,
        read_kind: Val<B>,
        address: Val<B>,
        bytes: u32,
        solver: &mut Solver<B>,
        tag: bool,
        opts: ReadOpts,
        region: &'static str,
    ) -> Result<Val<B>, ExecError> {
        use crate::smt::smtlib::*;

        let value = solver.fresh();
        solver.add(Def::DeclareConst(value, Ty::BitVec(8 * bytes)));

        let tag_value = if tag {
            let v = solver.fresh();
            solver.add(Def::DeclareConst(v, Ty::BitVec(1)));
            Some(v)
        } else {
            None
        };
        let tag_ir_value = tag_value.map(Val::Symbolic);
        if let Some(c) = &self.client_info {
            c.symbolic_read(
                &self.regions,
                solver,
                &Val::Symbolic(value),
                &read_kind,
                &address,
                bytes,
                &tag_ir_value,
                &opts,
            )
        };
        solver.add_event(Event::ReadMem {
            value: Val::Symbolic(value),
            read_kind,
            address,
            bytes,
            tag_value: tag_ir_value.clone(),
            opts,
            region,
        });

        log!(log::MEMORY, &format!("Read symbolic: {} {:?}", value, tag_value));

        let return_value = match tag_ir_value {
            Some(v) => make_bv_bit_pair(Val::Symbolic(value), v),
            None => Val::Symbolic(value),
        };
        Ok(return_value)
    }

    /// `write_symbolic` just adds a WriteMem event to the trace,
    /// returning a symbolic boolean (the semantics of which is controlled
    /// by a memory model if required, but can be ignored in
    /// others). Raises a type error if the data argument is not a
    /// bitvector with a length that is a multiple of 8. This should be
    /// guaranteed by the Sail type system.
    fn write_symbolic(
        &mut self,
        write_kind: Val<B>,
        address: Val<B>,
        data: Val<B>,
        solver: &mut Solver<B>,
        tag: Option<Val<B>>,
        opts: WriteOpts,
        region: &'static str,
    ) -> Result<Val<B>, ExecError> {
        use crate::smt::smtlib::*;

        let data_length = crate::primop_util::length_bits(&data, solver, SourceLoc::unknown())?;
        if data_length % 8 != 0 {
            return Err(ExecError::Type(format!("write_symbolic {:?}", &data_length), SourceLoc::unknown()));
        };
        let bytes = data_length / 8;

        let value = solver.fresh();
        solver.add(Def::DeclareConst(value, Ty::Bool));
        if let Some(c) = &mut self.client_info {
            c.symbolic_write(&self.regions, solver, value, &write_kind, &address, &data, bytes, &tag, &opts)
        };
        solver.add_event(Event::WriteMem { value, write_kind, address, data, bytes, tag_value: tag, opts, region });

        Ok(Val::Symbolic(value))
    }

    fn write_symbolic_tag(
        &mut self,
        write_kind: Val<B>,
        address: Val<B>,
        tag: Val<B>,
        solver: &mut Solver<B>,
    ) -> Result<Val<B>, ExecError> {
        use crate::smt::smtlib::*;

        let value = solver.fresh();
        solver.add(Def::DeclareConst(value, Ty::Bool));
        if let Some(c) = &mut self.client_info {
            c.symbolic_write_tag(&self.regions, solver, value, &write_kind, &address, &tag)
        };
        solver.add_event(Event::WriteMem {
            value,
            write_kind,
            address,
            data: Val::Bits(B::zero_width()),
            bytes: 0,
            tag_value: Some(tag),
            opts: WriteOpts::default(),
            region: DEFAULT_REGION_NAME,
        });

        Ok(Val::Symbolic(value))
    }

    pub fn smt_address_constraint(
        &self,
        address: &Exp<Sym>,
        bytes: u32,
        kind: SmtKind,
        solver: &mut Solver<B>,
        tag: Option<&Exp<Sym>>,
    ) -> Exp<Sym> {
        smt_address_constraint(&self.regions, address, bytes, kind, solver, tag)
    }

    // Perform a concrete version of the address constraint
    pub fn access_check(&self, address: Address, bytes: u32, kind: SmtKind) -> bool {
        access_check(&self.regions, address, bytes, kind)
    }
}

fn ranges_for_access_checks<B: BV>(
    regions: &[Region<B>],
    bytes: u32,
    kind: SmtKind,
) -> impl Iterator<Item = (&Range<Address>, bool)> {
    regions
        .iter()
        .filter(move |r| match kind {
            SmtKind::ReadData => true,
            SmtKind::ReadInstr => matches!(r, Region::SymbolicCode(_)),
            SmtKind::WriteData => matches!(r, Region::Symbolic(_)),
        })
        .map(|r| (r.region_range(), matches!(r, Region::Symbolic(_))))
        .filter(move |(r, _k)| r.end - r.start >= bytes as u64)
}

pub fn access_check<B: BV>(regions: &[Region<B>], address: Address, bytes: u32, kind: SmtKind) -> bool {
    ranges_for_access_checks(regions, bytes, kind).any(|(r, _k)| r.start <= address && address <= r.end - bytes as u64)
}

pub fn smt_address_constraint<B: BV>(
    regions: &[Region<B>],
    address: &Exp<Sym>,
    bytes: u32,
    kind: SmtKind,
    solver: &mut Solver<B>,
    tag: Option<&Exp<Sym>>,
) -> Exp<Sym> {
    use crate::smt::smtlib::Exp::*;
    let addr_var = match address {
        Var(v) => *v,
        _ => {
            let v = solver.fresh();
            solver.add(Def::DefineConst(v, address.clone()));
            v
        }
    };
    let addr_size = solver.length(addr_var).unwrap_or_else(|| panic!("address is not a bitvector"));
    ranges_for_access_checks(regions, bytes, kind)
        .map(|(r, k)| {
            let in_range = And(
                Box::new(Bvule(Box::new(bits64(r.start, addr_size)), Box::new(Var(addr_var)))),
                // Use an extra bit to prevent wrapping
                Box::new(Bvult(
                    Box::new(Bvadd(
                        Box::new(ZeroExtend(1, Box::new(Var(addr_var)))),
                        Box::new(ZeroExtend(1, Box::new(bits64(bytes as u64, addr_size)))),
                    )),
                    Box::new(ZeroExtend(1, Box::new(bits64(r.end, addr_size)))),
                )),
            );
            // If we're not in a normal Symbolic region tags must be clear
            if let (false, Some(tag)) = (k, tag) {
                And(Box::new(in_range), Box::new(Eq(Box::new(tag.clone()), Box::new(bits64(0, 1)))))
            } else {
                in_range
            }
        })
        .fold(Bool(false), |acc, e| match acc {
            Bool(false) => e,
            _ => Or(Box::new(acc), Box::new(e)),
        })
}

fn reverse_endianness(bytes: &mut [u8]) {
    if bytes.len() <= 2 {
        bytes.reverse()
    } else {
        let (bytes_upper, bytes_lower) = bytes.split_at_mut(bytes.len() / 2);
        reverse_endianness(bytes_upper);
        reverse_endianness(bytes_lower);
        bytes.rotate_left(bytes.len() / 2)
    }
}

#[allow(clippy::too_many_arguments)]
fn read_constrained<B: BV>(
    range: &Range<Address>,
    generator: &(dyn Fn(&mut Solver<B>) -> Sym),
    read_kind: Val<B>,
    address: Address,
    bytes: u32,
    solver: &mut Solver<B>,
    tag: bool,
    opts: ReadOpts,
    region: &'static str,
) -> Result<Val<B>, ExecError> {
    let constrained = generator(solver);
    if address == range.start && address + bytes as u64 == range.end {
        solver.add_event(Event::ReadMem {
            value: Val::Symbolic(constrained),
            read_kind,
            address: Val::Bits(B::from_u64(address)),
            bytes,
            tag_value: None,
            opts,
            region,
        });
        if tag {
            Ok(make_bv_bit_pair(Val::Symbolic(constrained), Val::Bits(B::zeros(1))))
        } else {
            Ok(Val::Symbolic(constrained))
        }
    } else {
        Err(ExecError::BadRead("Constrained read address is not within bounds"))
    }
}

fn read_concrete<B: BV>(
    memory: &HashMap<Address, u8>,
    read_kind: Val<B>,
    address: Address,
    bytes: u32,
    solver: &mut Solver<B>,
    tag: bool,
    opts: ReadOpts,
    region: &'static str,
) -> Result<Val<B>, ExecError> {
    let mut byte_vec: Vec<u8> = Vec::with_capacity(bytes as usize);
    for i in address..(address + u64::from(bytes)) {
        byte_vec.push(*memory.get(&i).unwrap_or(&0))
    }

    reverse_endianness(&mut byte_vec);

    if byte_vec.len() <= 8 {
        log!(log::MEMORY, &format!("Read concrete: {:?}", byte_vec));

        let value = Val::Bits(B::from_bytes(&byte_vec));
        solver.add_event(Event::ReadMem {
            value,
            read_kind,
            address: Val::Bits(B::from_u64(address)),
            bytes,
            tag_value: None,
            opts,
            region,
        });
        if tag {
            Ok(make_bv_bit_pair(Val::Bits(B::from_bytes(&byte_vec)), Val::Bits(B::zeros(1))))
        } else {
            Ok(Val::Bits(B::from_bytes(&byte_vec)))
        }
    } else {
        // TODO: Handle reads > 64 bits
        Err(ExecError::BadRead("Concrete read more than 8 bytes"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::error::ExecError;
    use crate::smt::smtlib::{bits64, Def, Exp, Ty};
    use crate::smt::{Config, Context, Solver, Sym};

    #[test]
    fn test_symbolic_overlap() {
        let mut mem = Memory::<B64>::new();
        mem.add_zero_region(0x00..0xFF);

        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        let addr = Sym::from_u32(0);
        solver.add(Def::DeclareConst(addr, Ty::BitVec(64)));
        solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0xA0, 64)))));

        match mem.check_concrete_overlap(addr, ExecError::BadRead("test"), &mut solver) {
            Ok(Overlap::Unique(0xA0)) => (),
            _ => panic!("Unexpected result from check_concrete_overlap"),
        }
    }
}
