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

use std::collections::HashMap;
use std::convert::{From, Into};
use std::fmt;
use std::ops::Range;
use std::sync::Arc;

use isla_lib::bitvector::{bzhi_u64, BV};
use isla_lib::error::ExecError;
use isla_lib::ir::Val;
use isla_lib::log;
use isla_lib::memory::{CustomRegion, Memory};
use isla_lib::primop_util::{length_bits, smt_sbits};
use isla_lib::smt::{
    smtlib::{bits64, Exp, Ty},
    Event, ReadOpts, SmtResult, Solver, Sym, WriteOpts,
};
use isla_lib::source_loc::SourceLoc;

pub mod setup;
pub mod setup_lexer;
lalrpop_mod!(
    #[allow(clippy::all)]
    pub setup_parser,
    "/page_table/setup_parser.rs"
);

#[derive(Debug, Clone)]
pub struct S1PageAttrs {
    uxn: Option<bool>, // UXN in EL1&0 translation regime, XN in others
    pxn: Option<bool>,
    contiguous: Option<bool>,
    n_g: Option<bool>,
    af: Option<bool>,
    sh: Option<u8>,
    ap: Option<u8>,
    ns: Option<bool>,
    attr_indx: Option<u8>,
}

// Names identical to ARM ARM
const S1_PAGE_ATTR_FIELDS: [(&str, u64, u64); 9] = [
    ("UXN", 54, 54),
    ("PXN", 53, 53),
    ("Contiguous", 52, 52),
    ("nG", 11, 11),
    ("AF", 10, 10),
    ("SH", 9, 8),
    ("AP", 7, 6),
    ("NS", 5, 5),
    ("AttrIndx", 4, 2),
];

impl Default for S1PageAttrs {
    fn default() -> Self {
        S1PageAttrs {
            uxn: Some(false),
            pxn: Some(false),
            contiguous: Some(false),
            n_g: Some(false),
            af: Some(true),
            sh: Some(0b00),
            ap: Some(0b01),
            ns: Some(false),
            attr_indx: Some(0b000),
        }
    }
}

impl S1PageAttrs {
    pub fn code() -> Self {
        S1PageAttrs {
            uxn: Some(false),
            pxn: Some(false),
            contiguous: Some(false),
            n_g: Some(false),
            af: Some(true),
            sh: Some(0b00),
            ap: Some(0b11),
            ns: Some(false),
            attr_indx: Some(0b000),
        }
    }
}

#[derive(Debug, Clone)]
pub struct S2PageAttrs {
    xn: Option<bool>,
    contiguous: Option<bool>,
    af: Option<bool>,
    sh: Option<u8>,
    s2ap: Option<u8>,
    mem_attr: Option<u8>,
}

// Names identical to ARM ARM
const S2_PAGE_ATTR_FIELDS: [(&str, u64, u64); 6] =
    [("XN", 54, 54), ("Contiguous", 52, 52), ("AF", 10, 10), ("SH", 9, 8), ("S2AP", 7, 6), ("MemAttr", 5, 2)];

impl Default for S2PageAttrs {
    fn default() -> Self {
        S2PageAttrs {
            xn: Some(false),
            contiguous: Some(false),
            af: Some(true),
            sh: Some(0b00),
            s2ap: Some(0b11),
            // normal/normal write-through read/write-allocate non-transient memory
            mem_attr: Some(0b1111),
        }
    }
}

impl S2PageAttrs {
    pub fn code() -> Self {
        S2PageAttrs {
            xn: Some(false),
            contiguous: Some(false),
            af: Some(true),
            sh: Some(0b00),
            s2ap: Some(0b00),
            // normal/normal write-through read/write-allocate non-transient memory
            mem_attr: Some(0b1111),
        }
    }
}

fn bool_to_bit<V>(b: bool) -> Exp<V> {
    bits64(if b { 1 } else { 0 }, 1)
}

pub trait PageAttrs: Clone {
    /// Return a set of page attributes with all bits unknown
    fn unknown() -> Self;

    /// Return a list of the page attributes, each of which has a name
    /// and then a position as a high-bit and low-bit pair
    /// (inclusive). For example, in ARM stage 2 attributes we have
    /// `("S2AP", 7, 6)` which is a 2-bit field.
    fn fields() -> &'static [(&'static str, u64, u64)];

    /// Returns a representation of the page attribute as two 64-bit
    /// words. The first u64 contains a 1 or 0 for each bit set or
    /// unset in the page attributes. The second u64 contains a bit
    /// that is set to 1 for each unknown bit in the page attributes
    ///
    /// i.e. if this returns `(s, u)`, then the page attributes can be
    /// any bitvector `a` such that `a & ~u == s & ~u`.
    fn bits(&self) -> (u64, u64);

    fn set<B: BV>(&self, desc: Sym, solver: &mut Solver<B>);

    fn set_field<B: BV>(&mut self, attr: &str, bits: B) -> Option<()>;
}

macro_rules! attr_bool {
    ($field: expr, $n: expr, $set: ident, $unknown: ident) => {
        if let Some(bit) = $field {
            $set |= u64::from(bit) << $n
        } else {
            $unknown |= 1 << $n
        }
    };
}

macro_rules! attr_u8 {
    ($field: expr, $hi: expr, $lo: expr, $set: ident, $unknown: ident) => {
        if let Some(bits) = $field {
            $set |= bzhi_u64(bits as u64, ($hi - $lo) + 1) << $lo
        } else {
            $unknown |= bzhi_u64(u64::MAX, ($hi - $lo) + 1) << $lo
        }
    }
}

impl PageAttrs for S1PageAttrs {
    fn unknown() -> Self {
        S1PageAttrs {
            uxn: None,
            pxn: None,
            contiguous: None,
            n_g: None,
            af: None,
            sh: None,
            ap: None,
            ns: None,
            attr_indx: None,
        }
    }

    fn fields() -> &'static [(&'static str, u64, u64)] {
        &S1_PAGE_ATTR_FIELDS
    }

    fn bits(&self) -> (u64, u64) {
        let mut set = 0;
        let mut unknown = 0;

        attr_bool!(self.uxn, 53, set, unknown);
        attr_bool!(self.pxn, 54, set, unknown);
        attr_bool!(self.contiguous, 52, set, unknown);
        attr_bool!(self.n_g, 11, set, unknown);
        attr_bool!(self.af, 10, set, unknown);
        attr_u8!(self.sh, 9, 8, set, unknown);
        attr_u8!(self.ap, 7, 6, set, unknown);
        attr_bool!(self.ns, 5, set, unknown);
        attr_u8!(self.attr_indx, 4, 2, set, unknown);

        (set, unknown)
    }

    fn set<B: BV>(&self, desc: Sym, solver: &mut Solver<B>) {
        use Exp::*;

        // Bit 54 is UXN (Unprivileged execute-never)
        if let Some(uxn) = self.uxn {
            solver.assert_eq(Extract(54, 54, Box::new(Var(desc))), bool_to_bit(uxn))
        }

        // Bit 53 is PXN (Privileged execute-never)
        if let Some(pxn) = self.pxn {
            solver.assert_eq(Extract(54, 54, Box::new(Var(desc))), bool_to_bit(pxn))
        }

        // Bit 52 is the contiguous bit
        if let Some(contiguous) = self.contiguous {
            solver.assert_eq(Extract(52, 52, Box::new(Var(desc))), bool_to_bit(contiguous))
        }

        // Bit 11 is nG (not global bit)
        if let Some(n_g) = self.n_g {
            solver.assert_eq(Extract(11, 11, Box::new(Var(desc))), bool_to_bit(n_g))
        }

        // Bit 10 is AF (access flag)
        if let Some(af) = self.af {
            solver.assert_eq(Extract(10, 10, Box::new(Var(desc))), bool_to_bit(af))
        }

        // Bits 9-8 is SH (shareability field)
        if let Some(sh) = self.sh {
            solver.assert_eq(Extract(9, 8, Box::new(Var(desc))), bits64(sh as u64 & 0b11, 2))
        }

        // Bits 7-6 is AP (access permissions)
        if let Some(ap) = self.ap {
            solver.assert_eq(Extract(7, 6, Box::new(Var(desc))), bits64(ap as u64 & 0b11, 2))
        }

        // Bit 5 is NS (non-secure bit)
        if let Some(ns) = self.ns {
            solver.assert_eq(Extract(5, 5, Box::new(Var(desc))), bool_to_bit(ns))
        }

        // Bits 4-2 AttrIndx
        if let Some(attr_indx) = self.attr_indx {
            solver.assert_eq(Extract(4, 2, Box::new(Var(desc))), bits64(attr_indx as u64 & 0b111, 3))
        }
    }

    fn set_field<B: BV>(&mut self, attr: &str, bits: B) -> Option<()> {
        if let Some((_, hi, lo)) = Self::fields().iter().find(|info| info.0 == attr) {
            let len = (hi - lo) + 1;
            if u64::from(bits.len()) != len {
                return None;
            }
        } else {
            return None;
        }

        match attr {
            "UXN" => self.uxn = Some(!bits.is_zero()),
            "PXN" => self.pxn = Some(!bits.is_zero()),
            "Contiguous" => self.contiguous = Some(!bits.is_zero()),
            "nG" => self.n_g = Some(!bits.is_zero()),
            "AF" => self.af = Some(!bits.is_zero()),
            "SH" => self.sh = Some(bits.lower_u8()),
            "AP" => self.ap = Some(bits.lower_u8()),
            "NS" => self.ns = Some(!bits.is_zero()),
            "AttrIndx" => self.attr_indx = Some(bits.lower_u8()),
            _ => unreachable!(),
        }

        Some(())
    }
}

impl PageAttrs for S2PageAttrs {
    fn unknown() -> Self {
        S2PageAttrs { xn: None, contiguous: None, af: None, sh: None, s2ap: None, mem_attr: None }
    }

    fn fields() -> &'static [(&'static str, u64, u64)] {
        &S2_PAGE_ATTR_FIELDS
    }

    fn bits(&self) -> (u64, u64) {
        let mut set = 0;
        let mut unknown = 0;

        attr_bool!(self.xn, 54, set, unknown);
        attr_bool!(self.contiguous, 52, set, unknown);
        attr_bool!(self.af, 10, set, unknown);
        attr_u8!(self.sh, 9, 8, set, unknown);
        attr_u8!(self.s2ap, 7, 6, set, unknown);
        attr_u8!(self.mem_attr, 5, 2, set, unknown);

        (set, unknown)
    }

    fn set<B: BV>(&self, desc: Sym, solver: &mut Solver<B>) {
        use Exp::*;

        // Bit 54 is XN (Execute-never)
        if let Some(xn) = self.xn {
            solver.assert_eq(Extract(54, 54, Box::new(Var(desc))), bool_to_bit(xn))
        }

        // Bit 53 is always 0
        solver.assert_eq(Extract(53, 53, Box::new(Var(desc))), bits64(0, 1));

        // Bit 52 is the contiguous bit
        if let Some(contiguous) = self.contiguous {
            solver.assert_eq(Extract(52, 52, Box::new(Var(desc))), bool_to_bit(contiguous))
        }

        // Bit 11 is always 0
        solver.assert_eq(Extract(53, 53, Box::new(Var(desc))), bits64(0, 1));

        // Bit 10 is AF (access flag)
        if let Some(af) = self.af {
            solver.assert_eq(Extract(10, 10, Box::new(Var(desc))), bool_to_bit(af))
        }

        // Bits 9-8 is SH (shareability field)
        if let Some(sh) = self.sh {
            solver.assert_eq(Extract(9, 8, Box::new(Var(desc))), bits64(sh as u64 & 0b11, 2))
        }

        // Bits 7-6 is S2AP (stage 2 access permissions)
        if let Some(s2ap) = self.s2ap {
            solver.assert_eq(Extract(7, 6, Box::new(Var(desc))), bits64(s2ap as u64 & 0b11, 2))
        }

        // Bits 5-2 MemAttr (memory regions attributes for stage 2 translations)
        if let Some(mem_attr) = self.mem_attr {
            solver.assert_eq(Extract(5, 2, Box::new(Var(desc))), bits64(mem_attr as u64 & 0b1111, 4))
        }
    }

    fn set_field<B: BV>(&mut self, attr: &str, bits: B) -> Option<()> {
        if let Some((_, hi, lo)) = Self::fields().iter().find(|info| info.0 == attr) {
            let len = (hi - lo) + 1;
            if u64::from(bits.len()) != len {
                return None;
            }
        } else {
            return None;
        }

        match attr {
            "XN" => self.xn = Some(!bits.is_zero()),
            "Contiguous" => self.contiguous = Some(!bits.is_zero()),
            "AF" => self.af = Some(!bits.is_zero()),
            "SH" => self.sh = Some(bits.lower_u8()),
            "S2AP" => self.s2ap = Some(bits.lower_u8()),
            "MemAttr" => self.mem_attr = Some(bits.lower_u8()),
            _ => unreachable!(),
        }

        Some(())
    }
}

/// An index for a page table.
#[derive(Debug, Copy, Clone)]
pub struct Index {
    base_addr: u64,
    ix: usize,
}

/// Get the physical address of a page table from it's index.
pub fn table_address(i: Index) -> u64 {
    i.base_addr + ((i.ix as u64) << 12)
}

/// A 64-bit page table descriptor.
#[derive(Clone)]
pub enum Desc<B> {
    Concrete(u64),

    /// A Symbolic descriptor has an initial value and a dynamic callback of the Smt expression to use
    /// which encodes a set of possible bitvectors.
    ///
    /// For debugging purposes we also store a vector of those bits here for printing, etc.
    Symbolic(u64, Vec<u64>, Arc<dyn Send + Sync + Fn(&mut Solver<B>) -> Sym>),
}

impl<B> fmt::Debug for Desc<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Desc::Concrete(i) => write!(f, "Concrete({})", i),
            Desc::Symbolic(init, maybe_bits, _) => write!(f, "Symbolic({}, {:?} + dyn)", init, maybe_bits),
        }
    }
}

/// Returns the concrete bits representing a level 3 page descriptor
/// with attributes applied. Returns None if the attributes could be
/// unknown (as unknown attributes cannot be represented in concrete
/// page bits).
pub fn page_desc_bits<P: PageAttrs>(page: u64, attrs: P) -> Option<u64> {
    let mask: u64 = ((1 << 36) - 1) << 12;
    let (attrs, unknowns) = attrs.bits();

    if unknowns == 0 {
        Some((page & mask) | 0b11 | attrs)
    } else {
        None
    }
}

pub fn block_desc_bits<P: PageAttrs>(page: u64, attrs: P, level: u64) -> Option<u64> {
    assert!(level == 1 || level == 2);

    let res0 = 30 - (9 * (level - 1));
    let mask: u64 = ((1 << (48 - res0)) - 1) << res0;
    let (attrs, unknowns) = attrs.bits();

    if unknowns == 0 {
        Some((page & mask) | 0b01 | attrs)
    } else {
        None
    }
}

impl<B: BV> Desc<B> {
    pub fn into_val(self, solver: &mut Solver<B>) -> Val<B> {
        match self {
            Desc::Concrete(bits) => Val::Bits(B::new(bits, 64)),
            Desc::Symbolic(_, _, desc) => Val::Symbolic(desc(solver)),
        }
    }

    pub fn to_val(&self, solver: &mut Solver<B>) -> Val<B> {
        match self {
            Desc::Concrete(bits) => Val::Bits(B::new(*bits, 64)),
            Desc::Symbolic(_, _, desc) => Val::Symbolic(desc(solver)),
        }
    }

    // An invalid level 3 descriptor is any where bit 0 is 0
    pub fn new_invalid() -> Self {
        Desc::Concrete(0)
    }

    pub fn initial_value(&self) -> u64 {
        match self {
            Desc::Concrete(bits) => *bits,
            Desc::Symbolic(init, _, _) => *init,
        }
    }

    // A reserved level 3 descriptor is any where bits 1-0 are 0b01. The other bits are RES0
    pub fn new_reserved() -> Self {
        Desc::Concrete(1)
    }

    pub fn new_table(table: Index) -> Self {
        Desc::Concrete(table_address(table) | 0b11)
    }

    fn is_concrete_invalid(&self) -> bool {
        match self {
            Desc::Concrete(desc) => *desc == 0,
            _ => false,
        }
    }

    pub fn concrete_table_address(&self) -> Option<u64> {
        match self {
            Desc::Concrete(desc) => Some(*desc & !0b11),
            _ => None,
        }
    }

    pub fn page<P: PageAttrs>(page: u64, attrs: P) -> Self {
        if let Some(desc) = page_desc_bits(page, attrs) {
            Desc::Concrete(desc)
        } else {
            Desc::new_invalid()
        }
    }

    pub fn block<P: PageAttrs>(output_address: u64, attrs: P, level: u64) -> Self {
        if let Some(desc) = block_desc_bits(output_address, attrs, level) {
            Desc::Concrete(desc)
        } else {
            Desc::new_invalid()
        }
    }

    pub fn symbolic_address(&self, solver: &mut Solver<B>) -> Sym {
        use Exp::*;
        match self {
            Desc::Concrete(addr) => {
                let mask = bzhi_u64(u64::MAX ^ 0xFFF, 48);
                solver.define_const(bits64(*addr & mask, 64), SourceLoc::unknown())
            }
            Desc::Symbolic(_, _, desc) => {
                let v = desc(solver);
                solver.define_const(
                    ZeroExtend(
                        16,
                        Box::new(Concat(Box::new(Extract(47, 12, Box::new(Var(v)))), Box::new(bits64(0, 12)))),
                    ),
                    SourceLoc::unknown(),
                )
            }
        }
    }

    pub fn or_bits(self, new_bits: u64) -> Self {
        log!(log::MEMORY, &format!("Allowing descriptor bit pattern: 0x{:x}", new_bits));
        use Exp::*;
        match self {
            Desc::Concrete(old_bits) => Desc::Symbolic(
                old_bits,
                vec![new_bits],
                Arc::new(move |solver| solver.choice(bits64(old_bits, 64), bits64(new_bits, 64), SourceLoc::unknown())),
            ),
            Desc::Symbolic(init, mut maybe_bits, old_desc) => {
                maybe_bits.push(new_bits);
                Desc::Symbolic(
                    init,
                    maybe_bits,
                    Arc::new(move |solver| {
                        let v = old_desc(solver);
                        solver.choice(Var(v), bits64(new_bits, 64), SourceLoc::unknown())
                    }),
                )
            }
        }
    }

    /// Make a level 3 descriptor potentially be invalid
    pub fn or_invalid(self) -> Self {
        self.or_desc(0)
    }

    /// Make a level 3 descriptor potentially be a fixed given descriptor
    pub fn or_desc(self, desc: u64) -> Self {
        self.or_bits(desc)
    }
}

/// A concrete ARMv8 virtual address
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct VirtualAddress {
    pub bits: u64,
}

impl VirtualAddress {
    /// Create a virtual address from a 64-bit unsigned integer. This
    /// function will clear all bits from 48 and above to guarantee it
    /// is a valid ARMv8 virtual address.
    pub fn from_u64(bits: u64) -> Self {
        VirtualAddress { bits: bzhi_u64(bits, 48) }
    }

    pub fn bits(self) -> u64 {
        self.bits
    }

    /// `va.level_index(n)` will return the index used for the
    /// translation table at level `n` when translating `va`. Panics
    /// if `n > 3`.
    pub fn level_index(self, level: u64) -> usize {
        assert!(level <= 3);
        ((self.bits >> ((3 - level) * 9 + 12)) & ((1 << 9) - 1)) as usize
    }

    /// Return the offset of a virtual address within a 4K page.
    pub fn page_offset(self, level: u64) -> u64 {
        assert!(level == 1 || level == 2 || level == 3);
        let mask = bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, 12 + (9 * (3 - level as u32)));
        self.bits & mask
    }

    /// Create a virtual address that will be translated by the
    /// translation table indices in order from level 0 to 3 plus a
    /// page offset. Panics if any level argument is not less than
    /// 512, and the page offset is not less than 4096.
    pub fn from_indices(level0: usize, level1: usize, level2: usize, level3: usize, page_offset: usize) -> Self {
        let mut bits = 0;

        assert!(level0 < 512);
        bits |= (level0 as u64) << (12 + (9 * 3));

        assert!(level1 < 512);
        bits |= (level1 as u64) << (12 + (9 * 2));

        assert!(level2 < 512);
        bits |= (level2 as u64) << (12 + 9);

        assert!(level3 < 512);
        bits |= (level3 as u64) << 12;

        assert!(page_offset < 4096);
        bits |= page_offset as u64;

        VirtualAddress { bits }
    }
}

#[derive(Debug, Clone)]
struct PageTable<B> {
    table: Vec<Desc<B>>,
}

impl<B: BV> PageTable<B> {
    fn from_descriptor(desc: Desc<B>) -> Self {
        PageTable { table: vec![desc; 512] }
    }
}

#[derive(Debug, Clone)]
pub struct PageTables<B> {
    base_addr: u64,
    tables: Vec<PageTable<B>>,
    region: &'static str,
}

#[derive(Debug, Clone)]
pub struct ImmutablePageTables<B> {
    base_addr: u64,
    tables: Arc<[PageTable<B>]>,
    region: &'static str,
}

#[derive(Clone, Debug, Default)]
pub struct UpdateWalk {
    tables: [u64; 3],
    ptes: [u64; 4],
    updated: Vec<u64>,
}

impl UpdateWalk {
    fn table(&self, level: u64) -> u64 {
        assert!(level == 1 || level == 2 || level == 3);
        self.tables[level as usize - 1]
    }

    fn table_mut(&mut self, level: u64) -> &mut u64 {
        assert!(level == 1 || level == 2 || level == 3);
        &mut self.tables[level as usize - 1]
    }

    fn pte(&self, level: u64) -> u64 {
        assert!(level == 0 || level == 1 || level == 2 || level == 3);
        self.ptes[level as usize]
    }

    fn pte_mut(&mut self, level: u64) -> &mut u64 {
        assert!(level == 0 || level == 1 || level == 2 || level == 3);
        &mut self.ptes[level as usize]
    }
}

impl<B: BV> PageTables<B> {
    /// Create a new set of ARMv8 page tables, which is initially
    /// empty. The base address will be the address used to allocate
    /// the first table, which are then allocated contiguously in 4K
    /// chunks. A translation table base register (e.g. TTBR0_EL1) can
    /// point to any valid translation table, so does not have to
    /// match this value.
    pub fn new(region: &'static str, base_addr: u64) -> Self {
        PageTables { base_addr, tables: Vec::new(), region }
    }

    pub fn range(&self) -> Range<u64> {
        self.base_addr..(self.base_addr + 4096 * self.tables.len() as u64)
    }

    /// Allocate a new translation table.
    pub fn alloc(&mut self) -> Index {
        log!(log::MEMORY, &format!("Allocating new table 0x{:x}", self.base_addr + 4096 * self.tables.len() as u64));
        self.tables.push(PageTable::from_descriptor(Desc::new_invalid()));
        Index { base_addr: self.base_addr, ix: self.tables.len() - 1 }
    }

    pub fn get(&self, i: Index) -> &[Desc<B>] {
        &self.tables[i.ix].table
    }

    pub fn get_mut(&mut self, i: Index) -> &mut [Desc<B>] {
        &mut self.tables[i.ix].table
    }

    /// Lookup a translation table at a specific physical
    /// address. Returns None if there is no level 3 translation table
    /// at that address.
    pub fn lookup(&self, addr: u64) -> Option<Index> {
        if addr < self.base_addr {
            return None;
        };

        let i = ((addr - self.base_addr) >> 12) as usize;
        if self.tables.get(i).is_some() {
            Some(Index { base_addr: self.base_addr, ix: i })
        } else {
            None
        }
    }

    pub fn update<F>(&mut self, level0: Index, va: VirtualAddress, update_desc: F, level: u64) -> Option<UpdateWalk>
    where
        B: BV,
        F: Fn(Desc<B>) -> Option<Desc<B>>,
    {
        log!(log::MEMORY, &format!("Creating page table mapping: 0x{:x} at level {}", va.bits, level));
        if !(level == 1 || level == 2 || level == 3) {
            return None;
        }

        let mut desc = self.get(level0)[va.level_index(0)].clone();
        let mut table = level0;
        let mut walk_info = UpdateWalk::default();

        *walk_info.pte_mut(0) = table_address(level0) + va.level_index(0) as u64;

        // Create the level 1 and 2 descriptors
        for i in 1..=(level - 1) {
            if desc.is_concrete_invalid() {
                log!(
                    log::MEMORY,
                    &format!(
                        "Creating level {} descriptor location 0x{:x} + {}",
                        i - 1,
                        table_address(table),
                        va.level_index(i - 1)
                    )
                );
                desc = Desc::new_table(self.alloc());
                self.get_mut(table)[va.level_index(i - 1)] = desc.clone();
            }

            table = self.lookup(desc.concrete_table_address().unwrap())?;
            desc = self.get(table)[va.level_index(i)].clone();

            *walk_info.table_mut(i) = table_address(table);
            *walk_info.pte_mut(i) = table_address(table) + va.level_index(i) as u64;
        }

        let table = self.lookup(desc.concrete_table_address()?).unwrap_or_else(|| {
            log!(
                log::MEMORY,
                &format!(
                    "Creating level {} descriptor location 0x{:x} + {}",
                    level - 1,
                    table_address(table),
                    va.level_index(level - 1)
                )
            );
            let next_table = self.alloc();
            self.get_mut(table)[va.level_index(level - 1)] = Desc::new_table(next_table);
            next_table
        });

        log!(
            log::MEMORY,
            &format!(
                "Updating level {} descriptor location 0x{:x} + {}",
                level,
                table_address(table),
                va.level_index(level)
            )
        );

        *walk_info.table_mut(level) = table_address(table);
        *walk_info.pte_mut(level) = table_address(table) + va.level_index(level) as u64;

        let desc = &mut self.get_mut(table)[va.level_index(level)];
        *desc = update_desc(desc.clone())?;
        walk_info.updated.push(walk_info.pte(level));

        Some(walk_info)
    }

    pub fn map<P: PageAttrs>(
        &mut self,
        level0: Index,
        va: VirtualAddress,
        page: u64,
        is_table: bool,
        attrs: P,
        level: u64,
    ) -> Option<UpdateWalk> {
        if is_table && (level == 1 || level == 2) {
            self.update(level0, va, |_| Some(Desc::Concrete(page | 0b11)), level)
        } else if level == 1 || level == 2 {
            self.update(level0, va, |_| Some(Desc::block(page, attrs.clone(), level)), level)
        } else if level == 3 {
            self.update(level0, va, |_| Some(Desc::page(page, attrs.clone())), level)
        } else {
            None
        }
    }

    pub fn maybe_map<P: PageAttrs>(
        &mut self,
        level0: Index,
        va: VirtualAddress,
        page: u64,
        is_table: bool,
        attrs: P,
        level: u64,
    ) -> Option<UpdateWalk> {
        if is_table && (level == 1 || level == 2) {
            self.update(level0, va, |desc| Some(desc.or_bits(page | 0b11)), level)
        } else if level == 1 || level == 2 {
            self.update(level0, va, |desc| Some(desc.or_bits(block_desc_bits(page, attrs.clone(), level)?)), level)
        } else if level == 3 {
            self.update(level0, va, |desc| Some(desc.or_bits(page_desc_bits(page, attrs.clone())?)), level)
        } else {
            None
        }
    }

    pub fn maybe_invalid(&mut self, level0: Index, va: VirtualAddress, level: u64) -> Option<UpdateWalk> {
        self.update(level0, va, |desc| Some(desc.or_invalid()), level)
    }

    pub fn maybe_raw_desc(
        &mut self,
        level0: Index,
        va: VirtualAddress,
        level: u64,
        rawdesc: u64,
    ) -> Option<UpdateWalk> {
        self.update(level0, va, |desc| Some(desc.or_desc(rawdesc)), level)
    }

    pub fn invalid(&mut self, level0: Index, va: VirtualAddress, level: u64) -> Option<UpdateWalk> {
        self.update(level0, va, |_| Some(Desc::new_invalid()), level)
    }

    pub fn identity_map<P: PageAttrs>(&mut self, level0: Index, page: u64, attrs: P, level: u64) -> Option<UpdateWalk> {
        self.map(level0, VirtualAddress::from_u64(page), page, false, attrs, level)
    }

    pub fn freeze(&self) -> ImmutablePageTables<B> {
        ImmutablePageTables { base_addr: self.base_addr, tables: self.tables.clone().into(), region: self.region }
    }
}

impl<B: BV> ImmutablePageTables<B> {
    fn initial_descriptor(&self, addr: u64) -> Option<u64> {
        let table_addr = addr & !0xFFF;

        // Ensure page table reads are 8 bytes and aligned
        if (addr & 0b111) != 0 || table_addr < self.base_addr {
            return None;
        }

        let offset = ((addr & 0xFFF) >> 3) as usize;
        let i = ((table_addr - self.base_addr) >> 12) as usize;

        let desc: Val<B> = match self.tables.get(i) {
            Some(PageTable { table }) => Val::Bits(B::new(table[offset].initial_value(), 64)),
            None => return None,
        };

        match desc {
            Val::Bits(bv) => Some(bv.lower_u64()),
            _ => None,
        }
    }
}

impl<B: BV> CustomRegion<B> for ImmutablePageTables<B> {
    fn read(
        &self,
        read_kind: Val<B>,
        addr: u64,
        bytes: u32,
        solver: &mut Solver<B>,
        _tag: bool,
    ) -> Result<Val<B>, ExecError> {
        log!(log::MEMORY, &format!("Page table read: 0x{:x}", addr));

        let table_addr = addr & !0xFFF;

        // Ensure page table reads are 8 bytes and aligned
        if (addr & 0b111) != 0 || bytes != 8 || table_addr < self.base_addr {
            return Err(ExecError::BadRead("unaligned page table read"));
        }

        let offset = ((addr & 0xFFF) >> 3) as usize;
        let i = ((table_addr - self.base_addr) >> 12) as usize;

        let desc: Val<B> = match self.tables.get(i) {
            Some(PageTable { table }) => table[offset].to_val(solver),
            None => return Err(ExecError::BadRead("page table index out of bounds")),
        };

        solver.add_event(Event::ReadMem {
            value: desc.clone(),
            read_kind,
            address: Val::Bits(B::from_u64(addr)),
            bytes,
            tag_value: None,
            opts: ReadOpts::default(),
            region: self.region,
        });

        log!(log::MEMORY, &format!("Page table descriptor: 0x{:x} -> {:?}", addr, desc));

        Ok(desc)
    }

    fn write(
        &mut self,
        write_kind: Val<B>,
        addr: u64,
        write_desc: Val<B>,
        solver: &mut Solver<B>,
        tag: Option<Val<B>>,
    ) -> Result<Val<B>, ExecError> {
        log!(log::MEMORY, &format!("Page table write: 0x{:x} <- {:?}", addr, write_desc));

        let table_addr = addr & !0xFFF;
        let write_len_bits = length_bits(&write_desc, solver, SourceLoc::unknown())?;

        // Ensure page table writes are also 8 bytes and aligned
        if (addr & 0b111) != 0 || write_len_bits != 64 || table_addr < self.base_addr {
            return Err(ExecError::BadWrite("unaligned page table write"));
        }

        let offset = ((addr & 0xFFF) >> 3) as usize;
        let i = ((table_addr - self.base_addr) >> 12) as usize;

        let current_desc: Val<B> = match self.tables.get(i) {
            Some(PageTable { table }) => table[offset].to_val(solver),
            None => return Err(ExecError::BadWrite("page table index out of bounds")),
        };

        let (skip_sat_check, query) = match (current_desc, &write_desc) {
            (Val::Bits(d1), Val::Bits(d2)) if d1 == *d2 => (true, Exp::Bool(true)),
            (Val::Bits(d1), Val::Symbolic(d2)) => (false, Exp::Eq(Box::new(smt_sbits(d1)), Box::new(Exp::Var(*d2)))),
            (Val::Symbolic(d1), Val::Bits(d2)) => (false, Exp::Eq(Box::new(Exp::Var(d1)), Box::new(smt_sbits(*d2)))),
            (Val::Symbolic(d1), Val::Symbolic(d2)) => (false, Exp::Eq(Box::new(Exp::Var(d1)), Box::new(Exp::Var(*d2)))),
            (Val::Bits(_), Val::Bits(_)) => {
                return Err(ExecError::BadWrite("page table write trivially unsatisfiable"))
            }
            (_, _) => return Err(ExecError::BadWrite("ill-typed descriptor")),
        };

        if skip_sat_check || solver.check_sat_with(&query, SourceLoc::unknown()) == SmtResult::Sat {
            let value = solver.declare_const(Ty::Bool, SourceLoc::unknown());
            solver.add_event(Event::WriteMem {
                value,
                write_kind,
                address: Val::Bits(B::from_u64(addr)),
                data: write_desc,
                bytes: 8,
                tag_value: tag,
                opts: WriteOpts::default(),
                region: self.region,
            });
            Ok(Val::Symbolic(value))
        } else {
            Err(ExecError::BadWrite("page table write unsatisfiable"))
        }
    }

    fn initial_value(&self, addr: u64, bytes: u32) -> Option<B> {
        let desc_addr = addr & !0b111;
        let desc_offset = addr & 0b111;

        if (bytes as u64 + desc_offset) > 8 {
            return None;
        };

        let desc = self.initial_descriptor(desc_addr)?;

        Some(B::new(bzhi_u64(desc >> (desc_offset * 8), bytes * 8), bytes * 8))
    }

    fn region_name(&self) -> &'static str {
        self.region
    }

    fn clone_dyn(&self) -> Box<dyn Send + Sync + CustomRegion<B>> {
        Box::new(self.clone())
    }
}

pub struct TranslationTableWalk {
    pub(crate) l0pte: u64,
    pub(crate) l0desc: u64,
    pub(crate) l1pte: u64,
    pub(crate) l1desc: u64,
    pub(crate) l2pte: u64,
    pub(crate) l2desc: u64,
    pub(crate) l3pte: u64,
    pub(crate) l3desc: u64,
    pub(crate) pa: u64,
}

fn desc_to_u64<B: BV>(desc: Val<B>) -> Result<u64, ExecError> {
    match desc {
        Val::Bits(bv) => Ok(bv.lower_u64()),
        _ => Err(ExecError::BadRead("symbolic descriptor")),
    }
}

/// To compute the various bits of translation table information we
/// might need in the initial state, we have a function that does a
/// simple translation table walk and records each intermedate
/// descriptor address in the l0pte to l3pte fields of the
/// `TranslationTableWalk` struct, and the descriptor values in the
/// l0desc to l3desc fields. All the flags in the descriptors are
/// ignored.
///
/// For now we assume a 4K granule. If a block descriptor is
/// encountered, all higher level descriptor fields will be zero.
///
/// If an entry is invalid, then all higher level fields will be zero, including the PA.
pub fn initial_translation_table_walk<B: BV>(
    va: VirtualAddress,
    table_addr: u64,
    memory: &Memory<B>,
) -> Result<TranslationTableWalk, ExecError> {
    fn is_block(desc: u64) -> bool {
        desc & 0b11 == 0b01
    }

    fn is_invalid(desc: u64) -> bool {
        desc & 0b1 == 0b0
    }

    fn pa(desc: u64, va: VirtualAddress, level: u64) -> u64 {
        (desc & bzhi_u64(!0xFFF, 48)) + va.page_offset(level)
    }

    let l0pte = table_addr + va.level_index(0) as u64 * 8;
    let l0desc = memory.read_initial(l0pte, 8).and_then(desc_to_u64)?;
    if is_invalid(l0desc) {
        return Ok(TranslationTableWalk {
            l0pte,
            l0desc,
            l1pte: 0,
            l1desc: 0,
            l2pte: 0,
            l2desc: 0,
            l3pte: 0,
            l3desc: 0,
            pa: 0,
        });
    }

    let l1pte = (l0desc & !0b11) + va.level_index(1) as u64 * 8;
    let l1desc = memory.read_initial(l1pte, 8).and_then(desc_to_u64)?;
    if is_block(l1desc) {
        let pa = pa(l1desc, va, 1);
        return Ok(TranslationTableWalk { l0pte, l0desc, l1pte, l1desc, l2pte: 0, l2desc: 0, l3pte: 0, l3desc: 0, pa });
    } else if is_invalid(l1desc) {
        return Ok(TranslationTableWalk {
            l0pte,
            l0desc,
            l1pte,
            l1desc,
            l2pte: 0,
            l2desc: 0,
            l3pte: 0,
            l3desc: 0,
            pa: 0,
        });
    }

    let l2pte = (l1desc & !0b11) + va.level_index(2) as u64 * 8;
    let l2desc = memory.read_initial(l2pte, 8).and_then(desc_to_u64)?;
    if is_block(l2desc) {
        let pa = pa(l2desc, va, 2);
        return Ok(TranslationTableWalk { l0pte, l0desc, l1pte, l1desc, l2pte, l2desc, l3pte: 0, l3desc: 0, pa });
    } else if is_invalid(l2desc) {
        return Ok(TranslationTableWalk { l0pte, l0desc, l1pte, l1desc, l2pte, l2desc, l3pte: 0, l3desc: 0, pa: 0 });
    }

    let l3pte = (l2desc & !0b11) + va.level_index(3) as u64 * 8;
    let l3desc = memory.read_initial(l3pte, 8).and_then(desc_to_u64)?;

    if is_invalid(l2desc) {
        Ok(TranslationTableWalk { l0pte, l0desc, l1pte, l1desc, l2pte, l2desc, l3pte, l3desc, pa: 0 })
    } else {
        let pa = pa(l3desc, va, 3);
        Ok(TranslationTableWalk { l0pte, l0desc, l1pte, l1desc, l2pte, l2desc, l3pte, l3desc, pa })
    }
}

fn name_bitvector<B: BV>(names: &mut HashMap<B, String>, bv: B, name: String) {
    if bv.is_zero() {
        return;
    }

    names
        .entry(bv)
        .and_modify(|existing_name| {
            if name.len() < existing_name.len() {
                *existing_name = name.clone()
            }
        })
        .or_insert(name);
}

pub fn name_initial_walk_bitvectors<B: BV>(
    names: &mut HashMap<B, String>,
    va_name: &str,
    va: VirtualAddress,
    table_name: &str,
    table_addr: u64,
    memory: &Memory<B>,
) {
    let table_name_short = if table_name == "s1_default" {
        "s1:".to_string()
    } else if table_name == "s2_default" {
        "s2:".to_string()
    } else {
        format!("{}:", table_name)
    };

    if let Ok(walk) = initial_translation_table_walk(va, table_addr, memory) {
        name_bitvector(names, B::from_u64(walk.l0pte), format!("{}l0pte({})", table_name_short, va_name));
        name_bitvector(names, B::from_u64(walk.l0desc), format!("{}l0desc({})", table_name_short, va_name));
        name_bitvector(names, B::from_u64(walk.l1pte), format!("{}l1pte({})", table_name_short, va_name));
        name_bitvector(names, B::from_u64(walk.l1desc), format!("{}l1desc({})", table_name_short, va_name));
        name_bitvector(names, B::from_u64(walk.l2pte), format!("{}l2pte({})", table_name_short, va_name));
        name_bitvector(names, B::from_u64(walk.l2desc), format!("{}l2desc({})", table_name_short, va_name));
        name_bitvector(names, B::from_u64(walk.l3pte), format!("{}l3pte({})", table_name_short, va_name));
        name_bitvector(names, B::from_u64(walk.l3desc), format!("{}l3desc({})", table_name_short, va_name));
        name_bitvector(names, B::from_u64(walk.pa), format!("{}pa({})", table_name_short, va_name));
    }
}

#[cfg(test)]
mod tests {
    use isla_lib::bitvector::b64::B64;
    use isla_lib::smt::{smtlib::Def, Config, Context};

    use super::*;

    #[test]
    fn test_va_index() {
        let va = VirtualAddress::from_u64(0x8000_1000);
        assert_eq!(va.level_index(3), 1);
        assert_eq!(va.level_index(2), 0);
        assert_eq!(va.level_index(1), 2);
        assert_eq!(va.level_index(0), 0);

        assert_eq!(va, VirtualAddress::from_indices(0, 2, 0, 1, 0));

        let va = VirtualAddress::from_u64(0x8000_0004);
        assert_eq!(va.level_index(3), 0);
        assert_eq!(va.level_index(2), 0);
        assert_eq!(va.level_index(1), 2);
        assert_eq!(va.level_index(0), 0);

        assert_eq!(va, VirtualAddress::from_indices(0, 2, 0, 0, 4));
    }

    #[test]
    fn test_table_address() {
        let mut tbls = PageTables::<B64>::new("test", 0x5000_0000);
        let tbl1 = tbls.alloc();
        let tbl2 = tbls.alloc();
        let tbl3 = tbls.alloc();
        assert_eq!(table_address(tbl1), 0x5000_0000);
        assert_eq!(table_address(tbl2), 0x5000_0000 + 4096);
        assert_eq!(table_address(tbl3), 0x5000_0000 + 4096 * 2);
    }

    /// A simple translation table walk for testing purposes. We
    /// assume 4k pages, ignore attributes, and assume that level 0-2
    /// tables always concretely point to lower level tables and not
    /// pages
    fn simple_translation_table_walk<B: BV>(
        tables: &PageTables<B>,
        level0: Index,
        va: VirtualAddress,
        solver: &mut Solver<B>,
    ) -> Option<Sym> {
        use Exp::*;

        let l0desc = &tables.get(level0)[va.level_index(0)];

        let level1 = tables.lookup(l0desc.concrete_table_address()?)?;
        let l1desc = &tables.get(level1)[va.level_index(1)];

        let level2 = tables.lookup(l1desc.concrete_table_address()?)?;
        let l2desc = &tables.get(level2)[va.level_index(2)];

        let level3 = tables.lookup(l2desc.concrete_table_address()?)?;
        let l3desc = &tables.get(level3)[va.level_index(3)];

        let page_addr = l3desc.symbolic_address(solver);
        let addr = solver.define_const(
            Bvadd(Box::new(Var(page_addr)), Box::new(bits64(va.page_offset(3), 64))),
            SourceLoc::unknown(),
        );

        Some(addr)
    }

    #[test]
    fn test_translate() {
        use Def::*;
        use Exp::*;
        use SmtResult::*;

        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);

        let mut tables = PageTables::<B64>::new("test", 0x5000_0000);
        let l3 = tables.alloc();
        let l2 = tables.alloc();
        let l1 = tables.alloc();
        let l0 = tables.alloc();

        let va = VirtualAddress::from_u64(0xDEAD_BEEF);

        // Create a level 3 descriptor that can point at one of either two pages
        tables.get_mut(l3)[va.level_index(3)] = Desc::page(0x8000_0000, S1PageAttrs::default())
            .or_bits(page_desc_bits(0x8000_1000, S1PageAttrs::default()).unwrap());
        tables.get_mut(l2)[va.level_index(2)] = Desc::new_table(l3);
        tables.get_mut(l1)[va.level_index(1)] = Desc::new_table(l2);
        tables.get_mut(l0)[va.level_index(0)] = Desc::new_table(l1);

        assert_eq!(Sat, solver.check_sat(SourceLoc::unknown()));

        // Translate our concrete virtual address to a symbolic
        // physical address, and check it could be in either page
        if let Some(pa) = simple_translation_table_walk(&tables, l0, va, &mut solver) {
            assert_eq!(
                Sat,
                solver.check_sat_with(&Eq(Box::new(Var(pa)), Box::new(bits64(0x8000_0EEF, 64))), SourceLoc::unknown())
            );
            assert_eq!(
                Sat,
                solver.check_sat_with(&Eq(Box::new(Var(pa)), Box::new(bits64(0x8000_1EEF, 64))), SourceLoc::unknown())
            );

            // Additionally, it  can't be anything other than those two addresses
            solver.add(Assert(Neq(Box::new(Var(pa)), Box::new(bits64(0x8000_0EEF, 64)))));
            solver.add(Assert(Neq(Box::new(Var(pa)), Box::new(bits64(0x8000_1EEF, 64)))));
            assert_eq!(Unsat, solver.check_sat(SourceLoc::unknown()));
        } else {
            panic!("simple_translation_table_walk failed")
        }
    }
}
