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

use std::convert::{From, Into};
use std::ops::Range;
use std::sync::Arc;

use isla_lib::bitvector::{bzhi_u64, BV, b64::B64};
use isla_lib::error::ExecError;
use isla_lib::executor::LocalFrame;
use isla_lib::ir::Val;
use isla_lib::log;
use isla_lib::memory::CustomRegion;
use isla_lib::primop::{length_bits, smt_sbits};
use isla_lib::smt::{
    smtlib::{Def, Exp, Ty, bits64},
    Event, SmtResult, Solver, Sym,
};

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

pub struct S2PageAttrs {
    xn: Option<bool>,
    contiguous: Option<bool>,
    af: Option<bool>,
    sh: Option<u8>,
    s2ap: Option<u8>,
    mem_attr: Option<u8>,
}

impl Default for S2PageAttrs {
    fn default() -> Self {
        S2PageAttrs {
            xn: Some(false),
            contiguous: Some(false),
            af: Some(true),
            sh: Some(0b00),
            s2ap: Some(0b01),
            mem_attr: Some(0b0000),
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
            mem_attr: Some(0b0000),
        }
    }
}

fn bool_to_bit(b: bool) -> Exp {
    bits64(if b { 1 } else { 0 }, 1)
}

pub trait PageAttrs {
    fn unknown() -> Self;

    fn bits(&self) -> (u64, u64);

    fn set<B: BV>(&self, desc: Sym, solver: &mut Solver<B>);
}

macro_rules! attr_bool {
    ($field: expr, $n: expr, $set: ident, $unknown: ident) => {
        if let Some(bit) = $field {
            $set |= u64::from(bit) << $n
        } else {
            $unknown |= 1 << $n
        }
    }
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
}

impl PageAttrs for S2PageAttrs {
    fn unknown() -> Self {
        S2PageAttrs { xn: None, contiguous: None, af: None, sh: None, s2ap: None, mem_attr: None }
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
}

/// An index for a level 3 page table. For type-safety and to aid in
/// constructing valid page tables, we wrap page table addresses into
/// a set of indexing types for level 3 and level 0, 1, and 2 page
/// tables, as well as generic indices which can be used for either.
#[derive(Copy, Clone)]
pub struct L3Index {
    base_addr: u64,
    ix: usize,
}

/// An index for a level 0, 1, or 2 page table.
#[derive(Copy, Clone)]
pub struct L012Index {
    base_addr: u64,
    ix: usize,
}

/// An index for a level 0, 1, 2, or 3 page table.
#[derive(Copy, Clone)]
pub struct GenericIndex {
    base_addr: u64,
    ix: usize,
}

impl From<L3Index> for GenericIndex {
    fn from(i: L3Index) -> Self {
        GenericIndex { base_addr: i.base_addr, ix: i.ix }
    }
}

impl From<L012Index> for GenericIndex {
    fn from(i: L012Index) -> Self {
        GenericIndex { base_addr: i.base_addr, ix: i.ix }
    }
}

/// Get the physical address of a page table from it's index.
pub fn table_address<I: Into<GenericIndex>>(i: I) -> u64 {
    let i = i.into();
    i.base_addr + ((i.ix as u64) << 12)
}

/// A level 3 page table descriptor.
#[derive(Copy, Clone, Debug)]
pub enum L3Desc {
    Concrete(u64),
    Symbolic(u64, Sym),
}

impl<B: BV> Into<Val<B>> for L3Desc {
    fn into(self) -> Val<B> {
        match self {
            L3Desc::Concrete(bits) => Val::Bits(B::new(bits, 64)),
            L3Desc::Symbolic(_, v) => Val::Symbolic(v),
        }
    }
}

impl L3Desc {
    // An invalid level 3 descriptor is any where bit 0 is 0
    pub fn new_invalid() -> Self {
        L3Desc::Concrete(0)
    }

    pub fn initial_value(self) -> u64 {
        match self {
            L3Desc::Concrete(bits) => bits,
            L3Desc::Symbolic(init, _) => init,
        }
    }

    // A reserved level 3 descriptor is any where bits 1-0 are 0b01. The other bits are RES0
    pub fn new_reserved() -> Self {
        L3Desc::Concrete(1)
    }

    pub fn page<P: PageAttrs>(page: u64, attrs: P) -> Self {
        let mask: u64 = ((1 << 36) - 1) << 12;
        let (attrs, unknowns) = attrs.bits();

        assert!(page & !mask == 0);
        assert!(unknowns == 0);
        
        let desc = (page & mask) | 0b11 | attrs;

        L3Desc::Concrete(desc)
    }

    pub fn symbolic_address<B: BV>(self, solver: &mut Solver<B>) -> Sym {
        use Exp::*;
        match self {
            L3Desc::Concrete(addr) => {
                let mask = bzhi_u64(u64::MAX ^ 0xFFF, 48);
                solver.define_const(bits64(addr & mask, 64))
            }
            L3Desc::Symbolic(_, v) => solver.define_const(ZeroExtend(
                16,
                Box::new(Concat(Box::new(Extract(47, 12, Box::new(Var(v)))), Box::new(bits64(0, 12)))),
            )),
        }
    }

    /// Make a level 3 descriptor potentially be invalid
    pub fn or_invalid<B: BV>(self, solver: &mut Solver<B>) -> Self {
        use Exp::*;
        let (init, old_desc) = match self {
            L3Desc::Concrete(bits) => (bits, bits64(bits, 64)),
            L3Desc::Symbolic(init, v) => (init, Var(v)),
        };
        let is_invalid = solver.declare_const(Ty::Bool);
        let new_desc = solver.define_const(Ite(Box::new(Var(is_invalid)), Box::new(bits64(0, 64)), Box::new(old_desc)));
        L3Desc::Symbolic(init, new_desc)
    }

    // A symbolic level 3 descriptor pointing to a set of possible
    // pages. If pages is empty return an invalid descriptor
    pub fn new_symbolic<B: BV, P: PageAttrs>(pages: &[u64], attrs: P, solver: &mut Solver<B>) -> Self {
        use Exp::*;

        let desc = solver.declare_const(Ty::BitVec(64));

        // bits 51 to 48 are reserved and always zero (RES0)
        solver.assert_eq(Extract(51, 48, Box::new(Var(desc))), bits64(0b0000, 4));

        // buts 1 to 0 are always 0b11 for a valid address descriptor
        solver.assert_eq(Extract(1, 0, Box::new(Var(desc))), bits64(0b11, 2));

        // Attributes are in bits 63-52 and 11-2
        attrs.set(desc, solver);

        // For a 4K page size bits 47-12 contain the output address
        let mut page_constraints = Vec::new();
        for page in pages {
            page_constraints.push(Eq(Box::new(Extract(47, 12, Box::new(Var(desc)))), Box::new(bits64(page >> 12, 36))))
        }

        if let Some(p) = page_constraints.pop() {
            let constraint = page_constraints.drain(..).fold(p, |p1, p2| Or(Box::new(p1), Box::new(p2)));
            solver.add(Def::Assert(constraint))
        } else {
            return L3Desc::new_invalid();
        }

        L3Desc::Symbolic(pages[0], desc)
    }
}

/// A level 0, 1, or 2 page table descriptor.
#[derive(Copy, Clone, Debug)]
pub enum L012Desc {
    Concrete(u64),
    Symbolic(Sym),
}

impl<B: BV> Into<Val<B>> for L012Desc {
    fn into(self) -> Val<B> {
        match self {
            L012Desc::Concrete(bits) => Val::Bits(B::new(bits, 64)),
            L012Desc::Symbolic(v) => Val::Symbolic(v),
        }
    }
}

impl L012Desc {
    // An invalid level 0, 1 or 2 descriptor is any where bit 0 is 0
    fn new_invalid() -> Self {
        L012Desc::Concrete(0)
    }

    fn is_concrete_invalid(self) -> bool {
        match self {
            L012Desc::Concrete(desc) => desc == 0,
            _ => false,
        }
    }

    pub fn concrete_address(self) -> Option<u64> {
        match self {
            L012Desc::Concrete(desc) => Some(desc & !0b11),
            _ => None,
        }
    }

    pub fn new_table<T: Into<GenericIndex>>(table: T) -> Self {
        L012Desc::Concrete(table_address(table) | 0b11)
    }
}

/// A concrete ARMv8 virtual address
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct VirtualAddress {
    bits: u64,
}

impl VirtualAddress {
    /// Create a virtual address from a 64-bit unsigned integer. This
    /// function will clear all bits from 48 and above to guarantee it
    /// is a valid ARMv8 virtual address.
    pub fn from_u64(bits: u64) -> Self {
        VirtualAddress { bits: bzhi_u64(bits, 48) }
    }

    /// `va.level_index(n)` will return the index used for the
    /// translation table at level `n` when translating `va`. Panics
    /// if `n > 3`.
    pub fn level_index(self, level: u64) -> usize {
        assert!(level <= 3);
        ((self.bits >> ((3 - level) * 9 + 12)) & ((1 << 9) - 1)) as usize
    }

    /// Return the offset of a virtual address within a 4K page.
    pub fn page_offset(self) -> u64 {
        self.bits & 0xFFF
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

#[derive(Clone)]
enum PageTable {
    L3([L3Desc; 512]),
    L012([L012Desc; 512]),
}

#[derive(Clone)]
pub struct PageTables {
    base_addr: u64,
    tables: Vec<PageTable>,
    kind: &'static str,
}

#[derive(Clone)]
pub struct ImmutablePageTables {
    base_addr: u64,
    tables: Arc<[PageTable]>,
    kind: &'static str,
}

impl PageTables {
    /// Create a new set of ARMv8 page tables, which is initially
    /// empty. The base address will be the address used to allocate
    /// the first table, which are then allocated contiguously in 4K
    /// chunks. A translation table base register (e.g. TTBR0_EL1) can
    /// point to any valid translation table, so does not have to
    /// match this value.
    pub fn new(kind: &'static str, base_addr: u64) -> Self {
        PageTables { base_addr, tables: Vec::new(), kind }
    }

    pub fn range(&self) -> Range<u64> {
        self.base_addr..(self.base_addr + 4096 * self.tables.len() as u64)
    }

    /// Allocate a new level 3 translation table.
    pub fn alloc_l3(&mut self) -> L3Index {
        log!(log::MEMORY, "Allocating new level 3 table");
        self.tables.push(PageTable::L3([L3Desc::new_invalid(); 512]));
        L3Index { base_addr: self.base_addr, ix: self.tables.len() - 1 }
    }

    /// Allocate a new level 0, 1, or 2 translation table
    pub fn alloc(&mut self) -> L012Index {
        log!(log::MEMORY, "Allocating new level 0, 1, or 2 table");
        self.tables.push(PageTable::L012([L012Desc::new_invalid(); 512]));
        L012Index { base_addr: self.base_addr, ix: self.tables.len() - 1 }
    }

    pub fn get_l3(&self, i: L3Index) -> &[L3Desc; 512] {
        match &self.tables[i.ix] {
            PageTable::L3(table) => table,
            _ => panic!("invalid page table index"),
        }
    }

    pub fn get_l3_mut(&mut self, i: L3Index) -> &mut [L3Desc; 512] {
        match &mut self.tables[i.ix] {
            PageTable::L3(table) => table,
            _ => panic!("invalid page table index"),
        }
    }

    pub fn get(&self, i: L012Index) -> &[L012Desc; 512] {
        match &self.tables[i.ix] {
            PageTable::L012(table) => table,
            _ => panic!("invalid page table index"),
        }
    }

    pub fn get_mut(&mut self, i: L012Index) -> &mut [L012Desc; 512] {
        match &mut self.tables[i.ix] {
            PageTable::L012(table) => table,
            _ => panic!("invalid page table index"),
        }
    }

    /// Lookup a level 3 translation table at a specific physical
    /// address. Returns None if there is no level 3 translation table
    /// at that address.
    pub fn lookup_l3(&self, addr: u64) -> Option<L3Index> {
        if addr < self.base_addr {
            return None;
        };

        let i = ((addr - self.base_addr) >> 12) as usize;
        if let Some(PageTable::L3(_)) = self.tables.get(i) {
            Some(L3Index { base_addr: self.base_addr, ix: i })
        } else {
            None
        }
    }

    /// The same as `lookup_l3` but for level 0, 1 and 2 tables.
    pub fn lookup(&self, addr: u64) -> Option<L012Index> {
        if addr < self.base_addr {
            return None;
        };

        let i = ((addr - self.base_addr) >> 12) as usize;
        if let Some(PageTable::L012(_)) = self.tables.get(i) {
            Some(L012Index { base_addr: self.base_addr, ix: i })
        } else {
            None
        }
    }

    pub fn map<B: BV, P: PageAttrs>(&mut self, level0: L012Index, va: VirtualAddress, page: u64, attrs: P, maybe_invalid: Option<&mut Solver<B>>) -> Option<()> {
        log!(log::MEMORY, &format!("Creating page table mapping: 0x{:x} -> 0x{:x}", va.bits, page));

        let mut desc: L012Desc = self.get(level0)[va.level_index(0)];
        let mut table = level0;

        for i in 1..=2 {
            if desc.is_concrete_invalid() {
                log!(log::MEMORY, &format!("Creating new level {} descriptor", i - 1));
                desc = L012Desc::new_table(self.alloc());
                self.get_mut(table)[va.level_index(i - 1)] = desc;
            }

            table = self.lookup(desc.concrete_address().unwrap())?;
            desc = self.get(table)[va.level_index(i)]
        }

        let table = self.lookup_l3(desc.concrete_address()?).unwrap_or_else(|| {
            log!(log::MEMORY, "Creating new level 3 descriptor");
            let l3_table = self.alloc_l3();
            self.get_mut(table)[va.level_index(2)] = L012Desc::new_table(l3_table);
            l3_table
        });
        self.get_l3_mut(table)[va.level_index(3)] = if let Some(solver) = maybe_invalid {
            L3Desc::page(page, attrs).or_invalid(solver)
        } else {
            L3Desc::page(page, attrs)
        };

        Some(())
    }

    pub fn identity_map<P: PageAttrs>(&mut self, level0: L012Index, page: u64, attrs: P) -> Option<()> {
        self.map::<B64, P>(level0, VirtualAddress::from_u64(page), page, attrs, None)
    }

    pub fn identity_or_invalid_map<B: BV, P: PageAttrs>(&mut self, level0: L012Index, page: u64, attrs: P, solver: &mut Solver<B>) -> Option<()> {
        self.map(level0, VirtualAddress::from_u64(page), page, attrs, Some(solver))
    }
    
    pub fn alias<B: BV>(&mut self, addr: u64, i: usize, pages: &[u64], solver: &mut Solver<B>) -> Option<()> {
        let table = self.lookup_l3(addr)?;
        self.get_l3_mut(table)[i] = L3Desc::new_symbolic(pages, S1PageAttrs::default(), solver);
        Some(())
    }

    pub fn freeze(&self) -> ImmutablePageTables {
        ImmutablePageTables { base_addr: self.base_addr, tables: self.tables.clone().into(), kind: self.kind }
    }
}

impl ImmutablePageTables {
    fn initial_descriptor<B: BV>(&self, addr: u64) -> Option<u64> {
        let table_addr = addr & !0xFFF;

        // Ensure page table reads are 8 bytes and aligned
        if (addr & 0b111) != 0 || table_addr < self.base_addr {
            return None;
        }

        let offset = ((addr & 0xFFF) >> 3) as usize;
        let i = ((table_addr - self.base_addr) >> 12) as usize;

        let desc: Val<B> = match self.tables.get(i) {
            Some(PageTable::L012(table)) => table[offset].into(),
            Some(PageTable::L3(table)) => Val::Bits(B::new(table[offset].initial_value(), 64)),
            None => return None,
        };

        match desc {
            Val::Bits(bv) => Some(bv.lower_u64()),
            _ => None,
        }
    }
}

impl<B: BV> CustomRegion<B> for ImmutablePageTables {
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
            Some(PageTable::L012(table)) => table[offset].into(),
            Some(PageTable::L3(table)) => table[offset].into(),
            None => return Err(ExecError::BadRead("page table index out of bounds")),
        };

        solver.add_event(Event::ReadMem {
            value: desc.clone(),
            read_kind,
            address: Val::Bits(B::from_u64(addr)),
            bytes,
            tag_value: None,
            kind: self.kind,
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
        let write_len_bits = length_bits(&write_desc, solver)?;

        // Ensure page table writes are also 8 bytes and aligned
        if (addr & 0b111) != 0 || write_len_bits != 64 || table_addr < self.base_addr {
            return Err(ExecError::BadWrite("unaligned page table write"));
        }

        let offset = ((addr & 0xFFF) >> 3) as usize;
        let i = ((table_addr - self.base_addr) >> 12) as usize;

        let current_desc: Val<B> = match self.tables.get(i) {
            Some(PageTable::L012(table)) => table[offset].into(),
            Some(PageTable::L3(table)) => table[offset].into(),
            None => return Err(ExecError::BadWrite("page table index out of bounds")),
        };

        let (skip_sat_check, query) = match (current_desc, &write_desc) {
            (Val::Bits(d1), Val::Bits(d2)) if d1 == *d2 => (true, Exp::Bool(true)),
            (Val::Bits(d1), Val::Symbolic(d2)) => (false, Exp::Eq(Box::new(smt_sbits(d1)), Box::new(Exp::Var(*d2)))),
            (Val::Symbolic(d1), Val::Bits(d2)) => (false, Exp::Eq(Box::new(Exp::Var(d1)), Box::new(smt_sbits(*d2)))),
            (Val::Symbolic(d1), Val::Symbolic(d2)) => (false, Exp::Eq(Box::new(Exp::Var(d1)), Box::new(Exp::Var(*d2)))),
            (Val::Bits(_), Val::Bits(_))=> return Err(ExecError::BadWrite("page table write trivially unsatisfiable")),
            (_, _) => return Err(ExecError::BadWrite("ill-typed descriptor")),
        };

        if skip_sat_check || solver.check_sat_with(&query) == SmtResult::Sat {
            let value = solver.declare_const(Ty::Bool);
            solver.add_event(Event::WriteMem {
                value,
                write_kind,
                address: Val::Bits(B::from_u64(addr)),
                data: write_desc,
                bytes: 8,
                tag_value: tag,
                kind: self.kind,
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

        let desc = self.initial_descriptor::<B>(desc_addr)?;

        Some(B::new(bzhi_u64(desc >> (desc_offset * 8), bytes * 8), bytes * 8))
    }

    fn memory_kind(&self) -> &'static str {
        self.kind
    }

    fn clone_dyn(&self) -> Box<dyn Send + Sync + CustomRegion<B>> {
        Box::new(self.clone())
    }
}

pub fn primop_setup_page_tables<B: BV>(
    _args: Vec<Val<B>>,
    _solver: &mut Solver<B>,
    _frame: &mut LocalFrame<B>,
) -> Result<Val<B>, ExecError> {
    Ok(Val::Unit)
}

#[cfg(test)]
mod tests {
    use isla_lib::bitvector::b64::B64;
    use isla_lib::smt::{Config, Context};

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
        let mut tbls = PageTables::new("test", 0x5000_0000);
        let tbl1 = tbls.alloc_l3();
        let tbl2 = tbls.alloc_l3();
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
        tables: &PageTables,
        level0: L012Index,
        va: VirtualAddress,
        solver: &mut Solver<B>,
    ) -> Option<Sym> {
        use Exp::*;

        let l0desc = tables.get(level0)[va.level_index(0)];

        let level1 = tables.lookup(l0desc.concrete_address()?)?;
        let l1desc = tables.get(level1)[va.level_index(1)];

        let level2 = tables.lookup(l1desc.concrete_address()?)?;
        let l2desc = tables.get(level2)[va.level_index(2)];

        let level3 = tables.lookup_l3(l2desc.concrete_address()?)?;
        let l3desc = tables.get_l3(level3)[va.level_index(3)];

        let page_addr = l3desc.symbolic_address(solver);
        let addr = solver.define_const(Bvadd(Box::new(Var(page_addr)), Box::new(bits64(va.page_offset(), 64))));

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

        let mut tables = PageTables::new("test", 0x5000_0000);
        let l3 = tables.alloc_l3();
        let l2 = tables.alloc();
        let l1 = tables.alloc();
        let l0 = tables.alloc();

        let va = VirtualAddress::from_u64(0xDEAD_BEEF);

        // Create a level 3 descriptor that can point at one of either two pages
        tables.get_l3_mut(l3)[va.level_index(3)] =
            L3Desc::new_symbolic(&[0x8000_0000, 0x8000_1000], S1PageAttrs::unknown(), &mut solver);
        tables.get_mut(l2)[va.level_index(2)] = L012Desc::new_table(l3);
        tables.get_mut(l1)[va.level_index(1)] = L012Desc::new_table(l2);
        tables.get_mut(l0)[va.level_index(0)] = L012Desc::new_table(l1);

        assert_eq!(Sat, solver.check_sat());

        // Translate our concrete virtual address to a symbolic
        // physical address, and check it could be in either page
        if let Some(pa) = simple_translation_table_walk(&tables, l0, va, &mut solver) {
            assert_eq!(Sat, solver.check_sat_with(&Eq(Box::new(Var(pa)), Box::new(bits64(0x8000_0EEF, 64)))));
            assert_eq!(Sat, solver.check_sat_with(&Eq(Box::new(Var(pa)), Box::new(bits64(0x8000_1EEF, 64)))));

            // Additionally, it  can't be anything other than those two addresses
            solver.add(Assert(Neq(Box::new(Var(pa)), Box::new(bits64(0x8000_0EEF, 64)))));
            solver.add(Assert(Neq(Box::new(Var(pa)), Box::new(bits64(0x8000_1EEF, 64)))));
            assert_eq!(Unsat, solver.check_sat());
        } else {
            panic!("simple_translation_table_walk failed")
        }
    }
}
