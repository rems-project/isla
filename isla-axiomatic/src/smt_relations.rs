// BSD 2-Clause License
//
// Copyright (c) 2022 Alasdair Armstrong
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

use isla_lib::bitvector::BV;
use isla_lib::ir::{Typedefs, Val};
use isla_lib::memory::Memory;
use isla_lib::smt::Event;

use isla_mml::accessor::{self, ModelEvent};
use isla_mml::memory_model::{ExpArena, MemoryModel, Name, Symtab};
use isla_mml::smt::{compile_memory_model, BitWidth, Sexp, SexpArena, SexpId};

use crate::axiomatic::relations;
use crate::axiomatic::{AxEvent, ExecutionInfo};
use crate::footprint_analysis::Footprint;
use crate::smt_model::pairwise::Pairs;

use isla_sexp::sexp;

fn smt_bitvec<B: BV>(val: &Val<B>, sexps: &mut SexpArena) -> SexpId {
    match val {
        Val::Symbolic(v) => sexps.alloc(Sexp::Symbolic(*v)),
        Val::Bits(bv) => sexps.alloc(Sexp::Bits(bv.to_vec())),
        _ => panic!("Non bitvector passed to smt_bitvec"),
    }
}

fn same_location<B: BV>(ev1: &AxEvent<B>, ev2: &AxEvent<B>, sexps: &mut SexpArena) -> SexpId {
    match (ev1.address(), ev2.address()) {
        (Some(Val::Symbolic(sym1)), Some(Val::Symbolic(sym2))) => {
            if sym1 == sym2 {
                sexps.bool_true
            } else {
                sexp!(sexps, [eq, [var, *sym1], [var, *sym2]])
            }
        }
        (Some(Val::Bits(bv)), Some(Val::Symbolic(sym))) | (Some(Val::Symbolic(sym)), Some(Val::Bits(bv))) => {
            sexp!(sexps, [eq, [var, *sym], [bits, bv.to_vec()]])
        }
        (Some(Val::Bits(bv1)), Some(Val::Bits(bv2))) => {
            if bv1 == bv2 {
                sexps.bool_true
            } else {
                sexp!(sexps, [eq, [bits, bv1.to_vec()], [bits, bv2.to_vec()]])
            }
        }
        (_, _) => sexps.bool_false,
    }
}

fn define_rel(name: Name, body: SexpId, sexps: &mut SexpArena, toplevel: &mut Vec<SexpId>) {
    toplevel.push(sexp!(
        sexps,
        [define_fun, [atom, name], [list, [ev1, sexps.event], [ev2, sexps.event]], sexps.bool_ty, body]
    ))
}

fn declare_rel(name: Name, body: SexpId, sexps: &mut SexpArena, toplevel: &mut Vec<SexpId>) {
    toplevel
        .push(sexp!(sexps, [declare_fun, [atom, name], [list, [ev1, sexps.event], [ev2, sexps.event]], sexps.bool_ty]));
    toplevel.push(sexp!(
        sexps,
        [
            assert,
            [
                forall,
                [list, [ev1, sexps.event], [ev2, sexps.event]],
                [eq, [list, [atom, name], sexps.ev1, sexps.ev2], body]
            ]
        ]
    ));
}

#[derive(Copy, Clone, Debug)]
pub enum RelationMode {
    Declare,
    Define,
}

fn rel(mode: RelationMode, name: Name, body: SexpId, sexps: &mut SexpArena, toplevel: &mut Vec<SexpId>) {
    match mode {
        RelationMode::Define => define_rel(name, body, sexps, toplevel),
        RelationMode::Declare => declare_rel(name, body, sexps, toplevel),
    }
}

fn basic_rel<B, F>(rel: F, events: &[AxEvent<B>], sexps: &mut SexpArena) -> SexpId
where
    B: BV,
    F: Fn(&AxEvent<B>, &AxEvent<B>) -> bool,
{
    let mut disj = Vec::new();
    for (ev1, ev2) in Pairs::from_slice(events).filter(|(ev1, ev2)| rel(ev1, ev2)) {
        disj.push(sexp!(sexps, [and, [eq, sexps.ev1, [atom, ev1.mm_name]], [eq, sexps.ev2, [atom, ev2.mm_name]],]))
    }
    sexps.alloc_or(disj)
}

fn condition_rel<B, F, G>(rel: F, events: &[AxEvent<B>], cond: G, sexps: &mut SexpArena) -> SexpId
where
    B: BV,
    F: Fn(&AxEvent<B>, &AxEvent<B>) -> bool,
    G: Fn(&AxEvent<B>, &AxEvent<B>, &mut SexpArena) -> SexpId,
{
    let mut disj = Vec::new();
    for (ev1, ev2) in Pairs::from_slice(events).filter(|(ev1, ev2)| rel(ev1, ev2)) {
        disj.push(sexp!(
            sexps,
            [and, [eq, sexps.ev1, [atom, ev1.mm_name]], [eq, sexps.ev2, [atom, ev2.mm_name]], |sexps| cond(
                ev1, ev2, sexps
            )]
        ))
    }
    sexps.alloc_or(disj)
}

fn dependency_rel<B: BV>(
    rel: relations::DepRel<B>,
    events: &[AxEvent<B>],
    thread_opcodes: &[Vec<Option<B>>],
    footprints: &HashMap<B, Footprint>,
    sexps: &mut SexpArena,
) -> SexpId {
    let mut disj = Vec::new();
    for (ev1, ev2) in Pairs::from_slice(events).filter(|(ev1, ev2)| rel(ev1, ev2, thread_opcodes, footprints)) {
        disj.push(sexp!(sexps, [and, [eq, sexps.ev1, [atom, ev1.mm_name]], [eq, sexps.ev2, [atom, ev2.mm_name]]]))
    }
    sexps.alloc_or(disj)
}

macro_rules! smt_basic_relation {
    ($r:ident, $smt_name:expr) => {
        pub fn $r<B: BV>(
            mode: RelationMode,
            events: &[AxEvent<B>],
            _: &[Vec<Option<B>>],
            _: &HashMap<B, Footprint>,
            symtab: &mut Symtab,
            sexps: &mut SexpArena,
            toplevel: &mut Vec<SexpId>,
        ) {
            let body = basic_rel(relations::$r, events, sexps);
            rel(mode, symtab.intern($smt_name), body, sexps, toplevel)
        }
    };
}

macro_rules! smt_condition_relation {
    ($r1:ident, $r2:path, $cond:expr, $smt_name:expr) => {
        pub fn $r1<B: BV>(
            mode: RelationMode,
            events: &[AxEvent<B>],
            _: &[Vec<Option<B>>],
            _: &HashMap<B, Footprint>,
            symtab: &mut Symtab,
            sexps: &mut SexpArena,
            toplevel: &mut Vec<SexpId>,
        ) {
            let body = condition_rel($r2, events, $cond, sexps);
            rel(mode, symtab.intern($smt_name), body, sexps, toplevel)
        }
    };
}

macro_rules! smt_dependency_relation {
    ($r:ident, $smt_name:expr) => {
        pub fn $r<B: BV>(
            mode: RelationMode,
            events: &[AxEvent<B>],
            thread_opcodes: &[Vec<Option<B>>],
            footprints: &HashMap<B, Footprint>,
            symtab: &mut Symtab,
            sexps: &mut SexpArena,
            toplevel: &mut Vec<SexpId>,
        ) {
            let body = dependency_rel(relations::$r, events, thread_opcodes, footprints, sexps);
            rel(mode, symtab.intern($smt_name), body, sexps, toplevel)
        }
    };
}

smt_basic_relation!(po, "po");
smt_basic_relation!(internal, "int");
smt_basic_relation!(external, "ext");
smt_basic_relation!(intra_instruction_ordered, "iio");
smt_basic_relation!(instruction_order, "instruction-order");
smt_basic_relation!(same_translation, "same-translation");

smt_condition_relation!(loc, relations::disjoint, same_location, "loc");
smt_condition_relation!(po_loc, relations::po, same_location, "po-loc");

smt_dependency_relation!(ctrl, "ctrl");
smt_dependency_relation!(addr, "addr");
smt_dependency_relation!(data, "data");
smt_dependency_relation!(rmw, "rmw");

pub fn trf<B: BV>(
    exec: &ExecutionInfo<B>,
    memory: &Memory<B>,
    typedefs: Typedefs,
    symtab: &mut Symtab,
    sexps: &mut SexpArena,
    toplevel: &mut Vec<SexpId>,
) -> Result<(), String> {
    let index_bitwidths = accessor::index_bitwidths(&exec.smt_events);

    // First, we create a tt-init predicate for the initial state of
    // the page tables, such that `(tt-init addr data)` is true if the
    // initial descriptor at address `addr` is `data`.
    {
        let tt_init = symtab.intern("tt-init");
        let addr_name = sexps.alloc(Sexp::Atom(symtab.intern("addr")));
        let data_name = sexps.alloc(Sexp::Atom(symtab.intern("data")));
        let bits64 = sexps.alloc_bitvec(64);

        let mut disj = Vec::new();
        for (ax_event, _, base_event) in exec.base_events() {
            if let Event::ReadMem { address: Val::Bits(address), bytes, .. } = base_event {
                if relations::is_translate(ax_event) && *bytes == 8 {
                    let data = memory
                        .read_initial(address.lower_u64(), 8)
                        .unwrap_or_else(|_| Val::Bits(B::from_u64(0)))
                        .as_bits()
                        .copied()
                        .ok_or_else(|| "Symbolic initial descriptor in page table read".to_string())?;

                    disj.push(sexp!(
                        sexps,
                        [and, [eq, addr_name, [bits, address.to_vec()]], [eq, data_name, [bits, data.to_vec()]],]
                    ))
                }
            }
        }
        let body = sexps.alloc_or(disj);

        toplevel.push(sexps.alloc_define_fun(
            tt_init,
            &[(addr_name, bits64), (data_name, bits64)],
            sexps.bool_ty,
            body,
        ));
    }

    // Now we can generate the tt-write set, such that `ev in
    // tt-write(addr, data)` if `ev` is a memory write that writes
    // `data` to the page tables.
    {
        let mut exps = ExpArena::new();
        let tt_write = concat!(
            "define tt-write(addr: bits(64), data: bits(64), ev: Event): bool =\n",
            "  (ev == IW & tt-init(addr, data))\n",
            "  (W(ev) & write_addr_data_of_64(ev, addr, data))"
        );
        let mm = MemoryModel::from_string(file!(), 0, tt_write, &mut exps, symtab).unwrap();
        compile_memory_model(&mm, typedefs, &exps, &vec![], sexps, symtab, toplevel).unwrap();
    }
    let tt_write = sexps.alloc(Sexp::Atom(symtab.intern("tt-write")));

    // Now we can finally build the trf relation
    {
        let mut disj = Vec::new();
        let mut translation_index_set = None;

        for ax_event in exec.smt_events.iter().filter(|e| relations::is_translate(e)) {
            let translate_name = sexps.alloc(Sexp::Atom(ax_event.mm_name));
            if let Some(ix) = ax_event.index_set {
                // If translations are indexed, then we assume they all share the same index set
                if let Some(previous_ix) = translation_index_set {
                    if ix != previous_ix {
                        return Err("Translate events have mismatching index sets".to_string());
                    }
                } else {
                    translation_index_set = Some(ix)
                }
                let width = index_bitwidths
                    .get(&ix)
                    .copied()
                    .ok_or_else(|| "Unknown bitwidth for translation index set".to_string())?;

                for (r, base_event) in ax_event.base_events().iter().copied().enumerate() {
                    if let Event::ReadMem { value, address, bytes, .. } = base_event {
                        if *bytes == 8 {
                            let corresponding_write =
                                sexps.alloc(Sexp::Atom(symtab.intern(&format!("{}_W{}", ax_event.name, r))));
                            toplevel.push(sexp!(sexps, [declare_const, corresponding_write, sexps.event]));
                            let value = smt_bitvec(value, sexps);
                            let address = smt_bitvec(address, sexps);
                            toplevel
                                .push(sexp!(sexps, [assert, [list, tt_write, address, value, corresponding_write]]));

                            disj.push(sexp!(
                                sexps,
                                [
                                    and,
                                    [eq, sexps.ev1, corresponding_write],
                                    [eq, sexps.ev2, translate_name],
                                    [eq, sexps.index, [bits, B::new(r as u64, width).to_vec()]]
                                ]
                            ))
                        }
                    }
                }
            } else {
                // If there's no index set, then each translate event must correspond to a sinlge base event
                let base_event = ax_event
                    .base()
                    .ok_or_else(|| "Unindexed translation event with multiple (or zero) base events".to_string())?;
                if let Event::ReadMem { value, address, bytes, .. } = base_event {
                    if *bytes == 8 {
                        let corresponding_write =
                            sexps.alloc(Sexp::Atom(symtab.intern(&format!("{}_W", ax_event.name))));
                        toplevel.push(sexps.alloc(Sexp::List(vec![
                            sexps.declare_const,
                            corresponding_write,
                            sexps.event,
                        ])));
                        let value = smt_bitvec(value, sexps);
                        let address = smt_bitvec(address, sexps);
                        let corresponding_write_valid =
                            sexps.alloc(Sexp::List(vec![tt_write, address, value, corresponding_write]));
                        toplevel.push(sexps.alloc(Sexp::List(vec![sexps.assert, corresponding_write_valid])));

                        disj.push(sexp!(
                            sexps,
                            [and, [eq, sexps.ev1, corresponding_write], [eq, sexps.ev2, translate_name]]
                        ))
                    }
                }
            }
        }
        let body = sexps.alloc_or(disj);
        toplevel.push(if let Some(ix) = translation_index_set {
            let index_ty = sexps.alloc(Sexp::BitVec(BitWidth::Index(ix)));
            sexps.alloc_define_fun(
                symtab.intern("trf"),
                &[(sexps.index, index_ty), (sexps.ev1, sexps.event), (sexps.ev2, sexps.event)],
                sexps.bool_ty,
                body,
            )
        } else {
            sexps.alloc_define_fun(
                symtab.intern("trf"),
                &[(sexps.ev1, sexps.event), (sexps.ev2, sexps.event)],
                sexps.bool_ty,
                body,
            )
        })
    }

    Ok(())
}
