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

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;

use isla_lib::bitvector::BV;
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::smt::{register_name_string, Event};

use crate::axiomatic::relations;
use crate::axiomatic::{AxEvent, ExecutionInfo};
use crate::footprint_analysis::Footprint;
use crate::litmus::Litmus;
use crate::sexp::SexpVal;
use crate::smt_model::{pairwise::Pairs, Model, ModelParseError};

mod ascii_backend;
pub mod graph_events;
pub mod graph_opts;
pub mod grid_layout;
mod gv_backend;

pub use ascii_backend::draw_graph_ascii;
pub use graph_events::*;
pub use graph_opts::*;
pub use gv_backend::draw_graph_gv;

#[derive(Debug)]
pub enum GraphError<'s> {
    /// Will be caused if we cannot parse the SMT solver (z3) output
    /// as a valid S-expression model.
    ModelError(ModelParseError<'s>),
}

impl<'s> fmt::Display for GraphError<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ModelError(err) => {
                write!(f, "Failed to parse smt model: ")?;
                err.fmt(f)
            }
        }
    }
}

impl<'s> Error for GraphError<'s> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        // TODO: would like to return the inner error, but ModelParseError might contain a non-static reference to a Tok<'_> ...
        None
    }
}

// produce a (concrete) Val which represnets the name of the
// register + field
fn regname_val<B: BV>(ev: &Event<B>, symtab: &Symtab) -> Option<Val<B>> {
    let regnamestr = register_name_string(ev, symtab);
    regnamestr.map(Val::String)
}

/// get tag (T | R | IF | etc) from a read event
/// isla simply outputs one ReadMem() event for all of them.
fn tag_from_read_event<'a, B: BV>(ev: &AxEvent<B>) -> &'a str {
    if ev.is_ifetch {
        "IF"
    } else if relations::is_translate(ev) {
        "T"
    } else {
        "R"
    }
}

/// generate an initial graph from a candidate
/// without any symbolic parts filled in
#[allow(clippy::too_many_arguments)]
fn concrete_graph_from_candidate<'m, B: BV>(
    exec: &ExecutionInfo<B>,
    names: GraphValueNames<B>,
    _footprints: &HashMap<B, Footprint>,
    litmus: &Litmus<B>,
    _ifetch: bool,
    opts: &GraphOpts,
    symtab: &Symtab,
) -> Result<Graph, GraphError<'m>> {
    // there is no z3 model to interpret the values from
    // so we instead look through the candidate to see what information
    // we can show to the user for debugging help
    let mut events: HashMap<String, GraphEvent> = HashMap::new();

    let combined_events: Vec<_> = if opts.debug {
        exec.smt_events.iter().chain(exec.other_events.iter()).collect()
    } else {
        exec.smt_events.iter().collect()
    };

    // this re-computes the Translations even though the smt generation ages ago already did it
    // but that's long gone and it's not a big deal (hopefully!)
    let _translations = exec.translations();

    for event in combined_events {
        let ev = event.base.last();
        match ev {
            Some(Event::ReadMem { value, address, bytes, .. }) => {
                let event_name = tag_from_read_event(event);
                let graphvalue = GraphValue::from_vals(event_name, Some(address), *bytes, Some(value));
                events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
            }
            Some(Event::WriteMem { data, address, bytes, .. }) => {
                let graphvalue = GraphValue::from_vals("W", Some(address), *bytes, Some(data));
                events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
            }
            Some(Event::ReadReg(_name, _, val)) => {
                let regnamestr = register_name_string(ev.unwrap(), symtab).unwrap();
                if opts.debug && opts.show_regs.contains(&regnamestr) {
                    let fieldval = regname_val(event.base().unwrap(), symtab).unwrap();
                    let graphvalue = GraphValue::from_vals("Rreg", Some(&fieldval), 8, Some(val));
                    events.insert(
                        event.name.clone(),
                        GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)),
                    );
                };
            }
            Some(Event::WriteReg(_name, _, val)) => {
                let regnamestr = register_name_string(ev.unwrap(), symtab).unwrap();
                if opts.debug && opts.show_regs.contains(&regnamestr) {
                    let fieldval = regname_val(event.base().unwrap(), symtab).unwrap();
                    let graphvalue = GraphValue::from_vals("Wreg", Some(&fieldval), 8, Some(val));
                    events.insert(
                        event.name.clone(),
                        GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)),
                    );
                };
            }
            Some(Event::Abstract { .. }) => {
                // abstract events cover everything else in the interface...
                events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, None));
            }
            _ => {
                if opts.debug {
                    events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, None));
                } else {
                    panic!("concrete_graph_from_candidate unknown graph event: {:?}", event);
                }
            }
        }
    }

    Ok(Graph {
        events,
        sets: vec![],
        relations: vec![],
        show: vec![],
        opts: opts.clone(),
        litmus_opts: litmus.graph_opts.clone(),
        names: names.to_u64(),
    })
}

/// run an interpretation function over the symbolic events
/// to generate new nodes in the graph
#[allow(clippy::too_many_arguments)]
fn update_graph_symbolic_events<'m, 'ev, Fev, Frel, B>(
    exec: &'ev ExecutionInfo<B>,
    litmus: &Litmus<B>,
    ifetch: bool,
    opts: &GraphOpts,
    mut model: Option<Model<'_, 'ev, B>>,
    mut g: Graph,
    interpret: Fev,
    interpret_rel: Frel,
) -> Graph
where
    B: BV,
    Fev: Fn(&mut Option<Model<'_, 'ev, B>>, GraphValue, &str, &str, &Val<B>, u32, &Val<B>) -> GraphValue,
    Frel: Fn(&mut Option<Model<'_, 'ev, B>>, &str) -> GraphRelation,
{
    let mut builtin_relations = vec!["iio", "po", "rf", "co", "addr", "data", "ctrl"];
    if ifetch {
        builtin_relations.push("fpo");
        builtin_relations.push("irf");
    }

    let events: Vec<_> = if opts.debug {
        exec.smt_events.iter().chain(exec.other_events.iter()).collect()
    } else {
        exec.smt_events.iter().collect()
    };

    let mut event_names: Vec<&'ev str> = events.iter().map(|ev| ev.name.as_ref()).collect();
    event_names.push("IW");

    // collect all relations from the litmus file, builtins and from the cat `show`s
    // nubing away duplicates
    log!(log::GRAPH, "collecting and interpreting show relations from z3 model");

    // if the cmdline has args, those take priority
    // otherwise if the litmus specifies a meta graph section with shows, use those
    // otherwise just use the `show ...` commands from the cat itself
    let cmdline_shows: Vec<String> = opts.shows.clone().unwrap_or_default();
    let litmus_shows: Vec<String> = litmus.graph_opts.shows.clone().unwrap_or_default();
    let cat_shows: Option<Vec<String>> = None;
    let all_rels: HashSet<&str> = if !cmdline_shows.is_empty() {
        cmdline_shows.iter().map(String::as_str).collect()
    } else if !litmus_shows.is_empty() {
        litmus_shows.iter().map(String::as_str).collect()
    } else if cat_shows.is_some() {
        todo!("shows from cat file")
    } else {
        builtin_relations.into_iter().collect()
    };

    log!(log::GRAPH, format!("collected {} shows: {:?}", all_rels.len(), all_rels));

    for rel in all_rels {
        g.relations.push(interpret_rel(&mut model, rel).simplify());
    }

    log!(log::GRAPH, "finished interpreting, now populating remaining symbolic entries in graph");
    for event in events {
        match event.base.last() {
            Some(Event::ReadMem { value, address, bytes, .. }) => {
                if value.is_symbolic() || address.is_symbolic() {
                    // the event will already exist in the graph
                    // but some of the fields may be empty
                    let gev = g.events.remove(&event.name).unwrap();
                    let gval = gev.value.unwrap();
                    let event_kind_name = tag_from_read_event(event);
                    let graphvalue = interpret(&mut model, gval, &event.name, event_kind_name, address, *bytes, value);
                    g.events.insert(
                        event.name.clone(),
                        GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)),
                    );
                }
            }
            Some(Event::WriteMem { data, address, bytes, .. }) => {
                if data.is_symbolic() || address.is_symbolic() {
                    let gevent = g.events.remove(&event.name).unwrap();
                    let gval = gevent.value.unwrap();
                    let graphvalue = interpret(&mut model, gval, &event.name, "W", address, *bytes, data);
                    g.events.insert(
                        event.name.clone(),
                        GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)),
                    );
                }
            }
            Some(Event::ReadReg(_, _, val)) => {
                if opts.debug && val.is_symbolic() {
                    if let Some(gevent) = g.events.remove(&event.name) {
                        let gval = gevent.value.unwrap();
                        let tempval: Val<B> = Val::Unit;
                        let graphvalue = interpret(&mut model, gval, &event.name, "Rreg", &tempval, 8, val);
                        g.events.insert(
                            event.name.clone(),
                            GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)),
                        );
                    }
                }
            }
            Some(Event::WriteReg(_, _, val)) => {
                if opts.debug && val.is_symbolic() {
                    if let Some(gevent) = g.events.remove(&event.name) {
                        let gval = gevent.value.unwrap();
                        let tempval: Val<B> = Val::Unit;
                        let graphvalue = interpret(&mut model, gval, &event.name, "Wreg", &tempval, 8, val);
                        g.events.insert(
                            event.name.clone(),
                            GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)),
                        );
                    }
                }
            }
            _ => (),
        }
    }

    log!(log::GRAPH, "updating graph event kinds");
    update_event_kinds(&mut g.events);
    g
}

/// Generate a graph from just the candidate, showing the symbolic information as symbols
/// this graph won't contain definitions of the relations,  but just the events
#[allow(clippy::too_many_arguments)]
pub fn graph_from_unsat<'ir, 'ev, 'm, B: BV>(
    exec: &'ev ExecutionInfo<B>,
    names: GraphValueNames<B>,
    footprints: &HashMap<B, Footprint>,
    litmus: &Litmus<B>,
    ifetch: bool,
    opts: &GraphOpts,
    shared_state: &'ir SharedState<B>,
) -> Result<Graph, GraphError<'m>> {
    let footprint_relations: [(&str, relations::DepRel<B>); 6] = [
        ("po", |ev1, ev2, _, _| relations::po(ev1, ev2)),
        ("iio", |ev1, ev2, _, _| relations::intra_instruction_ordered(ev1, ev2)),
        ("addr", relations::addr),
        ("data", relations::data),
        ("ctrl", relations::ctrl),
        ("rmw", relations::rmw),
    ];

    let footprint_relations: HashMap<&str, relations::DepRel<B>> = footprint_relations.iter().cloned().collect();

    let combined_events: Vec<&'ev AxEvent<B>> = if opts.debug {
        exec.smt_events.iter().chain(exec.other_events.iter()).collect()
    } else {
        exec.smt_events.iter().collect()
    };

    log!(log::GRAPH, "generating graph from unsatisifable output");

    match concrete_graph_from_candidate(exec, names, footprints, litmus, ifetch, opts, &shared_state.symtab) {
        Err(e) => Err(e),
        Ok(g) => Ok(update_graph_symbolic_events(
            exec,
            litmus,
            ifetch,
            opts,
            None,
            g,
            |_m, gv, _ev, prefix, address, bytes, value| {
                // so just fill those fields that were empty in
                GraphValue::from_fields(
                    prefix,
                    gv.address.or_else(|| Some(address.to_string(shared_state))),
                    gv.virtual_address,
                    bytes,
                    gv.value.or_else(|| Some(value.to_string(shared_state))),
                )
            },
            |_m, rel_name| {
                let (rel_name, relty) = parse_relname_opt(rel_name);
                // when the smt was unsatisfiable we only have the relations from the footprint
                // we can still enumerate those and draw them
                if let Some(rel) = footprint_relations.get(rel_name) {
                    let edges: HashSet<(String, String)> = Pairs::from_slice(combined_events.as_slice())
                        .filter(|(ev1, ev2)| rel(ev1, ev2, &exec.thread_opcodes, footprints))
                        .map(|(ev1, ev2)| (ev1.name.clone(), ev2.name.clone()))
                        .collect();

                    GraphRelation { name: (*rel_name).to_string(), ty: relty, edges: edges.clone(), all_edges: edges }
                } else {
                    GraphRelation {
                        name: (*rel_name).to_string(),
                        ty: relty,
                        edges: HashSet::new(),
                        all_edges: HashSet::new(),
                    }
                }
            },
        )),
    }
}

/// Generate a graph from the output of a Z3 invocation that returned sat.
#[allow(clippy::too_many_arguments)]
pub fn graph_from_z3_output<'m, B: BV>(
    exec: &ExecutionInfo<B>,
    names: GraphValueNames<B>,
    footprints: &HashMap<B, Footprint>,
    z3_output: &'m str,
    litmus: &Litmus<B>,
    ifetch: bool,
    opts: &GraphOpts,
    symtab: &Symtab,
) -> Result<Graph, GraphError<'m>> {
    let combined_events: Vec<_> = if opts.debug {
        exec.smt_events.iter().chain(exec.other_events.iter()).collect()
    } else {
        exec.smt_events.iter().collect()
    };
    let mut event_names: Vec<&str> = combined_events.iter().map(|ev| ev.name.as_ref()).collect();
    event_names.push("IW");

    // parse the Z3 output to produce a Model
    // that allows us to lookup the values z3 produced
    // later in the code
    let model_buf: &str = &z3_output[3..];
    let model = Model::<B>::parse(&event_names, model_buf).map_err(GraphError::ModelError)?;

    log!(log::GRAPH, "generating graph from satisfiable model");

    match concrete_graph_from_candidate(exec, names, footprints, litmus, ifetch, opts, symtab) {
        Err(e) => Err(e),
        Ok(g) => Ok(update_graph_symbolic_events(
            exec,
            litmus,
            ifetch,
            opts,
            Some(model),
            g,
            |m, gv, ev, prefix, _address, bytes, _value| {
                if let Some(m) = m {
                    let val = match gv.value {
                        Some(v) => Some(v),
                        None => Some(
                            m.interpret(&format!("{}:value", ev), &[])
                                .map(SexpVal::convert_into_bits)
                                .map(|ob| ob.expect("expected numeric value"))
                                .map(|b| str_from_value(&Val::Bits(b)))
                                .unwrap_or_else(|_| "?".to_string()),
                        ),
                    };

                    let addr = match gv.address {
                        Some(v) => Some(v),
                        None => Some(
                            m.interpret(&format!("{}:address", ev), &[])
                                .map(SexpVal::convert_into_bits)
                                .map(|ob| ob.expect("expected numeric address"))
                                .map(|b| str_from_value(&Val::Bits(b)))
                                .unwrap_or_else(|_| "?".to_string()),
                        ),
                    };

                    // so just fill those fields that were empty in
                    GraphValue::from_fields(prefix, addr, gv.virtual_address, bytes, val)
                } else {
                    unreachable!()
                }
            },
            |m, rel_name| {
                let (rel_name, relty) = parse_relname_opt(rel_name);
                if let Some(m) = m {
                    match m.interpret_rel(rel_name) {
                        Ok(edges) => {
                            let edges: HashSet<(String, String)> =
                                edges.iter().map(|(from, to)| ((*from).to_string(), (*to).to_string())).collect();
                            GraphRelation {
                                name: (*rel_name).to_string(),
                                ty: relty,
                                edges: edges.clone(),
                                all_edges: edges,
                            }
                        }
                        Err(err) => {
                            eprintln!("Failed to interpret relation '{}': {}", rel_name, err);
                            GraphRelation {
                                name: (*rel_name).to_string(),
                                ty: relty,
                                edges: HashSet::new(),
                                all_edges: HashSet::new(),
                            }
                        }
                    }
                } else {
                    unreachable!()
                }
            },
        )),
    }
}
