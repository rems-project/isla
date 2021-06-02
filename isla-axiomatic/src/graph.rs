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

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};

use isla_lib::bitvector::BV;
use isla_lib::ir::*;
use isla_lib::smt::{Event, register_name_string};


use isla_cat::cat;

use crate::axiomatic::model::Model;
use crate::axiomatic::relations;
use crate::axiomatic::relations::is_translate;
use crate::axiomatic::{AxEvent, ExecutionInfo, Pairs, ThreadId};
use crate::footprint_analysis::Footprint;
use crate::litmus::instruction_from_objdump;
use crate::litmus::Litmus;
use crate::sexp::{InterpretError, SexpVal};

pub struct GraphOpts {
    pub include_registers: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphValue {
    prefix: String,
    address: Option<String>,
    bytes: String,
    value: Option<String>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphEvent {
    instr: Option<String>,
    opcode: String,
    po: usize,
    intra_instruction_order: usize,
    thread_id: ThreadId,
    name: String,
    value: Option<GraphValue>,
    color: Option<String>,
    style: String,
}

fn event_color<B: BV>(ev: &AxEvent<B>) -> Option<String> {
    match ev.base()? {
        Event::ReadMem { kind, .. } | Event::WriteMem { kind, .. } => {
            if kind == &"stage 1" {
                Some("darkslategray1".to_string())
            } else if kind == &"stage 2" {
                Some("wheat1".to_string())
            } else {
                None
            }
        }
        _ => None,
    }
}

impl GraphValue {
    pub fn from_fields(
        prefix: &str,
        address: Option<String>,
        bytes: u32,
        value: Option<String>,
    ) -> Self {
        GraphValue { prefix:prefix.to_string(), address: address, bytes: format!("{}", bytes), value: value }
    }

    pub fn from_vals<B: BV>(
        prefix: &str,
        address: &Val<B>,
        bytes: u32,
        value: &Val<B>,
    ) -> Self {
        let addr = if !address.is_symbolic() {
            let addrstr = address.as_bits().map(|bv| format!("#x{:x}", bv)).unwrap_or_else(|| "?".to_string());
            Some(addrstr)
        } else {
            None
        };

        let value = if !value.is_symbolic() {
            let valstr = value.as_bits().map(|bv| bv.signed().to_string()).unwrap_or_else(|| "?".to_string());
            Some(valstr)          
        } else {
            None
        };

        Self::from_fields(prefix, addr, bytes, value)
    }
}

impl GraphEvent {
    /// Create an event to display in a user-visible graph from an
    /// underlying axiomatic event. For display, we use the objdump
    /// output to find the human-readable assembly instruction
    pub fn from_axiomatic<'a, B: BV>(
        ev: &'a AxEvent<B>,
        objdump: &str,
        value: Option<GraphValue>,
    ) -> Self {
        let instr = instruction_from_objdump(&format!("{:x}", ev.opcode), objdump);
        GraphEvent {
            instr,
            opcode: format!("{}", ev.opcode),
            po: ev.po,
            intra_instruction_order: ev.intra_instruction_order,
            thread_id: ev.thread_id,
            name: ev.name.clone(),
            value: value,
            color: event_color(ev),
            style: (if is_translate(ev) { "dotted" } else { "solid" }).to_string(),
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphSet {
    pub name: String,
    pub elems: Vec<String>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphRelation {
    pub name: String,
    pub edges: Vec<(String, String)>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Graph {
    pub events: HashMap<String, GraphEvent>,  // EventName -> Event
    pub sets: Vec<GraphSet>,
    pub relations: Vec<GraphRelation>,
    pub show: Vec<String>,
}

static NEXT_COLOR: AtomicUsize = AtomicUsize::new(0);

fn extra_color() -> &'static str {
    let colors = [
        "seagreen",
        "steelblue",
        "violetred",
        "royalblue",
        "orangered",
        "navy",
        "hotpink",
        "green4",
        "dodgerblue",
        "chartreuse3",
        "darkorchid",
        "coral3",
        "darkolivegreen",
        "cyan4",
    ];
    let n = NEXT_COLOR.fetch_add(1, Ordering::SeqCst);
    colors[n % colors.len()]
}

fn relation_color(rel: &str) -> &'static str {
    match rel {
        "rf" => "crimson",
        "trf" => "maroon",
        "co" => "goldenrod",
        "fr" => "limegreen",
        "addr" => "blue2",
        "data" => "darkgreen",
        "ctrl" => "darkorange2",
        "rmw" => "firebrick4",
        "same-va-page" => "purple",
        "same-ipa-page" => "purple4",
        _ => extra_color(),
    }
}

impl fmt::Display for Graph {
    ///
    /// To build a digraph for each Graph we produce some neato-compatible dot
    /// with a fixed grid-like layout.
    /// 
    /// We layout something as follows:
    /// 
    ///         col0    col1    col2    col3    col4    col5    col6    col7
    /// 
    ///                            [Thread #0]
    /// 
    ///          [STR X0,[X1]]
    /// row0             [T]     [T]     [T]     [T]
    /// row1     [T]     [T]     [T]     [T]     [T]
    /// row2     [T]     [T]     [T]     [T]     [T]
    /// row3     [T]     [T]     [T]     [T]     [T]
    /// row4     [T]     [T]     [T]     [T]     [T]
    /// row5                                             [W]
    /// 
    /// 
    /// Nodes are written like [label]
    /// 
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "digraph Exec {{")?;
        writeln!(f, "  IW [label=\"Initial State\",shape=hexagon];")?;

        let mut thread_ids = HashSet::new();
        for ev in self.events.values() {
            thread_ids.insert(ev.thread_id);
        }

        for tid in thread_ids {
            writeln!(f, "  subgraph cluster{} {{", tid)?;
            writeln!(f, "    label=\"Thread #{}\"", tid)?;
            writeln!(f, "    style=dashed")?;
            writeln!(f, "    color=gray50")?;

            let mut lowest_po = None;
            let mut lowest_name = "";

            let events: Vec<&GraphEvent> = self.events.values().filter(|ev| ev.thread_id == tid).collect();

            for ev in &events {
                let instr = ev.instr.as_ref().unwrap_or(&ev.opcode);
                let color = if let Some(color) = &ev.color {
                    format!(",fillcolor={},style=filled", color)
                } else {
                    "".to_string()
                };

                if let Some(value) = &ev.value {
                    let q = "?".to_string();
                    let addrstr = value.address.as_ref().unwrap_or_else(|| &q);
                    let valstr = value.value.as_ref().unwrap_or_else(|| &q);
                    writeln!(f, "    {} [shape=box,label=\"{}\\l{}\"{}];", ev.name, instr, format!("{} {} ({}): {}", value.prefix, addrstr, value.bytes, valstr), color)?;
                } else {
                    writeln!(f, "    {} [style={},shape=box,label=\"{}\"{}];", ev.name, ev.style, instr, color)?;
                }

                if lowest_po.is_none() || ev.po < lowest_po.unwrap() {
                    lowest_po = Some(ev.po);
                    lowest_name = &ev.name;
                }
            }

            write!(f, "    ")?;
            for (i, ev) in events.iter().enumerate() {
                let last = i == events.len() - 1;
                let 
                write!(f, "{}{}", ev.name, if last { ";\n" } else { " -> " })?;
            }
            writeln!(f, "  }}")?;

            if lowest_po.is_some() {
                writeln!(f, "  IW -> {} [style=invis,constraint=true]", lowest_name)?;
            }
        }

        for to_show in &self.show {
            for rel in &self.relations {
                if rel.name == *to_show && !rel.edges.is_empty() {
                    let color = relation_color(&rel.name);
                    for (from, to) in &rel.edges {
                        if !(rel.name == "rf" && from == "IW") {
                            writeln!(
                                f,
                                "  {} -> {} [color={},label=\"  {}  \",fontcolor={}]",
                                from, to, color, rel.name, color
                            )?;
                        }
                    }
                }
            }
        }

        writeln!(f, "}}")
    }
}

#[derive(Debug, Clone)]
pub enum GraphError {
    /// Will be caused if we cannot parse the SMT solver (z3) output
    /// as a valid S-expression model.
    SmtParseError,
    /// Will be caused if we fail to interpret part of the model.
    InterpretError(InterpretError),
}

impl fmt::Display for GraphError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use GraphError::*;
        match self {
            SmtParseError => write!(f, "Failed to parse smt model"),
            InterpretError(err) => write!(f, "{}", err),
        }
    }
}

impl Error for GraphError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

// produce a (concrete) Val which represnets the name of the
// register + field
fn regname_val<'ir, B: BV>(
    ev: &AxEvent<B>,
    symtab: &'ir Symtab,
) -> Option<Val<B>> {
    let regnamestr = register_name_string(ev.base, symtab);
    regnamestr.map(Val::String)
}

/// generate an initial graph from a candidate
/// without any symbolic parts filled in
fn concrete_graph_from_candidate<'ir, B: BV>(
    exec: &ExecutionInfo<B>,
    footprints: &HashMap<B, Footprint>,
    litmus: &Litmus<B>,
    cat: &cat::Cat<cat::Ty>,
    _ifetch: bool,
    opts: &GraphOpts,
    symtab: &'ir Symtab,
) -> Result<Graph, GraphError> {
    // collect relations from the candidate
    let mut relations: Vec<GraphRelation> = Vec::new();
    let footprint_relations: [(&str, relations::DepRel<B>); 5] =
        [("po", |ev1, ev2, _, _| relations::po(ev1, ev2)), ("addr", relations::addr), ("data", relations::data), ("ctrl", relations::ctrl), ("rmw", relations::rmw)];

    for (name, rel) in footprint_relations.iter() {
        let edges: Vec<(&AxEvent<B>, &AxEvent<B>)> = Pairs::from_slice(&exec.events)
            .filter(|(ev1, ev2)| rel(ev1, ev2, &exec.thread_opcodes, footprints))
            .collect();
        relations.push(GraphRelation {
            name: (*name).to_string(),
            edges: edges.iter().map(|(from, to)| (from.name.clone(), to.name.clone())).collect(),
        })
    }

    // there is no z3 model to interpret the values from
    // so we instead look through the candidate to see what information
    // we can show to the user for debugging help
    let mut events: HashMap<String, GraphEvent> = HashMap::new();

    for event in exec.events.iter() {
        match event.base {
            Event::ReadMem { value, address, bytes, .. } => {
                let event_name = if event.is_ifetch { "IF" } else { "R" };
                let graphvalue = GraphValue::from_vals(event_name, address, *bytes, value);

                events.insert(
                    event.name.clone(),
                    GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                );
            },
            Event::WriteMem { data, address, bytes, .. } => {
                let graphvalue = GraphValue::from_vals("W", address, *bytes, data);

                events.insert(
                    event.name.clone(),
                    GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                );
            },
            Event::ReadReg(_, _, val) => {
                if opts.include_registers {
                    let fieldval = regname_val(event, symtab).unwrap();
                    let graphvalue = GraphValue::from_vals("Rr", &fieldval, 8, val);
                    events.insert(
                        event.name.clone(),
                        GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                    );
                }
            },
            Event::WriteReg(_, _, val) => {
                if opts.include_registers {
                let fieldval = regname_val(event, symtab).unwrap();
                let graphvalue = GraphValue::from_vals("Wr", &fieldval, 8, val);
                events.insert(
                    event.name.clone(),
                    GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                );
            }
            },
            _ => (),
        }
    }

    Ok(Graph {
        events: events,
        sets: vec![],
        relations,
        show: cat.shows(),
    })
}

/// run an interpretation function over the symbolic events
/// to generate new nodes in the graph
fn update_graph_symbolic_events<F, B>(
    exec: &ExecutionInfo<B>,
    litmus: &Litmus<B>,
    opts: &GraphOpts,
    mut g: Graph,
    interpret: &mut F,
) -> Graph
where
    B: BV,
    F: FnMut(GraphValue, &str, &str, &Val<B>, u32, &Val<B>) -> GraphValue,
{
    for event in exec.events.iter() {
        println!("update from symbolic {}: {:?}", event.name, event.base);
        match event.base {
            Event::ReadMem { value, address, bytes, .. } => {
                if value.is_symbolic() || address.is_symbolic() {
                    // the event will already exist in the graph
                    // but some of the fields may be empty
                    let gev = g.events.remove(&event.name).unwrap();
                    let gval = gev.value.unwrap();
                    let event_kind_name = if event.is_ifetch { "IF" } else { "R" };
                    let graphvalue = interpret(gval, &event.name, event_kind_name, address, *bytes, value);
                    g.events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
                }
            },
            Event::WriteMem { data, address, bytes, .. } => {
                if data.is_symbolic() || address.is_symbolic() {
                    let gevent = g.events.remove(&event.name).unwrap();
                    let gval = gevent.value.unwrap();
                    let graphvalue = interpret(gval, &event.name, "W", address, *bytes, data);
                    g.events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
                }
            },
            Event::ReadReg(_, _, val) => {
                if opts.include_registers && val.is_symbolic() {
                    let gevent = g.events.remove(&event.name).unwrap();
                    let gval = gevent.value.unwrap();
                    let tempval: Val<B> = Val::Unit;
                    let graphvalue = interpret(gval, &event.name, "Rr", &tempval, 8, val);
                    g.events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
                }
            },
            Event::WriteReg(_, _, val) => {
                if opts.include_registers && val.is_symbolic() {
                    let gevent = g.events.remove(&event.name).unwrap();
                    let gval = gevent.value.unwrap();
                    let tempval: Val<B> = Val::Unit;
                    let graphvalue = interpret(gval, &event.name, "Wr", &tempval, 8, val);
                    g.events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
                }
            },
            _ => (),
        }
    };

    g
}

/// Generate a graph from just the candidate, showing the symbolic information as symbols
/// this graph won't contain definitions of the relations,  but just the events
pub fn graph_from_unsat<'ir, B: BV>(
    exec: &ExecutionInfo<B>,
    footprints: &HashMap<B, Footprint>,
    litmus: &Litmus<B>,
    cat: &cat::Cat<cat::Ty>,
    ifetch: bool,
    opts: &GraphOpts,
    symtab: &'ir Symtab,
) -> Result<Graph, GraphError> {
    match concrete_graph_from_candidate(exec, footprints, litmus, cat, ifetch, opts, symtab) {
        Err(e) => Err(e),
        Ok(g) => Ok(
            update_graph_symbolic_events(
                exec,
                litmus,
                opts,
                g,
                &mut |gv, _ev, prefix, address, bytes, value| {
                    // so just fill those fields that were empty in
                    GraphValue::from_fields(prefix, gv.address.or_else(|| Some(address.to_string(symtab))), bytes, gv.value.or_else(|| Some(value.to_string(symtab))))
                }
            )
        ),
    }
}

/// Generate a graph from the output of a Z3 invocation that returned sat.
pub fn graph_from_z3_output<'ir, B: BV>(
    exec: &ExecutionInfo<B>,
    footprints: &HashMap<B, Footprint>,
    z3_output: &str,
    litmus: &Litmus<B>,
    cat: &cat::Cat<cat::Ty>,
    ifetch: bool,
    opts: &GraphOpts,
    symtab: &'ir Symtab,
) -> Result<Graph, GraphError> {
    use GraphError::*;

    let mut event_names: Vec<&str> = exec.events.iter().map(|ev| ev.name.as_ref()).collect();
    event_names.push("IW");

    // parse the Z3 output to produce a Model
    // that allows us to lookup the values z3 produced
    // later in the code
    let model_buf = &z3_output[3..];
    let mut model = Model::<B>::parse(&event_names, model_buf).ok_or(SmtParseError)?;

    match concrete_graph_from_candidate(exec, footprints, litmus, cat, ifetch, opts, symtab) {
        Err(e) => Err(e),
        Ok(g) => Ok(
            update_graph_symbolic_events(
                exec,
                litmus,
                opts,
                g,
                &mut |gv, ev, prefix, _address, bytes, _value| {
                    let val =
                        match gv.value {
                            Some(v) => Some(v),
                            None => Some(
                                String::from(
                                    &model
                                    .interpret(&format!("{}:value", ev), &[])
                                    .map(SexpVal::into_int_string)
                                    .unwrap_or_else(|_| "?".to_string())
                                )
                            ),
                        };

                    let addr =
                        match gv.address {
                            Some(v) => Some(v),
                            None => Some(
                                String::from(
                                    &model
                                    .interpret(&format!("{}:address", ev), &[])
                                    .map(SexpVal::into_truncated_string)
                                    .unwrap_or_else(|_| "?".to_string())
                                )
                            ),
                        };

                    // so just fill those fields that were empty in
                    GraphValue::from_fields(prefix, addr, bytes, val)
                }
            )
        ),
    }
}
