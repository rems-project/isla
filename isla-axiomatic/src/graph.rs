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
use isla_lib::smt::Event;

use isla_cat::cat;

use crate::axiomatic::model::Model;
use crate::axiomatic::relations;
use crate::axiomatic::{AxEvent, ExecutionInfo, Pairs, ThreadId};
use crate::footprint_analysis::Footprint;
use crate::litmus::instruction_from_objdump;
use crate::litmus::Litmus;
use crate::sexp::{InterpretError, SexpVal};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphEvent {
    instr: Option<String>,
    opcode: String,
    po: usize,
    thread_id: ThreadId,
    name: String,
    value: Option<String>,
    color: Option<String>,
}

fn event_color<B: BV>(ev: &AxEvent<B>) -> Option<String> {
    match ev.base {
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

impl GraphEvent {
    /// Create an event to display in a user-visible graph from an
    /// underlying axiomatic event. For display, we use the objdump
    /// output to find the human-readable assembly instruction, and
    /// get values read/written by memory events as an event name ->
    /// read/write description map.
    pub fn from_axiomatic<'a, B: BV>(
        ev: &'a AxEvent<B>,
        objdump: &str,
        rw_values: &mut HashMap<String, String>,
    ) -> Self {
        let instr = instruction_from_objdump(&format!("{:x}", ev.opcode), objdump);
        GraphEvent {
            instr,
            opcode: format!("{}", ev.opcode),
            po: ev.po,
            thread_id: ev.thread_id,
            name: ev.name.clone(),
            value: rw_values.remove(&ev.name),
            color: event_color(ev),
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
    pub events: Vec<GraphEvent>,
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
        "co" => "goldenrod",
        "fr" => "limegreen",
        "addr" => "blue2",
        "data" => "darkgreen",
        "ctrl" => "darkorange2",
        "rmw" => "firebrick4",
        _ => extra_color(),
    }
}

impl fmt::Display for Graph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "digraph Exec {{")?;
        writeln!(f, "  IW [label=\"Initial State\",shape=hexagon];")?;

        let mut thread_ids = HashSet::new();
        for ev in &self.events {
            thread_ids.insert(ev.thread_id);
        }

        for tid in thread_ids {
            writeln!(f, "  subgraph cluster{} {{", tid)?;
            writeln!(f, "    label=\"Thread #{}\"", tid)?;
            writeln!(f, "    style=dashed")?;
            writeln!(f, "    color=gray50")?;

            let mut lowest_po = None;
            let mut lowest_name = "";

            let events: Vec<&GraphEvent> = self.events.iter().filter(|ev| ev.thread_id == tid).collect();

            for ev in &events {
                let instr = ev.instr.as_ref().unwrap_or(&ev.opcode);
                let color = if let Some(color) = &ev.color {
                    format!(",fillcolor={},style=filled", color)
                } else {
                    "".to_string()
                };
                
                if let Some(value) = &ev.value {
                    writeln!(f, "    {} [shape=box,label=\"{}\\l{}\"{}];", ev.name, instr, value, color)?;
                } else {
                    writeln!(f, "    {} [shape=box,label=\"{}\"{}];", ev.name, instr, color)?;
                }

                if lowest_po.is_none() || ev.po < lowest_po.unwrap() {
                    lowest_po = Some(ev.po);
                    lowest_name = &ev.name;
                }
            }

            write!(f, "    ")?;
            for (i, ev) in events.iter().enumerate() {
                let last = i == events.len() - 1;
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
                    for (from, to) in &rel.edges {
                        if !(rel.name == "rf" && from == "IW") {
                            let color = relation_color(&rel.name);
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

/// Generate a graph from the output of a Z3 invocation that returned sat.
pub fn graph_from_z3_output<B: BV>(
    exec: ExecutionInfo<B>,
    footprints: &HashMap<B, Footprint>,
    z3_output: &str,
    litmus: &Litmus<B>,
    cat: &cat::Cat<cat::Ty>,
    ifetch: bool,
) -> Result<Graph, GraphError> {
    use GraphError::*;

    let mut event_names: Vec<&str> = exec.events.iter().map(|ev| ev.name.as_ref()).collect();
    event_names.push("IW");
    let model_buf = &z3_output[3..];
    let mut model = Model::<B>::parse(&event_names, model_buf).ok_or(SmtParseError)?;

    // We want to collect all the relations that were found by the SMT solver as part of the
    // model, as well as the addr/data/ctrl etc raltions we passed as input to the solver so we
    // can send them back to the client to be drawn.
    let mut relations: Vec<GraphRelation> = Vec::new();

    let footprint_relations: [(&str, relations::DepRel<B>); 4] =
        [("addr", relations::addr), ("data", relations::data), ("ctrl", relations::ctrl), ("rmw", relations::rmw)];

    for (name, rel) in footprint_relations.iter() {
        let edges: Vec<(&AxEvent<B>, &AxEvent<B>)> = Pairs::from_slice(&exec.events)
            .filter(|(ev1, ev2)| rel(ev1, ev2, &exec.thread_opcodes, footprints))
            .collect();
        relations.push(GraphRelation {
            name: (*name).to_string(),
            edges: edges.iter().map(|(from, to)| (from.name.clone(), to.name.clone())).collect(),
        })
    }

    let mut builtin_relations = vec!["rf", "co"];
    if ifetch {
        builtin_relations.push("irf")
    }

    for rel in cat.relations().iter().chain(builtin_relations.iter()) {
        let edges = model.interpret_rel(rel, &event_names).map_err(InterpretError)?;
        relations.push(GraphRelation {
            name: (*rel).to_string(),
            edges: edges.iter().map(|(from, to)| ((*from).to_string(), (*to).to_string())).collect(),
        })
    }

    // Now we want to get the memory read and write values for each event
    let mut rw_values: HashMap<String, String> = HashMap::new();

    for event in exec.events.iter() {
        fn interpret<B: BV>(
            model: &mut Model<B>,
            ev: &str,
            prefix: &str,
            value: &Val<B>,
            bytes: u32,
            address: &Val<B>,
        ) -> String {
            let value = if value.is_symbolic() {
                model
                    .interpret(&format!("{}:value", ev), &[])
                    .map(SexpVal::into_int_string)
                    .unwrap_or_else(|_| "?".to_string())
            } else {
                value.as_bits().map(|bv| bv.signed().to_string()).unwrap_or_else(|| "?".to_string())
            };

            let address = if address.is_symbolic() {
                model
                    .interpret(&format!("{}:address", ev), &[])
                    .map(SexpVal::into_truncated_string)
                    .unwrap_or_else(|_| "?".to_string())
            } else {
                address.as_bits().map(|bv| format!("#x{:x}", bv)).unwrap_or_else(|| "?".to_string())
            };

            format!("{} {} ({}): {}", prefix, address, bytes, value)
        }

        match event.base {
            Event::ReadMem { value, address, bytes, .. } => {
                rw_values.insert(
                    event.name.clone(),
                    interpret(
                        &mut model,
                        &event.name,
                        if event.is_ifetch { "IF" } else { "R" },
                        value,
                        *bytes,
                        address,
                    ),
                );
            }
            Event::WriteMem { data, address, bytes, .. } => {
                rw_values.insert(event.name.clone(), interpret(&mut model, &event.name, "W", data, *bytes, address));
            }
            _ => (),
        }
    }

    Ok(Graph {
        events: exec.events.iter().map(|ev| GraphEvent::from_axiomatic(ev, &litmus.objdump, &mut rw_values)).collect(),
        sets: vec![],
        relations,
        show: cat.shows(),
    })
}
