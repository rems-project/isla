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
pub enum GraphEventKind {
    Ifetch,
    ReadMem,
    WriteMem,
    TranslateS1(usize),
    TranslateS2(usize),
    TranslateS2inS1(usize),
    WriteS1Entry,
    WriteS2Entry,
}

/// to render the events
/// we must give each a name
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphEvent {
    instr: Option<String>,
    opcode: String,
    po: usize,
    iio: usize,
    thread_id: ThreadId,
    name: String,
    value: Option<GraphValue>,
    event_kind: GraphEventKind,
}

fn event_kind<B: BV>(ev: &AxEvent<B>) -> GraphEventKind {
    match ev.base {
        Event::WriteMem { kind, .. } => 
            if kind == &"stage 1" {
                GraphEventKind::WriteS1Entry
            } else if kind == &"stage 2" {
                GraphEventKind::WriteS2Entry
            } else {
                GraphEventKind::WriteMem
            },
        Event::ReadMem { kind, .. } =>
            if ev.is_ifetch {
                GraphEventKind::Ifetch
            } else if ev.is_translate && kind == &"stage 1" {
                GraphEventKind::TranslateS1(0)
            } else if ev.is_translate && kind == &"stage 2" {
                GraphEventKind::TranslateS2(0)
            } else {
                GraphEventKind::ReadMem
            },
        _ => unreachable!(),
    }
}

fn update_event_kinds(evs: &mut HashMap<String, GraphEvent>) {
    let mut events: Vec<&mut GraphEvent> = evs.iter_mut().map(|(_, v)| v).collect();
    &events.sort_by(|ev1, ev2| (ev1.po, ev1.iio).cmp(&(ev2.po, ev2.iio)));

    let mut last_po = 0;
    let mut s1level = 0;
    let mut s2level = 0;
    for ev in events {
        if ev.po != last_po {
            last_po = ev.po;
            s1level = 0;
            s2level = 0;
        }

        match ev.event_kind {
            GraphEventKind::TranslateS1(ref mut level) => {
                *level = s1level;
                s1level += 1;
                s2level = 0;
            },
            GraphEventKind::TranslateS2(ref mut level) => {
                *level = s2level;
                s2level += 1;
            },
            _ => {},
        }
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
            iio: ev.intra_instruction_order,
            thread_id: ev.thread_id,
            name: ev.name.clone(),
            value: value,
            event_kind: event_kind(ev),
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

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
enum Align {
    LEFT,
    MIDDLE,
    RIGHT,
}

#[derive(Debug, Clone, Copy)]
struct Layout {
    wiggle: (f64, f64),
    alignment: Align,
}

#[derive(Debug)]
struct Style {
    bg_color: String,
    node_shape: String,
    node_style: String,
}

fn event_style<'a>(ev: &'a GraphEvent) -> Style {
    match ev.event_kind {
        GraphEventKind::TranslateS1(_) | GraphEventKind::WriteS1Entry =>
            Style { bg_color: "darkslategray1".to_string(), node_shape: "box".to_string(), node_style: "filled".to_string() },
        GraphEventKind::TranslateS2(_) | GraphEventKind::WriteS2Entry => 
            Style { bg_color: "wheat1".to_string(), node_shape: "box".to_string(), node_style: "filled".to_string() },
        _ =>
            Style { bg_color: "lightgrey".to_string(), node_shape: "box".to_string(), node_style: "filled".to_string() },
    }
}

#[derive(Debug)]
enum GridNode<'a> {
    // the position is the accumulated position in inches
    Node(Layout, PositionedGraphNode<'a>),
    SubCluster(Layout, GraphLayout<'a>),
}

/// a GraphLayout is a hierarchical row/column layout
#[derive(Debug)]
struct GraphLayout<'a> {
    num_rows: usize,
    num_cols: usize,
    children: HashMap<(usize,usize), GridNode<'a>>,
    /// the position (in points) to place the grid at
    /// this gets filled in later by the layouter
    pos: Option<(i64, i64)>,
}


#[derive(Debug)]
struct PositionedGraphNode<'a> {
    /// the associated underlying event
    /// if it exists
    ev: Option<&'a GraphEvent>,
    /// the graphviz node name
    /// usually taken from the underlying event if it exists
    name: String,
    /// the label to put in the box on the graph
    label: String,
    /// the row/column in the subgrid
    grid_rc: (usize, usize),
    /// style information about the node
    /// to be passed to graphviz
    style: Style,
    /// the position (in points) to place the node at
    /// this gets filled in later by the layouter
    pos: Option<(i64, i64)>,
}

// graphviz defaults to 14pt font
#[allow(dead_code)]
const FONTSIZE: usize = 14;
// with a scale of 72ppi
const SCALE: f64 = 72.0;

impl GridNode<'_> {
    /// the width (in points) of the node or the child grid
    fn compute_width(&self) -> usize {
        match self {
            GridNode::Node(layout, pgn) =>
                (SCALE/2.0) as usize + FONTSIZE*pgn.label.len() + (2.0*SCALE*layout.wiggle.0).round() as usize,  
            GridNode::SubCluster(layout, cluster) =>
                cluster.compute_width() + (2.0*SCALE*layout.wiggle.0).round() as usize,
        }
    }

    /// the height (in points) of the node or the child grid
    fn compute_height(&self) -> usize {
        match self {
            GridNode::Node(layout, _) =>
                (SCALE + 2.0*SCALE*layout.wiggle.1).round() as usize,
            GridNode::SubCluster(layout, cluster) =>
                cluster.compute_height() + (2.0*SCALE*layout.wiggle.1).round() as usize,
        }
    }

    fn get_layout(&self) -> &Layout {
        match self {
            GridNode::Node(layout, _) => layout,
            GridNode::SubCluster(layout, _) => layout,
        }
    }
}

impl GraphLayout<'_> {
    fn compute_max_width_heights(&self) -> (HashMap<usize, usize>, HashMap<usize, usize>) {
        let mut widths: HashMap<usize, usize> = HashMap::new();
        let mut heights: HashMap<usize, usize> = HashMap::new();

        for r in 0 .. self.num_rows {
            for c in 0 .. self.num_cols {
                let (w, h) = if let Some(child) = self.children.get(&(r, c)) {
                    (child.compute_width(), child.compute_height())
                } else {
                    (0, 0)
                };

                if !heights.contains_key(&r) {
                    heights.insert(r, 0);
                };

                if !widths.contains_key(&c) {
                    widths.insert(c, 0);
                };

                heights.insert(r, std::cmp::max(heights[&r], h));
                widths.insert(c, std::cmp::max(widths[&c], w));
            }
        };

        (widths, heights)
    }

    fn compute_width(&self) -> usize {
        let (widths, _) = self.compute_max_width_heights();
        let total_width = widths.values().sum::<usize>();
        println!("compute width (#children = {}) widths={:?} total-width={}", self.children.len(), widths, total_width);
        total_width
    }

    fn compute_height(&self) -> usize {
        let (_, heights) = self.compute_max_width_heights();
        let total_height = heights.values().sum::<usize>();
        println!("compute height (#children = {}) heights={:?} total-height={}", self.children.len(), heights, total_height);
        total_height
    }

    fn accumulate_max_widths_heights(&self, start_x: i64, start_y: i64) -> (HashMap<usize, i64>, HashMap<usize, i64>) {
        let (widths, heights) = self.compute_max_width_heights();

        let mut acc_widths: HashMap<usize,i64> = HashMap::new();
        let mut acc_heights: HashMap<usize,i64> = HashMap::new();

        let mut acc_width: i64 = start_x;
        let mut acc_height: i64 = start_y;

        for r in 0 .. self.num_rows {
            acc_heights.insert(r, acc_height);
            acc_height += heights[&r] as i64;
        }

        for c in 0 .. self.num_cols {
            acc_widths.insert(c, acc_width);
            acc_width += widths[&c] as i64;
        }

        (acc_widths, acc_heights)
    }

    fn accumulate_positions(&mut self, start_x: i64, start_y: i64) -> () {
        let (max_widths, _) = self.compute_max_width_heights();
        let (cum_widths, cum_heights) = self.accumulate_max_widths_heights(start_x, start_y);

        for (&(r,c), node) in self.children.iter_mut() {
            let (x,y) = (cum_widths[&c] as i64, cum_heights[&r] as i64);
            let node_width = node.compute_width() as i64;
            let node_height = node.compute_height() as i64;
            let col_width = max_widths[&c] as i64;
            let node_layout = node.get_layout();
            let xleft =
                match node_layout.alignment {
                    Align::LEFT => x,
                    Align::MIDDLE => x+col_width/2-node_width/2,
                    Align::RIGHT => x+col_width-node_width,
                };
            // graphviz "pos" is middle of node
            // so we +w/2,h/2 to make the pos be the top-left
            match node {
                GridNode::Node(_, ref mut pgn) => {
                    pgn.pos = Some((xleft+node_width/2,y+node_height/2));
                },
                GridNode::SubCluster(_, ref mut cluster) => {
                    cluster.pos = Some((xleft+node_width/2,y+node_height/2));
                    cluster.accumulate_positions(xleft+node_width/2, y+node_height/2);
                },
            }
        }
    }

    #[allow(dead_code)]
    fn iter_nodes<'a>(&'a self) -> Vec<&PositionedGraphNode<'a>> {
        let mut nodes: Vec<&PositionedGraphNode<'a>> = Vec::new();

        for c in self.children.values() {
            match c {
                GridNode::Node(_, pgn) => nodes.push(pgn),
                GridNode::SubCluster(_, cluster) => {
                    let sub_nodes = cluster.iter_nodes();
                    nodes.extend(sub_nodes);
                },
            }
        }

        nodes
    }
}

impl PositionedGraphNode<'_> {
    /// a graphviz line for an event node
    /// in the following format:
    /// R1_79_0 [shape=box,pos="13,17!",label=<LABEL FORMAT>,fillcolor=wheat1,style=filled];
    fn fmt_as_node(&self) -> String {
        let node_attrs: Vec<(String,String)> = vec![
            ("fillcolor".to_string(),  
                format!("{}", self.style.bg_color)
            ),
            ("style".to_string(),
                format!("{}", self.style.node_style)
            ),
            ("pos".to_string(),
                if let Some((x,y)) = self.pos {
                    format!("\"{},{}!\"", x, -y)
                } else {
                    "\"\"".to_string()
                }
            ),
            ("shape".to_string(),
                format!("{}", self.style.node_shape)
            ),
            ("label".to_string(),
                self.label.clone()
            ),
        ];

        let attrs = node_attrs.iter().map(|(attr,val)| format!("{}={}", attr, val)).collect::<Vec<String>>().join(", ");
        format!("{} [{}]", self.name, attrs)
    }
}

impl GraphEvent {
    // format the node label in longform:
    // label="ldr x2, [x3]\lT #x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_long(&self) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        if let Some(value) = &self.value {
            let q = "?".to_string();
            let addrstr = value.address.as_ref().unwrap_or_else(|| &q);
            let valstr = value.value.as_ref().unwrap_or_else(|| &q);
            format!("\"{}\\l{}\"", instr, format!("{} {} ({}): {}", value.prefix, addrstr, value.bytes, valstr))
        } else {
            format!("\"{}\"", instr)
        }
    }

    // format the node label in shortform:
    // label="T #x205800"
    #[allow(dead_code)]
    fn fmt_label_short(&self) -> String {
        if let Some(value) = &self.value {
            let q = "?".to_string();
            let addrstr = value.address.as_ref().unwrap_or_else(|| &q);
            format!("\"{}:{}:{} {}\"", value.prefix, self.po, self.iio, addrstr)
        } else {
            String::from("\"?\"")
        }
    }
}

fn produce_node_layout<'a>(g: &'a Graph) -> GraphLayout<'a> {
    let mut tids = HashSet::new();
    for ev in g.events.values() {
        tids.insert(ev.thread_id);
    }

    let mut thread_ids: Vec<usize> = tids.into_iter().collect();
    thread_ids.sort();

    // layout information for the various parts of the graph
    let layout_iw = Layout { wiggle: (0.0, 0.0), alignment: Align::MIDDLE };
    let layout_threads = Layout { wiggle: (0.0, 0.0), alignment: Align::LEFT };
    let layout_thread = Layout { wiggle: (1.0,0.0), alignment: Align::LEFT };
    let layout_instr = Layout { wiggle: (0.0,0.5), alignment: Align::LEFT };
    let layout_event = Layout { wiggle: (0.1,0.1), alignment: Align::LEFT };

    let mut top_level_layout = GraphLayout { num_rows: 2, num_cols: 1, pos: None, children: HashMap::new() };
    let iw_pgn = GridNode::Node(layout_iw, PositionedGraphNode { ev: None, name: "IW".to_string(), style: Style { bg_color: "lightgrey".to_string(), node_shape: "hexagon".to_string(), node_style: "filled".to_string() }, grid_rc: (0,0), label: "\"Initial State\"".to_string(), pos: None });
    top_level_layout.children.insert((0,0),iw_pgn);

    let mut thread_layouts = GraphLayout { num_rows: 1, num_cols: thread_ids.len(), pos: None, children: HashMap::new() };

    for tid in thread_ids {
        let mut events: Vec<&GraphEvent> = g.events.values().filter(|ev| ev.thread_id == tid).collect();
        &events.sort_by(|ev1, ev2| (ev1.po, ev1.iio).cmp(&(ev2.po, ev2.iio)));

        let max_po: usize = events.iter().map(|ev| ev.po).max().unwrap_or(0);
        let mut thread_layout = GraphLayout { num_rows: 1+max_po, num_cols: 1, pos: None, children: HashMap::new() };

        let mut last_po: usize = 0;
        let mut iio_row: usize = 0;
        let mut iio_col: usize;
        let mut current_instruction_layout = GraphLayout { num_rows: 6, num_cols: 7, pos: None, children: HashMap::new() };
        for ev in events.iter() {
            if last_po != ev.po {
                thread_layout.children.insert((last_po,0), GridNode::SubCluster(layout_instr, current_instruction_layout));
                current_instruction_layout = GraphLayout { num_rows: 6, num_cols: 7, pos: None, children: HashMap::new() };

                last_po = ev.po;
                iio_row = 0;
            }

            // we fix a layout per instruction:
            //       0   1   2   3   4   5   6 
            //  0   IF      S2  S2  S2  S2
            //  1       S1  S2  S2  S2  S2
            //  2       S1  S2  S2  S2  S2
            //  3       S1  S2  S2  S2  S2
            //  4       S1  S2  S2  S2  S2   RW
            //
            // TODO:  hide some
            // TODO: different layout if only S1 enabled?
            match ev.event_kind {
                GraphEventKind::TranslateS1(level) => {
                    iio_col = 1;
                    iio_row = level+1;
                },
                GraphEventKind::TranslateS2(level) => {
                    iio_col = level+2;
                },
                GraphEventKind::ReadMem | GraphEventKind::WriteMem => {
                    iio_col = 6;
                },
                GraphEventKind::Ifetch => {
                    iio_col = 0;
                },
                _ => {
                    iio_col = 6;
                },
            }

            let rc = (iio_row,iio_col);
            current_instruction_layout.children.insert(
                rc,
                GridNode::Node(
                    layout_event,
                    PositionedGraphNode { ev: Some(*ev), style: event_style(ev), name: ev.name.clone(), grid_rc: rc, label: ev.fmt_label_short(), pos: None }
                )
            );
        }

        if current_instruction_layout.children.len() > 0 {
            thread_layout.children.insert((max_po,0), GridNode::SubCluster(layout_instr, current_instruction_layout));
        }

        thread_layouts.children.insert((0,tid), GridNode::SubCluster(layout_thread, thread_layout));
    }

    let threads_node = GridNode::SubCluster(layout_threads, thread_layouts);
    top_level_layout.children.insert((1,0), threads_node);
    top_level_layout.accumulate_positions(0, 0);
    top_level_layout
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

        let node_layout = produce_node_layout(self);

        let mut thread_ids = HashSet::new();
        for ev in self.events.values() {
            thread_ids.insert(ev.thread_id);
        }

        if let Some(GridNode::Node(_, iw)) = node_layout.children.get(&(0,0)) {
            writeln!(f, "{};", iw.fmt_as_node())?;
        }

        if let Some(GridNode::SubCluster(_, thread_clusters)) = node_layout.children.get(&(1,0)) {
            for tid in thread_ids {
                writeln!(f, "  subgraph cluster{} {{", tid)?;
                writeln!(f, "    label=\"Thread #{}\"", tid)?;
                writeln!(f, "    style=dashed")?;
                writeln!(f, "    color=gray50")?;

                let mut lowest_po = None;
                let mut lowest_name = "";

                let mut events: Vec<&GraphEvent> = self.events.values().filter(|ev| ev.thread_id == tid).collect();
                &events.sort_by(|ev1, ev2| (ev1.po, ev1.iio).cmp(&(ev2.po, ev2.iio)));

                // draw the events and boxes
                if let Some(GridNode::SubCluster(_, thread)) = thread_clusters.children.get(&(0,tid)) {
                    for ((po, _), instr) in thread.children.iter() {
                        if let GridNode::SubCluster(_, instr) = instr {
                            if let Some((x, y)) = instr.pos {
                                let (w, h) = (instr.compute_width() as i64, instr.compute_height() as i64);
                                let wiggle = (SCALE / 2.0) as i64;
                                // for each instruction, draw a dotted box around it
                                let border: Vec<(i64,i64)> = vec![
                                    (x-wiggle,y-wiggle), // top-left
                                    (x+w+wiggle,y-wiggle), // top-right
                                    (x+w+wiggle,y+h+wiggle), // bottom-right
                                    (x-wiggle,y+h+wiggle), // bottom-left
                                ];
                                
                                for (i, (bx, by)) in border.iter().enumerate() {
                                    writeln!(f, "tbox{}_{}_0{} [style=invis,pos=\"{},{}\"];", tid, po, i, bx, -by)?;
                                }
                                
                                for i in 0..4 {
                                    write!(f, "tbox{}_{}_0{} -> ", tid, po, i)?;
                                    if i == 3 {
                                        write!(f, "tbox{}_{}_00 [arrowhead=none]", tid, po)?;
                                    } else {
                                        write!(f, "tbox{}_{}_0{} -> ", tid, po, i+1)?;
                                    }
                                }

                                writeln!(f, " ;")?;
                                
                            };

                            for ev in instr.children.values() {
                                if let GridNode::Node(_, pgn) = ev {
                                    writeln!(f, "    {};", pgn.fmt_as_node())?;
                                }
                            }
                        }
                    }
                }

                for ev in &events {
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

fn tag_from_read_event<'a, B>(ev: &AxEvent<B>) -> &'a str {
    if ev.is_ifetch { 
        "IF" 
    } else if ev.is_translate {
        "Tr" 
    } else {
        "R"
    }
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
                let event_name = tag_from_read_event(event);
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

    update_event_kinds(&mut events);

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
        match event.base {
            Event::ReadMem { value, address, bytes, .. } => {
                if value.is_symbolic() || address.is_symbolic() {
                    // the event will already exist in the graph
                    // but some of the fields may be empty
                    let gev = g.events.remove(&event.name).unwrap();
                    let gval = gev.value.unwrap();
                    let event_kind_name = tag_from_read_event(event);
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
