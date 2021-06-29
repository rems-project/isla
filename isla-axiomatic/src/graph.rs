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
use isla_lib::log;
use isla_lib::smt::{Event, register_name_string};


use isla_cat::cat;

use crate::axiomatic::model::Model;
use crate::axiomatic::relations;
use crate::axiomatic::{AxEvent, ExecutionInfo, Pairs, ThreadId};
use crate::footprint_analysis::Footprint;
use crate::litmus::instruction_from_objdump;
use crate::litmus::Litmus;
use crate::sexp::{InterpretError, SexpVal};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphOpts {
    pub include_all_events: bool,
    pub compact: bool,
    pub show_all_reads: bool,
    pub smart_layout: bool,
    pub show_regs: HashSet<String>,
    pub flatten: bool,
    pub explode_labels: bool,
    pub debug_labels: bool,
}

impl GraphOpts {
    pub const DEFAULT_SHOW_REGS: &'static [&'static str] =
        &[
            "R0", "R1", "R2", "R3", "R4", "R5", "R6",
            "R7", "R8", "R9", "R10", "R11", "R12", "R13",
            "R14", "R15", "R16", "R18", "R18", "R19", "R20",
            "R21", "R22", "R23", "R24", "R25", "R26", "R27",
            "R28", "R29", "R30", "R31",
            "SP",
            "SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3",
            "VBAR_EL1", "VBAR_EL2",
        ];

    pub const ARMV8_ADDR_TRANS_SHOW_REGS: &'static [&'static str] =
        &[
            "TTBR0_EL1", "TTBR1_EL1",
            "TTBR0_EL2",
            "VTTBR_EL2",
        ];
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphValue {
    prefix: String,
    address: Option<String>,
    bytes: String,
    value: Option<String>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum Stage {
    Stage1,
    Stage2,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct WriteKind {
    pub to_translation_table_entry: Option<Stage>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct TranslateKind {
    pub stage: Stage,
    pub level: usize,  // TODO: BS: what about level -1 ?
    // for s2 translations during a s1 walk
    // which level of the s1 are we at
    pub for_s1: Option<usize>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum GraphEventKind {
    Ifetch,
    ReadMem,
    WriteMem(WriteKind),
    Translate(TranslateKind),
    ReadReg,
    WriteReg,
    Barrier,
    CacheOp,
    Info,  // for events that are purely decorative
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
    match ev.base() {
        Some(Event::WriteMem { kind, .. }) =>
            if kind == &"stage 1" {
                GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: Some(Stage::Stage1) })
            } else if kind == &"stage 2" {
                GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: Some(Stage::Stage2) })
            } else {
                GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: None })
            },
        Some(Event::ReadMem { kind, .. }) =>
            if ev.is_ifetch {
                GraphEventKind::Ifetch
            } else if relations::is_translate(ev) && kind == &"stage 1" {
                GraphEventKind::Translate(TranslateKind { stage: Stage::Stage1, level: 0, for_s1: None })
            } else if relations::is_translate(ev) && kind == &"stage 2" {
                GraphEventKind::Translate(TranslateKind { stage: Stage::Stage2, level: 0, for_s1: None })
            } else {
                GraphEventKind::ReadMem
            },
        Some(Event::ReadReg(_,_,_)) =>
            GraphEventKind::ReadReg,
        Some(Event::WriteReg(_,_,_)) =>
            GraphEventKind::WriteReg,
        Some(Event::Barrier { .. }) =>
            GraphEventKind::Barrier,
        Some(Event::CacheOp { .. }) =>
            GraphEventKind::CacheOp,
        _ =>
            GraphEventKind::Info,
    }
}

fn update_event_kinds(evs: &mut HashMap<String, GraphEvent>) {
    let mut events: Vec<&mut GraphEvent> = evs.iter_mut().map(|(_, v)| v).collect();
    &events.sort_by(|ev1, ev2| (ev1.thread_id, ev1.po, ev1.iio).cmp(&(ev2.thread_id, ev2.po, ev2.iio)));

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
            GraphEventKind::Translate(TranslateKind { stage: Stage::Stage1, ref mut level, .. }) => {
                *level = s1level;
                s1level += 1;
                s2level = 0;
            },
            GraphEventKind::Translate(TranslateKind { stage: Stage::Stage2, ref mut level, ref mut for_s1 }) => {
                *level = s2level;
                s2level += 1;
                *for_s1 = Some(s1level);
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
        address: Option<&Val<B>>,
        bytes: u32,
        value: Option<&Val<B>>,
    ) -> Self {
        let addr =
            if let Some(addr) = address {
                if !addr.is_symbolic() {
                    match addr {
                        Val::String(s) => Some(s.clone()),
                        _ => {
                            let addrstr = addr.as_bits().map(|bv| format!("#x{:x}", bv)).unwrap_or_else(|| "?addr".to_string());
                            Some(addrstr)
                        },
                    }
                } else {
                    None
                }
            } else {
                None
            };

        let value =
            if let Some(val) = value {
                if !val.is_symbolic() {
                    match val {
                        Val::String(s) => Some(s.clone()),
                        _ => {
                            let valstr = val.as_bits().map(|bv| bv.signed().to_string()).unwrap_or_else(|| "?val".to_string());
                            Some(valstr)
                        },
                    }
                } else {
                    None
                }
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
    pub edges: HashSet<(String, String)>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Graph {
    pub events: HashMap<String, GraphEvent>,  // EventName -> Event
    pub sets: Vec<GraphSet>,
    pub relations: Vec<GraphRelation>,
    pub show: Vec<String>,
    pub opts: GraphOpts,
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
        "po" => "black",
        "iio" => "grey",
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

fn event_style<'a>(ev: &'a GraphEvent) -> Style {
    match ev.event_kind {
        GraphEventKind::Translate(TranslateKind { stage: Stage::Stage1, ..}) | GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: Some(Stage::Stage1) }) =>
            Style { bg_color: "darkslategray1".to_string(), node_shape: "box".to_string(), node_style: "filled".to_string(), dimensions: (0.0, 0.0) },
            GraphEventKind::Translate(TranslateKind { stage: Stage::Stage2, ..}) | GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: Some(Stage::Stage2) }) =>
            Style { bg_color: "wheat1".to_string(), node_shape: "box".to_string(), node_style: "filled".to_string(), dimensions: (0.0, 0.0) },
        _ =>
            Style { bg_color: "lightgrey".to_string(), node_shape: "box".to_string(), node_style: "filled".to_string(), dimensions: (0.0, 0.0) },
    }
}

#[derive(Debug, Clone)]
enum GridNode<'a> {
    Node(PositionedGraphNode<'a>),
    SubCluster(GraphLayout<'a>),
}


/// padding around a child
/// in inches
#[derive(Debug, Clone)]
struct Padding {
    up: f64,
    down: f64,
    left: f64,
    right: f64,
}

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
enum Align {
    LEFT,
    MIDDLE,
    RIGHT,
}

#[derive(Debug, Clone)]
struct Layout {
    /// padding around the child
    /// up, down, left, right
    /// in points
    padding: Padding,
    /// alignment within the column
    alignment: Align,
    /// the position (in points) to place the child at
    /// this gets filled in later by the layouter
    /// for a Node this is the centre of the node
    pos: Option<(i64, i64)>,
    /// the position (in points) of the top-left of the bounding box
    bb_pos: Option<(i64, i64)>,
    /// if false, do not render in the final image
    show: bool,
    /// if false, the node has 0width and 0height for layouting purposes
    skinny: bool,
}

#[derive(Debug, Clone)]
struct GridChild<'a> {
    /// the node
    node: GridNode<'a>,
    /// layout information about the child
    layout: Layout,
}

/// a GraphLayout is a hierarchical row/column layout
#[derive(Debug, Clone)]
struct GraphLayout<'a> {
    children: HashMap<(usize,usize), GridChild<'a>>,
}

#[derive(Debug, Clone)]
struct Style {
    bg_color: String,
    node_shape: String,
    node_style: String,
    /// the width/height of the node
    dimensions: (f64, f64),
}

#[derive(Debug, Clone)]
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

}

const FONTSIZE: usize = 24;
// with a scale of 72ppi
const SCALE: f64 = 72.0;

fn inches_from_points(p: usize) -> f64 {
    (p as f64) / SCALE
}

fn points_from_inches(i: f64) -> usize {
    (i * SCALE).round() as usize
}

impl PositionedGraphNode<'_> {
    /// the width (in points) of the actual underlying node shape
    fn compute_width(&self) -> usize {
        FONTSIZE*self.label.len()
    }

    /// the height (in points) of the actual underlying node shape
    fn compute_height(&self) -> usize {
        SCALE as usize
    }
}

impl<'ev> GridChild<'ev> {
    /// the width (in points) of the node or the child grid
    fn compute_width(&self) -> usize {
        if self.layout.skinny {
            return 0;
        }

        let ww: usize = points_from_inches(self.layout.padding.left + self.layout.padding.right);
        match &self.node {
            GridNode::Node(pgn) =>
                pgn.compute_width() + ww,
            GridNode::SubCluster(cluster) =>
                cluster.compute_width() + ww,
        }
    }

    /// the height (in points) of the node or the child grid
    fn compute_height(&self) -> usize {
        if self.layout.skinny {
            return 0;
        }

        let wh: usize = points_from_inches(self.layout.padding.up + self.layout.padding.down);
        match &self.node {
            GridNode::Node(pgn) =>
                pgn.compute_height() + wh,
            GridNode::SubCluster(cluster) =>
                cluster.compute_height() + wh,
        }
    }

    /// a graphviz line for an event node
    /// in the following format:
    /// R1_79_0 [shape=box,pos="13,17!",label=<LABEL FORMAT>,fillcolor=wheat1,style=filled];
    fn fmt_as_node(&self) -> String {
        if let GridNode::Node(pge) = &self.node {
            let node_attrs: Vec<(String,String)> = vec![
                ("fillcolor".to_string(),
                    format!("{}", pge.style.bg_color)
                ),
                ("style".to_string(),
                    format!("{}", pge.style.node_style)
                ),
                ("pos".to_string(),
                    if let Some((x,y)) = self.layout.pos {
                        format!("\"{},{}!\"", x, -y)
                    } else {
                        "\"\"".to_string()
                    }
                ),
                ("shape".to_string(),
                    format!("{}", pge.style.node_shape)
                ),
                ("label".to_string(),
                    pge.label.clone()
                ),
                ("width".to_string(),
                    format!("{}", pge.style.dimensions.0)
                ),
                ("height".to_string(),
                    format!("{}", pge.style.dimensions.1)
                ),
            ];

            let attrs = node_attrs.iter().map(|(attr,val)| format!("{}={}", attr, val)).collect::<Vec<String>>().join(", ");
            format!("{} [{}]", pge.name, attrs)
        } else {
            format!("N/A")
        }
    }

    #[allow(dead_code)]
    fn unwrap_node(&self) -> &PositionedGraphNode<'ev> {
        if let GridNode::Node(n) = &self.node {
            n
        } else {
            panic!("cannot unwrap SubCluster")
        }
    }

    #[allow(dead_code)]
    fn unwrap_cluster(&self) -> &GraphLayout<'ev> {
        if let GridNode::SubCluster(n) = &self.node {
            n
        } else {
            panic!("cannot unwrap Node")
        }
    }

    #[allow(dead_code)]
    fn unwrap_node_mut(&mut self) -> &mut PositionedGraphNode<'ev> {
        if let GridNode::Node(n) = &mut self.node {
            n
        } else {
            panic!("cannot unwrap SubCluster")
        }
    }

    #[allow(dead_code)]
    fn unwrap_cluster_mut(&mut self) -> &mut GraphLayout<'ev> {
        if let GridNode::SubCluster(n) = &mut self.node {
            n
        } else {
            panic!("cannot unwrap Node")
        }
    }
}

impl<'g> GraphLayout<'g> {
    fn num_rows(&self) -> usize {
        self.children.keys().map(|(r,_)| r).max().map(|x| x+1).unwrap_or(0)
    }

    fn num_cols(&self) -> usize {
        self.children.keys().map(|(_,c)| c).max().map(|x| x+1).unwrap_or(0)
    }

    fn compute_max_width_heights(&self) -> (HashMap<usize, usize>, HashMap<usize, usize>) {
        let mut widths: HashMap<usize, usize> = HashMap::new();
        let mut heights: HashMap<usize, usize> = HashMap::new();

        for r in 0 .. self.num_rows() {
            for c in 0 .. self.num_cols() {
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
        widths.values().sum::<usize>()
    }

    fn compute_height(&self) -> usize {
        let (_, heights) = self.compute_max_width_heights();
        heights.values().sum::<usize>()
    }

    fn accumulate_max_widths_heights(
        &self,
        start_x: i64,
        start_y: i64,
        widths: &HashMap<usize, usize>,
        heights: &HashMap<usize, usize>,
    ) -> (HashMap<usize, i64>, HashMap<usize, i64>) {
        let mut acc_widths: HashMap<usize,i64> = HashMap::new();
        let mut acc_heights: HashMap<usize,i64> = HashMap::new();

        let mut acc_width: i64 = start_x;
        let mut acc_height: i64 = start_y;

        for r in 0 .. self.num_rows() {
            acc_heights.insert(r, acc_height);
            acc_height += heights[&r] as i64;
        }

        for c in 0 .. self.num_cols() {
            acc_widths.insert(c, acc_width);
            acc_width += widths[&c] as i64;
        }

        (acc_widths, acc_heights)
    }

    fn flatten(&mut self) -> () {

        let mut row_exploders: HashMap<usize,usize> = HashMap::new();
        let mut col_exploders: HashMap<usize,usize> = HashMap::new();

        fn _default_insert(m: &mut HashMap<usize,usize>, k: usize) -> () {
            match m.insert(k, 1) {
                None => {},
                Some(old_v) => {
                    m.insert(k, old_v);
                }
            }
        }

        for r in 0..self.num_rows() {
            _default_insert(&mut row_exploders, r);
            for c in 0..self.num_cols() {
                let node = self.children.get(&(r,c));
                _default_insert(&mut col_exploders, c);
                match node {
                    Some(GridChild { node: GridNode::SubCluster(cluster), ..  }) => {
                        match col_exploders.insert(c, cluster.num_cols()) {
                            Some(v) => {
                                col_exploders.insert(c, std::cmp::max(v, cluster.num_cols()));
                            },
                            None => {},
                        };
                        match row_exploders.insert(r, cluster.num_rows()) {
                            Some(v) => {
                                row_exploders.insert(r, std::cmp::max(v, cluster.num_rows()));
                            },
                            None => {},
                        }
                    },
                    _ => {},
                }
            }
        }

        let (cum_cols, cum_rows) = self.accumulate_max_widths_heights(0, 0, &col_exploders, &row_exploders);
        let mut new_children: HashMap<(usize,usize), GridChild> = HashMap::new();
        let mut count_subclusters = 0;

        for ((r,c),child_node) in self.children.drain() {
            let row_start = cum_rows.get(&r).unwrap_or(&0);
            let col_start = cum_cols.get(&c).unwrap_or(&0);
            let (row_start, col_start) = (*row_start as usize, *col_start as usize);
            match child_node.node {
                GridNode::SubCluster(mut cluster) => {
                    count_subclusters += 1;

                    let maxrow: usize = cluster.children.keys().map(|(r,_)| *r).max().unwrap_or(1);
                    let maxcol: usize = cluster.children.keys().map(|(_,c)| *c).max().unwrap_or(1);

                    for ((subrow,subcol), mut n) in cluster.children.drain() {
                        if subrow == 0 {
                            n.layout.padding.up = child_node.layout.padding.up;
                        };
                        if subcol == 0 {
                            n.layout.padding.left = child_node.layout.padding.left;
                        }
                        if subrow == maxrow {
                            n.layout.padding.down = child_node.layout.padding.down;
                        }
                        if subcol == maxcol {
                            n.layout.padding.right = child_node.layout.padding.right;
                        }

                        match new_children.insert((row_start+subrow,col_start+subcol),n) {
                            None => {},
                            Some(old) => {
                                panic!("oops! placed a subcluster child at already-existing addr ({}+{},{}+{}): {:?}", row_start, subrow, col_start, subcol, old);
                            }
                        }
                    }
                },
                _ => {
                    // if we had a single node and the ones below/above got split up
                    // we have to decide which column to place this single node in now
                    // and we use the alignment to decide ...
                    let new_cols = *col_exploders.get(&c).unwrap();
                    let subcoloffs =
                        match child_node.layout.alignment {
                            Align::LEFT => 0,
                            Align::MIDDLE => new_cols/2,
                            Align::RIGHT => new_cols-1,
                        };

                    match new_children.insert((row_start,col_start+subcoloffs), child_node)  {
                        None => {},
                        Some(old) => {
                            panic!("oops! placed a second child at {:?}: {:?}", (row_start, col_start), old);
                        }
                    }
                },
            }
        }

        self.children = new_children;

        // if there were any clusters left
        // recurse and explode those too
        if count_subclusters > 0 {
            self.flatten()
        }
    }

    /// go through all children and attach a physical position
    /// (in points) at which to place the node.
    ///
    /// a subcluster position is marked by the top-left of the bounding box
    /// whereas a node's position is marked by the centre of the physical node
    fn accumulate_positions(&mut self, start_x: i64, start_y: i64) -> () {
        let (max_widths, max_heights) = self.compute_max_width_heights();
        let (cum_widths, cum_heights) = self.accumulate_max_widths_heights(start_x, start_y, &max_widths, &max_heights);

        for (&(r,c), mut child) in self.children.iter_mut() {
            let (x,y) = (cum_widths[&c] as i64, cum_heights[&r] as i64);
            let node_width = child.compute_width() as i64;
            let _node_height = child.compute_height() as i64;
            let col_width = max_widths[&c] as i64;
            let node_layout = &child.layout;

            // the breathing room around
            let (wxl, _wxr, wyu, _wyd) = (
                points_from_inches(node_layout.padding.left) as i64,
                points_from_inches(node_layout.padding.right) as i64,
                points_from_inches(node_layout.padding.up) as i64,
                points_from_inches(node_layout.padding.down) as i64,
            );

            // align left/middle/right according to layout instructions
            let xleft =
                match node_layout.alignment {
                    Align::LEFT => x,
                    Align::MIDDLE => x+col_width/2-node_width/2,
                    Align::RIGHT => x+col_width-node_width,
                };

            child.layout.bb_pos = Some((x,y));
            match child.node {
                GridNode::Node(ref mut pgn) => {
                    let (actual_node_width, actual_node_height) = (pgn.compute_width() as i64, pgn.compute_height() as i64);

                    // graphviz "pos" is middle of node
                    // so we +w/2,h/2 to make the pos be the top-left
                    child.layout.pos = Some((xleft+wxl+actual_node_width/2,y+wyu+actual_node_height/2));
                    pgn.style.dimensions = (inches_from_points(actual_node_width as usize), inches_from_points(actual_node_height as usize));
                },
                GridNode::SubCluster(ref mut cluster) => {
                    child.layout.pos = Some((x,y));
                    cluster.accumulate_positions(xleft+wxl, y+wyu);
                },
            };
        }
    }

    fn iter_nodes<'a>(&'a self, only_visible: bool, only_real: bool) -> Vec<&GridChild<'a>> {
        let mut nodes: Vec<&GridChild<'a>> = Vec::new();

        for c in self.children.values() {
            if !c.layout.show && only_visible {
                continue;
            }

            if c.layout.skinny && only_real {
                continue;
            }

            match &c.node {
                GridNode::Node(_) => nodes.push(&c),
                GridNode::SubCluster(cluster) => {
                    let sub_nodes = cluster.iter_nodes(only_visible, only_real);
                    nodes.extend(sub_nodes);
                },
            }
        }

        nodes
    }

    fn iter_nodes_mut(&mut self, only_visible: bool, only_real: bool) -> Vec<&mut GridChild<'g>> {
        let mut nodes: Vec<&mut GridChild<'g>> = Vec::new();

        for c in self.children.values_mut() {
            if !c.layout.show && only_visible {
                continue;
            }

            if c.layout.skinny && only_real {
                continue;
            }

            match c.node {
                GridNode::Node(_) => nodes.push(c),
                GridNode::SubCluster(ref mut cluster) => {
                    let sub_nodes = cluster.iter_nodes_mut(only_visible, only_real);
                    nodes.extend(sub_nodes);
                },
            }
        }

        nodes
    }

    fn find_node_mut(&mut self, name: &String) -> Option<&mut GridChild<'g>> {
        for n in self.iter_nodes_mut(false, false) {
            if let GridNode::Node(pge) = &n.node {
                if &pge.name == name {
                    return Some(n);
                }
            }
        }

        None
    }

    fn po(&self) -> Option<usize> {
        for c in self.iter_nodes(false, false) {
            if let GridNode::Node(pgn) = &c.node {
                if let Some(ev) = pgn.ev {
                    return Some(ev.po);
                }
            }
        }

        None
    }
}

impl GraphEvent {
    // format the node label with all debug info:
    // label="W_00_000: "ldr x2, [x3]": T #x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_debug(&self) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        if let Some(value) = &self.value {
            let q = "??".to_string();
            let addrstr = value.address.as_ref().unwrap_or_else(|| &q);
            let valstr = value.value.as_ref().unwrap_or_else(|| &q);
            format!("\"{}: \\\"{}\\\": {}\"", self.name, instr, format!("{} {} ({}): {}", value.prefix, addrstr, value.bytes, valstr))
        } else {
            format!("\"{}: \\\"{}\\\"\"", self.name, instr)
        }
    }

    // format the node label in longform:
    // label="ldr x2, [x3]\lT #x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_long(&self) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        if let Some(value) = &self.value {
            let q = "??".to_string();
            let addrstr = value.address.as_ref().unwrap_or_else(|| &q);
            let valstr = value.value.as_ref().unwrap_or_else(|| &q);
            format!("\"{}: {}\"", instr, format!("{} {} ({}): {}", value.prefix, addrstr, value.bytes, valstr))
        } else {
            format!("\"{}\"", instr)
        }
    }

    // format the node label in half form:
    // label="T #x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_medium(&self) -> String {
        if let Some(value) = &self.value {
            let q = "?".to_string();
            let addrstr = value.address.as_ref().unwrap_or_else(|| &q);
            let valstr = value.value.as_ref().unwrap_or_else(|| &q);
            format!("\"{}\"", format!("{} {} ({}): {}", value.prefix, addrstr, value.bytes, valstr))
        } else {
            String::from("\"?\"")
        }
    }

    // format the node label in shortform:
    // label="T #x205800"
    #[allow(dead_code)]
    fn fmt_label_short(&self) -> String {
        if let Some(value) = &self.value {
            let q = "?".to_string();
            let addrstr = value.address.as_ref().unwrap_or_else(|| &q);
            format!("\"{} {}\"", value.prefix, addrstr)
        } else {
            String::from("\"?\"")
        }
    }
}

impl Graph {
    fn produce_node_layout<'g>(&'g self, opts: &GraphOpts, pas: HashSet<&String>) -> GraphLayout<'g> {
        let mut tids = HashSet::new();
        for ev in self.events.values() {
            tids.insert(ev.thread_id);
        }

        let mut thread_ids: Vec<usize> = tids.into_iter().collect();
        thread_ids.sort();

        // layout information for the various parts of the graph
        let layout_iw = Layout { padding: Padding { up: 0.5, down: 1.0, left: 0.5, right: 0.5 }, alignment: Align::MIDDLE, pos: None, bb_pos: None, show: true, skinny: false };
        let layout_threads = Layout { padding: Padding { up: 0.0, down: 0.0, left: 0.0, right: 0.0 }, alignment: Align::LEFT, pos: None, bb_pos: None, show: true, skinny: false };
        let layout_thread = Layout { padding: Padding { up: 0.0, down: 0.0, left: 0.0, right: 3.0 }, alignment: Align::LEFT, pos: None, bb_pos: None, show: true, skinny: false };
        // space around each instruction for layout space, border and opcode label
        let layout_instr = Layout { padding: Padding { up: 0.0, down: 2.0, left: 0.0, right: 0.0 }, alignment: Align::MIDDLE, pos: None, bb_pos: None, show: true, skinny: false };
        // by aligning events in the middle we make sure arrows up/down the same column are vertical
        let layout_event = Layout { padding: Padding { up: 0.2, down: 0.2, left: 0.2, right: 0.2 }, alignment: Align::LEFT, pos: None, bb_pos: None, show: true, skinny: false };

        let mut top_level_layout = GraphLayout { children: HashMap::new() };
        let iw_pgn = GridNode::Node(
            PositionedGraphNode {
                ev: None,
                name: "IW".to_string(),
                style: Style { bg_color: "lightgrey".to_string(), node_shape: "hexagon".to_string(), node_style: "filled".to_string(), dimensions: (0.0, 0.0) },
                grid_rc: (0,0),
                label: "\"Initial State\"".to_string(),
            }
        );
        top_level_layout.children.insert((0,0), GridChild { node: iw_pgn, layout: layout_iw });

        let mut thread_layouts = GraphLayout { children: HashMap::new() };

        for tid in thread_ids {
            let mut events: Vec<&GraphEvent> = self.events.values().filter(|ev| ev.thread_id == tid).collect();
            &events.sort_by(|ev1, ev2| (ev1.thread_id, ev1.po, ev1.iio).cmp(&(ev2.thread_id, ev2.po, ev2.iio)));

            let mut thread_layout = GraphLayout { children: HashMap::new() };

            let mut iio_row: usize = 0;
            let mut iio_col: usize = 0;
            let mut iio_show_count: usize = 0;
            let mut last_instr_row: usize = 0;
            let mut last_po: Option<usize> = None;
            let mut iio_phase: usize = 0;
            let mut current_thread_instructions = HashMap::new();
            for ev in events.iter() {
                if last_po == None {
                    last_po = Some(ev.po);
                }

                if last_po != Some(ev.po) {
                    thread_layout.children.insert(
                        (last_instr_row,0),
                        GridChild {
                            node: GridNode::SubCluster(
                                GraphLayout {
                                    children: current_thread_instructions
                                }
                            ),
                            layout: layout_instr.clone()
                        }
                    );
                    current_thread_instructions = HashMap::new();

                    last_po = Some(ev.po);
                    last_instr_row += 1;
                    iio_row = 0;
                    iio_col = 0;
                    iio_show_count = 0;
                    iio_phase = 0;
                }

                let mut show = true;
                if let GraphEventKind::Translate(_) = ev.event_kind {
                    if let Some(v) = &ev.value {
                        if let Some(addr) = &v.address {
                            if ! pas.contains(&addr) && ! opts.show_all_reads {
                                show = false;
                            }
                        }
                    }
                };

                // if skinny then this node pretends to have 0width and 0height
                // and therefore mostly doesn't influence the layouter later
                let skinny =
                    if show {
                        false
                    } else {
                        if opts.compact {
                            true
                        } else {
                            false
                        }
                    };

                // we format with the short label for now
                // later we go back over each instruction and put in a longer label if needed
                let label =
                    if opts.debug_labels {
                        ev.fmt_label_debug()
                    } else if opts.explode_labels {
                        ev.fmt_label_medium()
                    } else {
                        ev.fmt_label_short()
                    };

                let rc =
                    if opts.smart_layout {
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
                            GraphEventKind::Ifetch => {
                                iio_phase = 2;
                                iio_col = 0;
                                iio_row += 1;
                            },
                            GraphEventKind::Translate(TranslateKind { stage: Stage::Stage1, .. }) => {
                                iio_phase = 3;
                                iio_col = 1;
                                iio_row += 1;
                            },
                            GraphEventKind::Translate(TranslateKind { stage: Stage::Stage2, .. }) => {
                                if iio_phase < 3 {
                                    iio_col = 2;
                                    iio_row += 1;
                                } else {
                                    iio_col += 1;
                                }
                                iio_phase = 4;
                            },
                            GraphEventKind::ReadMem | GraphEventKind::WriteMem(_) => {
                                iio_phase = 5;
                                iio_row += 1;
                                iio_col =
                                    current_thread_instructions
                                    .keys()
                                    .map(|(_,c)| *c)
                                    .max()
                                    .unwrap_or(1);
                            },
                            _ => {
                                if iio_phase == 0 {
                                    iio_col = 0;
                                    iio_phase = 1;
                                } else if iio_phase == 1 {
                                    iio_col += 1;
                                } else if iio_phase == 3 {
                                    iio_phase = 4;
                                    iio_row += 1;
                                    iio_col = 0;
                                } else {
                                    iio_col += 1;
                                }
                            },
                        };
                        (iio_row, iio_col)
                    } else {
                        // lay out in a square
                        // with rows
                        (iio_show_count / 5, iio_show_count % 5)
                    };

                current_thread_instructions.insert(
                    rc,
                    GridChild {
                        node: GridNode::Node(
                            PositionedGraphNode {
                                ev: Some(*ev),
                                style: event_style(ev),
                                name: ev.name.clone(),
                                grid_rc: rc,
                                label: label,
                            }
                        ),
                        layout: Layout { show: show, skinny: skinny, ..layout_event.clone() },
                    }
                );

                if show {
                    iio_show_count += 1;
                }
            }

            if current_thread_instructions.len() > 0 {
                let new_child = GridChild {
                    node: GridNode::SubCluster(
                        GraphLayout { children: current_thread_instructions }
                    ),
                    layout: layout_instr.clone(),
                };

                thread_layout.children.insert(
                    (last_instr_row, 0),
                    new_child,
                );
            }

            thread_layouts.children.insert(
                (0,tid),
                GridChild {
                    node: GridNode::SubCluster(thread_layout),
                    layout: layout_thread.clone()
                }
            );
        }

        // go over each instruction and refit the labels
        // to add more information to the nodes
        // if there's not enough context in the other shown nodes
        if ! opts.debug_labels {
            for instr_cluster in thread_layouts.children.values_mut() {
                let instrs = instr_cluster.unwrap_cluster_mut();
                for instr_child in instrs.children.values_mut() {
                    let instr_cluster = instr_child.unwrap_cluster_mut();
                    let instr_nodes = instr_cluster.iter_nodes_mut(true, false);
                    let count_show = instr_nodes.len();

                    for instr in instr_nodes {
                        let mut pgn = instr.unwrap_node_mut();
                        if let Some(ev) = &pgn.ev {
                            if count_show == 1 {
                                pgn.label = ev.fmt_label_long();
                            } else {
                                if let GraphEventKind::ReadReg | GraphEventKind::WriteReg | GraphEventKind::ReadMem | GraphEventKind::WriteMem(_) = ev.event_kind {
                                    pgn.label = ev.fmt_label_medium();
                                }
                            }
                        }
                    }
                }
            }
        }

        let threads_node = GridNode::SubCluster(thread_layouts);
        top_level_layout.children.insert((1,0), GridChild { node: threads_node, layout: layout_threads });

        if opts.flatten {
            // explode out into a big flat grid,
            // then use that to align rows and columns and layout things
            let mut exploded = top_level_layout.clone();
            let threads = exploded.children.get_mut(&(0,0)).unwrap().unwrap_cluster_mut();
            threads.flatten();
            threads.accumulate_positions(0,0);

            for n in exploded.iter_nodes(false, false) {
                let pge = n.unwrap_node();
                if let Some(mut tll_n) = top_level_layout.find_node_mut(&pge.name) {
                    tll_n.layout.pos = n.layout.pos;
                    tll_n.layout.bb_pos = n.layout.bb_pos;

                    let pge2 = tll_n.unwrap_node_mut();
                    pge2.style.dimensions = pge.style.dimensions;
                }
            };
        } else {
            top_level_layout.accumulate_positions(0, 0);
        };

        top_level_layout
    }

    fn draw_instr_box<'a>(&self, tid: usize, po: &usize, instr: &GridChild<'a>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let GridNode::SubCluster(cluster) = &instr.node {
            let opcode_q: String = "??? ???,[???]".to_string();
            let mut opcode: &String = &opcode_q;

            let mut tl: (i64,i64) = (i64::MAX,i64::MAX);
            let mut br: (i64,i64) = (0, 0);
            // find top-left
            for n in cluster.iter_nodes(false, true) {
                if let GridNode::Node(pgn) = &n.node {
                    if let Some(ev) = pgn.ev {
                        // put the actual disassembled instruction (if available)
                        // otherwise only include the opcode
                        opcode = ev.instr.as_ref().unwrap_or(&ev.opcode);
                    }

                    let (nw,nh) = (pgn.compute_width() as i64, pgn.compute_height() as i64);

                    // use the pos of the bounding box
                    // not the centre of the node
                    if let Some((x,y)) = n.layout.bb_pos {
                        let (x, y) = (x as i64, y as i64);

                        if br.0 < x+nw {
                            br.0 = x+nw;
                        }

                        if br.1 < y+nh {
                            br.1 = y+nh;
                        }

                        if x < tl.0 {
                            tl.0 = x;
                        }

                        if y < tl.1 {
                            tl.1 = y;
                        }
                    };
                };
            };

            let (x, y) = tl;
            let (w, h) = (br.0 - tl.0, br.1 - tl.1);

            // border 0.5 inch around events
            // enough for whitespace and a label
            let wiggle = (SCALE / 2.0) as i64;

            let (llx, lly) = (x-wiggle,y+h+wiggle);
            let (urx, ury) = (x+w+wiggle,y-wiggle);

            writeln!(f, "subgraph cluster{}_{} {{", tid, po)?;
            writeln!(f, "    label = \"{}\";", opcode)?;
            writeln!(f, "    graph [bb=\"{},{},{},{}\"];", llx, -lly, urx, -ury)?;
            writeln!(f, "    style=dashed;")
        } else {
            panic!("draw_instr_box should be passed a GraphLayout")
        }
    }
}

/// given a relation as a set of pairs of nodes
/// weed out transitive edges
fn transitively_reduce<'ev>(edges: &Vec<&'ev (String,String)>) -> Vec<(&'ev String,&'ev String)> {
    // to |-> {from0, from1, from2}
    let mut pairs: HashMap<&String,HashSet<&String>> = HashMap::new();

    for (from, to) in edges {
        let s = pairs.entry(to).or_insert(HashSet::new());
        s.insert(from);
    }

    let old_pairs = pairs.clone();
    for (_to, froms) in pairs.iter_mut() {
        let all_froms = froms.clone();
        for f in all_froms.iter() {
            // look for `other` in froms
            // such that `f |-> other |-> to
            for other_f in all_froms.iter() {
                if let Some(s) = old_pairs.get(other_f) {
                    if s.contains(f) {
                        froms.remove(f);
                    }
                }
            }
        }
    }

    let mut v = Vec::new();
    for (to, froms) in pairs.into_iter() {
        for f in froms {
            v.push((f,to));
        }
    }

    v
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
    ///        +------------------------------------------------+
    ///        |                STR X0,[X1]                     |
    /// row0   |          [T]     [T]     [T]     [T]           |
    /// row1   |  [T]     [T]     [T]     [T]     [T]           |
    /// row2   |  [T]     [T]     [T]     [T]     [T]           |
    /// row3   |  [T]     [T]     [T]     [T]     [T]           |
    /// row4   |  [T]     [T]     [T]     [T]     [T]     [W]   |
    ///        |                                                |
    ///        +------------------------------------------------+
    ///
    ///
    /// Nodes are written like [label]
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "digraph Exec {{")?;
        writeln!(f, "    splines=true;")?;
        writeln!(f, "    node [fontsize=24];")?;
        writeln!(f, "    edge [fontsize=16];")?;

        log!(log::VERBOSE, "writing digraph...");

        // keep track of all the PAs that were touched (written to)
        // in the execution, so we can decide whether to show an event later
        // or whether to use an event in layouting.
        let mut mutated_pas = HashSet::new();

        let mut thread_ids = HashSet::new();
        for ev in self.events.values() {
            thread_ids.insert(ev.thread_id);

            // collect PAs from various write events.
            match &ev.event_kind {
                GraphEventKind::WriteMem(_) => {
                    if let Some(v) = &ev.value {
                        if let Some(addr) = &v.address {
                            mutated_pas.insert(addr);
                        }
                    }
                },
                _ => {},
            }
        }

        // collect all event names which access a location written to in the test
        let mutated_pas_event_names: HashSet<&String> =
            self.events.values()
            .flat_map(|ev|
                match &ev.value {
                    Some(GraphValue { address: Some(addr), ..}) if mutated_pas.contains(addr) =>
                        Some(&ev.name),
                    _ =>
                        None,
                }
            )
            .collect();

        let node_layout = self.produce_node_layout(&self.opts, mutated_pas);
        let graph_event_nodes = node_layout.iter_nodes(true, false);
        log!(log::VERBOSE, "produced node layout");

        if let Some(iw) = node_layout.children.get(&(0,0)) {
            writeln!(f, "{};", iw.fmt_as_node())?;
        }

        if let Some(GridChild { node: GridNode::SubCluster(thread_clusters), .. }) = node_layout.children.get(&(1,0)) {
            let mut displayed_event_names: HashSet<String> = HashSet::new();
            displayed_event_names.insert("IW".to_string());

            let displayed_graph_events: Vec<&GraphEvent> =
                graph_event_nodes
                .iter()
                .flat_map(|c|
                    match c.node {
                        GridNode::Node(PositionedGraphNode { ev: Some(ev), .. }) => Some(ev),
                        _ => None,
                    }
                ).collect();

            for tid in thread_ids {
                let mut events: Vec<&GraphEvent> = self.events.values().filter(|ev| ev.thread_id == tid).collect();
                &events.sort_by(|ev1, ev2| (ev1.thread_id, ev1.po, ev1.iio).cmp(&(ev2.thread_id, ev2.po, ev2.iio)));

                let displayed_thread_events: Vec<&GraphEvent> =
                    displayed_graph_events.clone()
                    .into_iter()
                    .filter(|ge| ge.thread_id == tid)
                    .collect();

                // draw the events and boxes
                if let Some(GridChild { node: GridNode::SubCluster(thread), .. }) = thread_clusters.children.get(&(0,tid)) {
                    for ((po_row, _), instr) in thread.children.iter() {
                        if let GridNode::SubCluster(instr_cluster) = &instr.node {
                            if let Some(po) = instr_cluster.po() {
                                let displayed_instr_events: Vec<&GraphEvent> =
                                    displayed_thread_events.clone()
                                    .into_iter()
                                    .filter(|ge| ge.po == po)
                                    .collect();

                                if displayed_instr_events.len() > 1 {
                                    self.draw_instr_box(tid, po_row, &instr, f)?;
                                }

                                for ev in instr_cluster.children.values() {
                                    writeln!(f, "    {};", ev.fmt_as_node())?;
                                }

                                if displayed_instr_events.len() > 1 {
                                    writeln!(f, "}}")?;
                                }
                            }
                        }
                    }
                }



                for ev in &displayed_thread_events {
                    displayed_event_names.insert(ev.name.clone());
                }
            }

            log!(log::VERBOSE, "finished nodes, now writing relations...");

            for to_show in &self.show {
                for rel in &self.relations {
                    let mut symmetric_edges: HashSet<(String, String)> = HashSet::new();

                    if rel.name == *to_show && !rel.edges.is_empty() {
                        // some of the edges are to hidden nodes
                        // so we simply hide the edges
                        let show_edges: Vec<&(String,String)> = rel.edges.iter().filter(|(from,to)| displayed_event_names.contains(from) && displayed_event_names.contains(to)).collect();
                        let edges = transitively_reduce(&show_edges);
                        log!(log::VERBOSE, &format!("rel {}: edges = {:?}", rel.name, edges));
                        for (from, to) in edges.into_iter() {
                            // do not show IW -(rf)-> R
                            // when R's addr is not written by the test
                            if rel.name.ends_with("rf") && from == "IW" && !mutated_pas_event_names.contains(to) {
                                continue
                            }

                            let dir = if rel.edges.contains(&(to.clone(), from.clone())) {
                                if symmetric_edges.contains(&(to.clone(), from.clone())) {
                                    continue
                                } else {
                                    symmetric_edges.insert((from.clone(), to.clone()));
                                }
                                "dir=both,"
                            } else {
                                ""
                            };

                            let color = relation_color(&rel.name);
                            writeln!(
                                f,
                                " {} -> {} [{}color={}, label=\"  {}  \", fontcolor={}];",
                                from, to, dir, color, rel.name, color
                            )?;
                        }
                    }
                }
            }
        }

        log!(log::VERBOSE, "graph done");
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
    let regnamestr = register_name_string(ev.base().unwrap_or_else(|| panic!("multi-base events?")), symtab);
    regnamestr.map(Val::String)
}

/// get tag (T | R | IF | etc) from a read event
/// isla simply outputs one ReadMem() event for all of them.
fn tag_from_read_event<'a, B: BV>(ev: &AxEvent<B>) -> &'a str {
    if ev.is_ifetch {
        "IF"
    } else if relations::is_translate(ev) {
        "Tr"
    } else {
        "R"
    }
}

/// generate an initial graph from a candidate
/// without any symbolic parts filled in
fn concrete_graph_from_candidate<'ir, B: BV>(
    exec: &ExecutionInfo<B>,
    _footprints: &HashMap<B, Footprint>,
    litmus: &Litmus<B>,
    cat: &cat::Cat<cat::Ty>,
    _ifetch: bool,
    opts: &GraphOpts,
    symtab: &'ir Symtab,
) -> Result<Graph, GraphError> {
    // there is no z3 model to interpret the values from
    // so we instead look through the candidate to see what information
    // we can show to the user for debugging help
    let mut events: HashMap<String, GraphEvent> = HashMap::new();

    for event in exec.events.iter() {
        match event.base().unwrap_or_else(|| panic!("multi-base events?")) {
            Event::ReadMem { value, address, bytes, .. } => {
                let event_name = tag_from_read_event(event);
                let graphvalue = GraphValue::from_vals(event_name, Some(address), *bytes, Some(value));

                events.insert(
                    event.name.clone(),
                    GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                );
            },
            Event::WriteMem { data, address, bytes, .. } => {
                let graphvalue = GraphValue::from_vals("W", Some(address), *bytes, Some(data));

                events.insert(
                    event.name.clone(),
                    GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                );
            },
            Event::ReadReg(_name, _, val) => {
                if opts.include_all_events {
                    let fieldval = regname_val(event, symtab).unwrap();
                    let graphvalue = GraphValue::from_vals("Rreg", Some(&fieldval), 8, Some(val));
                    events.insert(
                        event.name.clone(),
                        GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                    );
                };
            },
            Event::WriteReg(_name, _, val) => {
                if opts.include_all_events {
                    let fieldval = regname_val(event, symtab).unwrap();
                    let graphvalue = GraphValue::from_vals("Wreg", Some(&fieldval), 8, Some(val));
                    events.insert(
                        event.name.clone(),
                        GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                    );
                };
            },
            Event::Barrier { .. } => {
                events.insert(
                    event.name.clone(),
                    GraphEvent::from_axiomatic(event, &litmus.objdump, None)
                );
            },
            Event::CacheOp { address, .. } => {
                let graphvalue = GraphValue::from_vals("C", Some(address), 8, None);
                events.insert(
                    event.name.clone(),
                    GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                );
            },
            _ => {
                if opts.include_all_events {
                    events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, None));
                } else {
                    panic!("concrete_graph_from_candidate unknown graph event: {:?}", event);
                }
            }
        }
    }

    Ok(Graph {
        events: events,
        sets: vec![],
        relations: vec![],
        show: cat.shows(),
        opts: opts.clone(),
    })
}

/// run an interpretation function over the symbolic events
/// to generate new nodes in the graph
fn update_graph_symbolic_events<'m, 'ev, Fev, Frel, B>(
    exec: &'ev ExecutionInfo<B>,
    litmus: &Litmus<B>,
    ifetch: bool,
    opts: &GraphOpts,
    cat: &cat::Cat<cat::Ty>,
    mut model: Option<Model<'_, 'ev, B>>,
    mut g: Graph,
    interpret: Fev,
    interpret_rel: Frel,
) -> Graph
where
    B: BV,
    Fev: Fn(&mut Option<Model<'_, 'ev, B>>, GraphValue, &str, &str, &Val<B>, u32, &Val<B>) -> GraphValue,
    Frel: Fn(&mut Option<Model<'_, 'ev, B>>, &str, &Vec<&'ev str>) -> GraphRelation,
{
    let mut builtin_relations = vec!["po", "rf", "co", "trf", "trf1", "trf2", "same-va-page", "same-ipa-page", "tlbi-same-va-page"];
    if ifetch {
        builtin_relations.push("fpo");
        builtin_relations.push("irf");
    }

    let mut event_names: Vec<&'ev str> = exec.events.iter().map(|ev| ev.name.as_ref()).collect();
    event_names.push("IW");

    // collect all relations from the builtins and from the cat `show`s
    // nubing away duplicates
    let show_rels: Vec<&str> = g.show.iter().map(String::as_str).collect();
    for rel in cat.relations().into_iter().chain(show_rels).chain(builtin_relations).collect::<HashSet<&str>>() {
        g.relations.push(interpret_rel(&mut model, rel, &event_names));
    }

    for event in exec.events.iter() {
        match event.base() {
            Some(Event::ReadMem { value, address, bytes, .. }) => {
                if value.is_symbolic() || address.is_symbolic() {
                    // the event will already exist in the graph
                    // but some of the fields may be empty
                    let gev = g.events.remove(&event.name).unwrap();
                    let gval = gev.value.unwrap();
                    let event_kind_name = tag_from_read_event(event);
                    let graphvalue = interpret(&mut model, gval, &event.name, event_kind_name, address, *bytes, value);
                    g.events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
                }
            },
            Some(Event::WriteMem { data, address, bytes, .. }) => {
                if data.is_symbolic() || address.is_symbolic() {
                    let gevent = g.events.remove(&event.name).unwrap();
                    let gval = gevent.value.unwrap();
                    let graphvalue = interpret(&mut model, gval, &event.name, "W", address, *bytes, data);
                    g.events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
                }
            },
            Some(Event::ReadReg(_, _, val)) => {
                if opts.include_all_events && val.is_symbolic() {
                    let gevent = g.events.remove(&event.name).unwrap();
                    let gval = gevent.value.unwrap();
                    let tempval: Val<B> = Val::Unit;
                    let graphvalue = interpret(&mut model, gval, &event.name, "Rreg", &tempval, 8, val);
                    g.events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
                }
            },
            Some(Event::WriteReg(_, _, val)) => {
                if opts.include_all_events && val.is_symbolic() {
                    let gevent = g.events.remove(&event.name).unwrap();
                    let gval = gevent.value.unwrap();
                    let tempval: Val<B> = Val::Unit;
                    let graphvalue = interpret(&mut model, gval, &event.name, "Wreg", &tempval, 8, val);
                    g.events.insert(event.name.clone(), GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue)));
                }
            },
            Some(Event::CacheOp { address, .. }) => {
                if address.is_symbolic() {
                    let gevent = g.events.remove(&event.name).unwrap();
                    let gval = gevent.value.unwrap();
                    let tempval: Val<B> = Val::Unit;
                    let graphvalue = interpret(&mut model, gval, &event.name, "C", address, 8, &tempval);
                    g.events.insert(
                        event.name.clone(),
                        GraphEvent::from_axiomatic(event, &litmus.objdump, Some(graphvalue))
                    );
                }
            },
            _ => (),
        }
    };

    update_event_kinds(&mut g.events);
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
                ifetch,
                opts,
                cat,
                None,
                g,
                |_m, gv, _ev, prefix, address, bytes, value| {
                    // so just fill those fields that were empty in
                    GraphValue::from_fields(prefix, gv.address.or_else(|| Some(address.to_string(symtab))), bytes, gv.value.or_else(|| Some(value.to_string(symtab))))
                },
                |_m, rel, _events| {
                    GraphRelation {
                        name: (*rel).to_string(),
                        edges: HashSet::new(),
                    }
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
    let model_buf: &str = &z3_output[3..];
    let model = Model::<B>::parse(&event_names, model_buf).ok_or(SmtParseError)?;

    match concrete_graph_from_candidate(exec, footprints, litmus, cat, ifetch, opts, symtab) {
        Err(e) => Err(e),
        Ok(g) => Ok(
            update_graph_symbolic_events(
                exec,
                litmus,
                ifetch,
                opts,
                cat,
                Some(model),
                g,
                |m, gv, ev, prefix, _address, bytes, _value| {
                    if let Some(m) = m {
                        let val =
                            match gv.value {
                                Some(v) => Some(v),
                                None => Some(
                                    String::from(
                                        m
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
                                        m
                                        .interpret(&format!("{}:address", ev), &[])
                                        .map(SexpVal::into_truncated_string)
                                        .unwrap_or_else(|_| "?".to_string())
                                    )
                                ),
                            };

                        // so just fill those fields that were empty in
                        GraphValue::from_fields(prefix, addr, bytes, val)
                    } else {
                        unreachable!()
                    }
                },
                |m, rel, events| {
                    if let Some(m) = m {
                        match m.interpret_rel(rel, events) {
                            Ok(edges) => GraphRelation {
                                name: (*rel).to_string(),
                                edges: edges.iter().map(|(from, to)| ((*from).to_string(), (*to).to_string())).collect(),
                            },
                            Err(err) => {
                                eprintln!("Failed to interpret {}: {}", rel, err) ;
                                GraphRelation {
                                    name: (*rel).to_string(),
                                    edges: HashSet::new(),
                                }
                            },
                        }
                    } else {
                        unreachable!()
                    }
                }
            )
        ),
    }
}
