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

use isla_lib::bitvector::BV;
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::smt::{register_name_string, Event};

use crate::axiomatic::model::Model;
use crate::axiomatic::relations;
use crate::axiomatic::{AxEvent, ExecutionInfo, Pairs, ThreadId};
use crate::footprint_analysis::Footprint;
use crate::litmus::{instruction_from_objdump, Objdump};
use crate::litmus::{Litmus, LitmusGraphOpts};
use crate::page_table::PageAttrs;
use crate::sexp::{InterpretError, SexpVal};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphOpts {
    pub compact: bool,
    pub smart_layout: bool,
    pub show_regs: HashSet<String>,
    pub flatten: bool,
    pub debug: bool,
    pub show_all_reads: bool,
    pub shows: Option<Vec<String>>,
    pub padding: Option<HashMap<String, f64>>,
    pub force_show_events: Option<Vec<String>>,
    pub force_hide_events: Option<Vec<String>>,
    pub squash_translation_labels: bool,
    pub control_delimit: bool,
    pub human_readable_values: bool,
}

impl GraphOpts {
    pub const DEFAULT_SHOW_REGS: &'static [&'static str] = &[
        "R0", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15", "R16",
        "R18", "R18", "R19", "R20", "R21", "R22", "R23", "R24", "R25", "R26", "R27", "R28", "R29", "R30", "R31", "SP",
        "SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3", "VBAR_EL1", "VBAR_EL2",
    ];

    pub const ARMV8_ADDR_TRANS_SHOW_REGS: &'static [&'static str] =
        &["TTBR0_EL1", "TTBR1_EL1", "TTBR0_EL2", "VTTBR_EL2"];

    /// by default we transitively reduce some relations to make them smaller
    /// can explicitly do this by postfixing a relation with -
    /// can also do the opposite by postfixing a relation with + to get the transitive closure instead.
    pub const DEFAULT_REL_TRANSITIVE_REDUCE: &'static [&'static str] =
        &["po", "iio", "co", "wco", "fpo", "instruction-order"];
}

#[derive(Debug)]
pub struct GraphValueNames<T> {
    /// names associated with translation tables and their entries
    pub s1_ptable_names: HashMap<T, String>,
    pub s2_ptable_names: HashMap<T, String>,
    /// names associated with physical addresses
    pub pa_names: HashMap<T, String>,
    /// names associated with intermediate-physical addresses
    pub ipa_names: HashMap<T, String>,
    /// names associated with virtual addresses
    pub va_names: HashMap<T, String>,
    /// buckets as unions of the above buckets
    /// for addresses and values
    pub value_names: HashMap<T, String>,
    pub paddr_names: HashMap<T, String>, // names for physical addresses
}

impl GraphValueNames<u64> {
    fn populate_values(&mut self) {
        let mut hm = HashMap::new();
        hm.extend(self.va_names.iter().map(|(i, s)| (*i, s.clone())));
        hm.extend(self.ipa_names.iter().map(|(i, s)| (*i, s.clone())));
        hm.extend(self.pa_names.iter().map(|(i, s)| (*i, s.clone())));
        self.value_names = hm;
    }

    fn populate_addrs(&mut self) {
        let mut hm = HashMap::new();
        hm.extend(self.s1_ptable_names.iter().map(|(i, s)| (*i, s.clone())));
        hm.extend(self.s2_ptable_names.iter().map(|(i, s)| (*i, s.clone())));
        hm.extend(self.pa_names.iter().map(|(i, s)| (*i, s.clone())));
        self.paddr_names = hm;
    }
}

impl<B: BV> GraphValueNames<B> {
    fn to_u64(&self) -> GraphValueNames<u64> {
        let mut gvn = GraphValueNames {
            s1_ptable_names: self.s1_ptable_names.iter().map(|(k, v)| (k.lower_u64(), v.clone())).collect(),
            s2_ptable_names: self.s2_ptable_names.iter().map(|(k, v)| (k.lower_u64(), v.clone())).collect(),
            pa_names: self.pa_names.iter().map(|(k, v)| (k.lower_u64(), v.clone())).collect(),
            ipa_names: self.ipa_names.iter().map(|(k, v)| (k.lower_u64(), v.clone())).collect(),
            va_names: self.va_names.iter().map(|(k, v)| (k.lower_u64(), v.clone())).collect(),
            value_names: HashMap::new(),
            paddr_names: HashMap::new(),
        };
        gvn.populate_values();
        gvn.populate_addrs();
        gvn
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GraphValue {
    prefix: String,
    address: Option<String>,
    virtual_address: Option<String>,
    bytes: String,
    value: Option<String>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct WriteKind {
    pub to_translation_table_entry: Option<usize>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct TranslateKind {
    pub stage: usize,
    pub level: usize, // TODO: BS: what about level -1 ?
    // for s2 translations during a s1 walk
    // which level of the s1 are we at
    pub for_s1: Option<usize>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum BarrierKind {
    // an actual fence instruction
    Fence,
    // taking an exception
    Fault,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum GraphEventKind {
    Ifetch,
    ReadMem,
    WriteMem(WriteKind),
    Translate(TranslateKind),
    ReadReg,
    WriteReg,
    Barrier(BarrierKind),
    CacheOp,
    Info, // for events that are purely decorative
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

fn event_kind<B: BV>(_objdump: &Objdump, ev: &AxEvent<B>) -> GraphEventKind {
    match ev.base.last() {
        Some(Event::WriteMem { region, .. }) => {
            if region == &"stage 1" {
                GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: Some(1) })
            } else if region == &"stage 2" {
                GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: Some(2) })
            } else {
                GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: None })
            }
        }
        Some(Event::ReadMem { region, .. }) => {
            if ev.is_ifetch {
                GraphEventKind::Ifetch
            } else if relations::is_translate(ev) && region == &"stage 1" {
                GraphEventKind::Translate(TranslateKind { stage: 1, level: 0, for_s1: None })
            } else if relations::is_translate(ev) && region == &"stage 2" {
                GraphEventKind::Translate(TranslateKind { stage: 2, level: 0, for_s1: None })
            } else {
                GraphEventKind::ReadMem
            }
        }
        Some(Event::ReadReg(_, _, _)) => GraphEventKind::ReadReg,
        Some(Event::WriteReg(_, _, _)) => GraphEventKind::WriteReg,
        _ => GraphEventKind::Info,
    }
}

fn update_event_kinds(evs: &mut HashMap<String, GraphEvent>) {
    let mut events: Vec<&mut GraphEvent> = evs.iter_mut().map(|(_, v)| v).collect();
    events.sort_by(|ev1, ev2| (ev1.thread_id, ev1.po, ev1.iio).cmp(&(ev2.thread_id, ev2.po, ev2.iio)));

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
            GraphEventKind::Translate(TranslateKind { stage: 1, ref mut level, .. }) => {
                *level = s1level;
                s1level += 1;
                s2level = 0;
            }
            GraphEventKind::Translate(TranslateKind { stage: 2, ref mut level, ref mut for_s1 }) => {
                *level = s2level;
                s2level += 1;
                *for_s1 = Some(s1level);
            }
            _ => {}
        }
    }
}

fn _bv_field_diffs<PA: PageAttrs>(
    desc: u64,
    target: PA,
    fields: &'static [(&'static str, u64, u64)],
) -> Vec<(&'static str, u64, u64)> {
    let (s, _) = target.bits();
    let mut diff = vec![];
    for (name, top, bot) in fields {
        let fieldmask = (1 << (top - bot + 1)) - 1;
        let db = (desc >> bot) & fieldmask;
        let tb = (s >> bot) & fieldmask;

        diff.push((*name, db, tb))
    }
    diff
}

fn _bv_dist(v: &[(&'static str, u64, u64)]) -> u64 {
    let mut diff: u64 = 0;

    for (_, expected, actual) in v.iter() {
        for i in 0..7 {
            diff += ((actual >> i) & 0b1) ^ ((expected >> i) & 0b1);
        }
    }

    diff
}

fn try_guess_descriptor(opts: &GraphOpts, names: &HashMap<u64, String>, desc: u64) -> String {
    use crate::page_table::{S1PageAttrs, S2PageAttrs};

    if (!opts.human_readable_values) || desc < 10 {
        return format!("0x{:x}", desc);
    }

    let addr = (desc >> 12) & ((1 << (49 - 12 + 1)) - 1);
    let addrstr = named_str_from_addr(opts, names, &format!("0x{:x}", addr));
    let dists = vec![
        _bv_field_diffs(desc, S1PageAttrs::default(), S1PageAttrs::fields()),
        _bv_field_diffs(desc, S1PageAttrs::code(), S1PageAttrs::fields()),
        _bv_field_diffs(desc, S2PageAttrs::default(), S2PageAttrs::fields()),
        _bv_field_diffs(desc, S2PageAttrs::code(), S2PageAttrs::fields()),
    ];

    let (dist, fields) = dists.into_iter().map(|t| (_bv_dist(&t), t)).min_by_key(|(k, _)| *k).unwrap();

    // if "too far" from a built-in descriptor
    // just print the hex
    if dist > 12 {
        return format!("0x{:x}", desc);
    }

    let mut args = vec![];
    for (fieldname, expected_field, actual_field) in fields {
        if expected_field != actual_field {
            args.push(format!("{}=0x{:x}", fieldname, actual_field));
        }
    }
    args.push(format!("addr={}", addrstr));

    format!("mkdesc({})", args.join(", "))
}

fn named_str_from_value(opts: &GraphOpts, names: &HashMap<u64, String>, v: &str) -> String {
    match u64::from_str_radix(&v[2..v.len()], 16) {
        Err(_) => v.to_string(),
        Ok(i) => match names.get(&i) {
            Some(s) => s.clone(),
            None => try_guess_descriptor(opts, names, i),
        },
    }
}

fn named_str_from_addr(_opts: &GraphOpts, names: &HashMap<u64, String>, v: &str) -> String {
    match u64::from_str_radix(&v[2..v.len()], 16) {
        Err(_) => v.to_string(),
        Ok(i) => match names.get(&i) {
            Some(s) => s.clone(),
            None => v.to_string(),
        },
    }
}

fn str_from_value<B: BV>(v: &Val<B>) -> String {
    if !v.is_symbolic() {
        match v {
            Val::String(s) => s.clone(),
            _ => {
                let valu: &B = v.as_bits().expect("value was not a bitvector");
                format!("0x{:x}", valu)
            }
        }
    } else {
        "?symbolic?".to_string()
    }
}

impl GraphValue {
    pub fn from_fields(
        prefix: &str,
        address: Option<String>,
        virtual_address: Option<String>,
        bytes: u32,
        value: Option<String>,
    ) -> Self {
        GraphValue { prefix: prefix.to_string(), address, bytes: format!("{}", bytes), value, virtual_address }
    }

    pub fn from_vals<B: BV>(prefix: &str, address: Option<&Val<B>>, bytes: u32, value: Option<&Val<B>>) -> Self {
        let addr = if let Some(addr) = address {
            if !addr.is_symbolic() {
                Some(str_from_value(addr))
            } else {
                None
            }
        } else {
            None
        };

        let value = if let Some(val) = value {
            if !val.is_symbolic() {
                Some(str_from_value(val))
            } else {
                None
            }
        } else {
            None
        };

        Self::from_fields(prefix, addr, None, bytes, value)
    }
}

impl GraphEvent {
    /// Create an event to display in a user-visible graph from an
    /// underlying axiomatic event. For display, we use the objdump
    /// output to find the human-readable assembly instruction
    pub fn from_axiomatic<'a, B: BV>(ev: &'a AxEvent<B>, objdump: &Objdump, value: Option<GraphValue>) -> Self {
        let instr = instruction_from_objdump(&format!("{:x}", ev.opcode), objdump);
        GraphEvent {
            instr,
            opcode: format!("{}", ev.opcode),
            po: ev.instruction_index,
            iio: ev.intra_instruction_index,
            thread_id: ev.thread_id,
            name: ev.name.clone(),
            value,
            event_kind: event_kind(objdump, ev),
        }
    }
}

#[derive(Debug, Clone)]
pub struct GraphSet {
    pub name: String,
    pub elems: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct GraphRelation {
    pub name: String,
    pub ty: RelType,
    pub edges: HashSet<(String, String)>,
}

#[derive(Debug)]
pub struct Graph {
    pub events: HashMap<String, GraphEvent>, // EventName -> Event
    pub sets: Vec<GraphSet>,
    pub relations: Vec<GraphRelation>,
    pub show: Vec<String>,
    pub opts: GraphOpts,              // options from cmdline
    pub litmus_opts: LitmusGraphOpts, // options from litmus file itself
    pub names: GraphValueNames<u64>,
}

fn extra_color(rel: &str) -> &'static str {
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

    // always use the same color
    let n: usize = rel.chars().map(|c| c as usize).sum();
    colors[n % colors.len()]
}

fn relation_color(rel: &str) -> &'static str {
    match rel {
        "po" => "black",
        "iio" => "black",
        "rf" => "crimson",
        "trf" => "maroon",
        "co" => "brown",
        "wco" => "black",
        "fr" => "goldenrod",
        "tfr" => "goldenrod4",
        "addr" => "midnightblue",
        "data" => "midnightblue",
        "ctrl" => "midnightblue",
        "rmw" => "firebrick4",
        "same-va-page" => "purple",
        "same-ipa-page" => "purple4",
        _ => extra_color(rel),
    }
}

#[derive(Debug, Copy, Clone)]
pub enum RelType {
    TransClosure,
    TransReduction,
    Normal,
}

/// given a relation name return (base, type)
fn parse_relname_opt(rel: &str) -> (&str, RelType) {
    if rel.ends_with('-') {
        (&rel[0..rel.len() - 1], RelType::TransReduction)
    } else if rel.ends_with('+') {
        (&rel[0..rel.len() - 1], RelType::TransClosure)
    } else if rel.ends_with('~') {
        (&rel[0..rel.len() - 1], RelType::Normal)
    } else {
        let trans_reductions: HashSet<String> =
            GraphOpts::DEFAULT_REL_TRANSITIVE_REDUCE.iter().cloned().map(String::from).collect();
        if trans_reductions.contains(rel) {
            (rel, RelType::TransReduction)
        } else {
            (rel, RelType::Normal)
        }
    }
}

fn event_style(ev: &GraphEvent) -> Style {
    // TODO: BS: do we want to colour-code event types?
    // e.g. Ts2 => wheat1, Ts1 => darkslategray1
    match ev.event_kind {
        GraphEventKind::Translate(_) if true => Style {
            bg_color: "darkslategray1".to_string(),
            node_shape: "box".to_string(),
            node_style: "filled".to_string(),
            dimensions: (0.0, 0.0),
        },
        GraphEventKind::Translate(TranslateKind { stage: 1, .. })
        | GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: Some(1) }) => Style {
            bg_color: "white".to_string(),
            node_shape: "box".to_string(),
            node_style: "filled".to_string(),
            dimensions: (0.0, 0.0),
        },
        GraphEventKind::Translate(TranslateKind { stage: 2, .. })
        | GraphEventKind::WriteMem(WriteKind { to_translation_table_entry: Some(2) }) => Style {
            bg_color: "white".to_string(),
            node_shape: "box".to_string(),
            node_style: "filled".to_string(),
            dimensions: (0.0, 0.0),
        },
        _ => Style {
            bg_color: "white".to_string(),
            node_shape: "box".to_string(),
            node_style: "filled".to_string(),
            dimensions: (0.0, 0.0),
        },
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
    Left,
    Middle,
    Right,
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
    children: HashMap<(usize, usize), GridChild<'a>>,
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
    /// the (event label, sublabel) pair
    ev_label: (String, String),
    /// the row/column in the subgrid
    grid_rc: (usize, usize),
    /// style information about the node
    /// to be passed to graphviz
    style: Style,
}

const FONTSIZE: usize = 44;
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
        (FONTSIZE * 3 / 5) * self.label.len()
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
            GridNode::Node(pgn) => pgn.compute_width() + ww,
            GridNode::SubCluster(cluster) => cluster.compute_width() + ww,
        }
    }

    /// the height (in points) of the node or the child grid
    fn compute_height(&self) -> usize {
        if self.layout.skinny {
            return 0;
        }

        let wh: usize = points_from_inches(self.layout.padding.up + self.layout.padding.down);
        match &self.node {
            GridNode::Node(pgn) => pgn.compute_height() + wh,
            GridNode::SubCluster(cluster) => cluster.compute_height() + wh,
        }
    }

    /// a graphviz line for an event node
    /// in the following format:
    /// R1_79_0 [shape=box,pos="13,17!",label=<LABEL FORMAT>,fillcolor=wheat1,style=filled];
    fn fmt_as_node(&self) -> String {
        if let GridNode::Node(pge) = &self.node {
            let node_attrs: Vec<(String, String)> = vec![
                ("fillcolor".to_string(), pge.style.bg_color.to_string()),
                ("style".to_string(), pge.style.node_style.to_string()),
                (
                    "pos".to_string(),
                    if let Some((x, y)) = self.layout.pos { format!("\"{},{}!\"", x, -y) } else { "\"\"".to_string() },
                ),
                ("shape".to_string(), pge.style.node_shape.to_string()),
                ("label".to_string(), pge.label.clone()),
                ("width".to_string(), pge.style.dimensions.0.to_string()),
                ("height".to_string(), pge.style.dimensions.1.to_string()),
            ];

            let attrs = node_attrs.iter().map(|(attr, val)| format!("{}={}", attr, val)).collect::<Vec<_>>().join(", ");
            format!("{} [{}]", pge.name, attrs)
        } else {
            "N/A".to_string()
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
        self.children.keys().map(|(r, _)| r).max().map(|x| x + 1).unwrap_or(0)
    }

    fn num_cols(&self) -> usize {
        self.children.keys().map(|(_, c)| c).max().map(|x| x + 1).unwrap_or(0)
    }

    fn compute_max_width_heights(&self) -> (HashMap<usize, usize>, HashMap<usize, usize>) {
        let mut widths: HashMap<usize, usize> = HashMap::new();
        let mut heights: HashMap<usize, usize> = HashMap::new();

        for r in 0..self.num_rows() {
            for c in 0..self.num_cols() {
                let (w, h) = if let Some(child) = self.children.get(&(r, c)) {
                    (child.compute_width(), child.compute_height())
                } else {
                    (0, 0)
                };

                heights.entry(r).or_insert(0);
                widths.entry(c).or_insert(0);

                heights.insert(r, std::cmp::max(heights[&r], h));
                widths.insert(c, std::cmp::max(widths[&c], w));
            }
        }

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
        let mut acc_widths: HashMap<usize, i64> = HashMap::new();
        let mut acc_heights: HashMap<usize, i64> = HashMap::new();

        let mut acc_width: i64 = start_x;
        let mut acc_height: i64 = start_y;

        for r in 0..self.num_rows() {
            acc_heights.insert(r, acc_height);
            acc_height += heights[&r] as i64;
        }

        for c in 0..self.num_cols() {
            acc_widths.insert(c, acc_width);
            acc_width += widths[&c] as i64;
        }

        (acc_widths, acc_heights)
    }

    fn flatten(&mut self) {
        let mut row_exploders: HashMap<usize, usize> = HashMap::new();
        let mut col_exploders: HashMap<usize, usize> = HashMap::new();

        for r in 0..self.num_rows() {
            row_exploders.entry(r).or_insert(1);
            for c in 0..self.num_cols() {
                let node = self.children.get(&(r, c));
                col_exploders.entry(c).or_insert(1);
                if let Some(GridChild { node: GridNode::SubCluster(cluster), .. }) = node {
                    if let Some(v) = col_exploders.insert(c, cluster.num_cols()) {
                        col_exploders.insert(c, std::cmp::max(v, cluster.num_cols()));
                    }
                    if let Some(v) = row_exploders.insert(r, cluster.num_rows()) {
                        row_exploders.insert(r, std::cmp::max(v, cluster.num_rows()));
                    }
                }
            }
        }

        let (cum_cols, cum_rows) = self.accumulate_max_widths_heights(0, 0, &col_exploders, &row_exploders);
        let mut new_children: HashMap<(usize, usize), GridChild> = HashMap::new();
        let mut count_subclusters = 0;

        for ((r, c), child_node) in self.children.drain() {
            let row_start = cum_rows.get(&r).unwrap_or(&0);
            let col_start = cum_cols.get(&c).unwrap_or(&0);
            let (row_start, col_start) = (*row_start as usize, *col_start as usize);
            match child_node.node {
                GridNode::SubCluster(mut cluster) => {
                    count_subclusters += 1;

                    let maxrow: usize = cluster.children.keys().map(|(r, _)| *r).max().unwrap_or(1);
                    let maxcol: usize = cluster.children.keys().map(|(_, c)| *c).max().unwrap_or(1);

                    for ((subrow, subcol), mut n) in cluster.children.drain() {
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

                        match new_children.insert((row_start + subrow, col_start + subcol), n) {
                            None => {}
                            Some(old) => {
                                panic!(
                                    "oops! placed a subcluster child at already-existing addr ({}+{},{}+{}): {:?}",
                                    row_start, subrow, col_start, subcol, old
                                );
                            }
                        }
                    }
                }
                _ => {
                    // if we had a single node and the ones below/above got split up
                    // we have to decide which column to place this single node in now
                    // and we use the alignment to decide ...
                    let new_cols = *col_exploders.get(&c).unwrap();
                    let subcoloffs = match child_node.layout.alignment {
                        Align::Left => 0,
                        Align::Middle => new_cols / 2,
                        Align::Right => new_cols - 1,
                    };

                    match new_children.insert((row_start, col_start + subcoloffs), child_node) {
                        None => {}
                        Some(old) => {
                            panic!("oops! placed a second child at {:?}: {:?}", (row_start, col_start), old);
                        }
                    }
                }
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
    fn accumulate_positions(&mut self, start_x: i64, start_y: i64) {
        let (max_widths, max_heights) = self.compute_max_width_heights();
        let (cum_widths, cum_heights) = self.accumulate_max_widths_heights(start_x, start_y, &max_widths, &max_heights);

        for (&(r, c), mut child) in self.children.iter_mut() {
            let (x, y) = (cum_widths[&c] as i64, cum_heights[&r] as i64);
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
            let xleft = match node_layout.alignment {
                Align::Left => x,
                Align::Middle => x + col_width / 2 - node_width / 2,
                Align::Right => x + col_width - node_width,
            };

            match child.node {
                GridNode::Node(ref mut pgn) => {
                    let (actual_node_width, actual_node_height) =
                        (pgn.compute_width() as i64, pgn.compute_height() as i64);

                    // graphviz "pos" is middle of node
                    // so we +w/2,h/2 to make the pos be the top-left
                    child.layout.bb_pos = Some((xleft, y));
                    child.layout.pos = Some((xleft + wxl + actual_node_width / 2, y + wyu + actual_node_height / 2));
                    pgn.style.dimensions = (
                        inches_from_points(actual_node_width as usize),
                        inches_from_points(actual_node_height as usize),
                    );
                }
                GridNode::SubCluster(ref mut cluster) => {
                    child.layout.bb_pos = Some((x, y));
                    child.layout.pos = Some((x, y));
                    cluster.accumulate_positions(xleft + wxl, y + wyu);
                }
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
                GridNode::Node(_) => nodes.push(c),
                GridNode::SubCluster(cluster) => {
                    let sub_nodes = cluster.iter_nodes(only_visible, only_real);
                    nodes.extend(sub_nodes);
                }
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
                }
            }
        }

        nodes
    }

    fn find_node_mut(&mut self, name: &str) -> Option<&mut GridChild<'g>> {
        for n in self.iter_nodes_mut(false, false) {
            if let GridNode::Node(pge) = &n.node {
                if pge.name == name {
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

    #[allow(dead_code)]
    fn opcode(&self) -> Option<&String> {
        for c in self.iter_nodes(false, false) {
            if let GridNode::Node(pgn) = &c.node {
                if let Some(ev) = pgn.ev {
                    return Some(ev.instr.as_ref().unwrap_or(&ev.opcode));
                }
            }
        }

        None
    }
}

impl GraphEvent {
    fn _name_bag_for_rw_event<'names>(
        &self,
        is_value: bool,
        names: &'names GraphValueNames<u64>,
    ) -> &'names HashMap<u64, String> {
        match &self.event_kind {
            GraphEventKind::Translate(TranslateKind { stage: 1, .. }) => &names.s1_ptable_names,
            GraphEventKind::Translate(TranslateKind { stage: 2, .. }) => &names.s2_ptable_names,
            _ if is_value => &names.value_names,
            _ => &names.paddr_names,
        }
    }

    fn _name_bag_for_addr<'names>(&self, names: &'names GraphValueNames<u64>) -> &'names HashMap<u64, String> {
        self._name_bag_for_rw_event(false, names)
    }

    fn _name_bag_for_value<'names>(&self, names: &'names GraphValueNames<u64>) -> &'names HashMap<u64, String> {
        self._name_bag_for_rw_event(true, names)
    }

    fn _fmt_ttbr(&self, opts: &GraphOpts, v: &GraphValue, names: &GraphValueNames<u64>) -> String {
        let val = v.value.as_ref().unwrap().clone();
        let ttbr = u64::from_str_radix(&val[2..val.len()], 16).expect("got unknown ttbr");
        let asid = ttbr >> 48;
        let base = ttbr & ((1 << 48) - 1);
        format!(
            "ttbr(id=0x{:x}, base={})",
            asid,
            named_str_from_addr(opts, &names.s1_ptable_names, &format!("0x{:x}", base))
        )
    }

    fn fmt_barrier(&self, opts: &GraphOpts, names: &GraphValueNames<u64>) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);

        if let Some(value) = &self.value {
            // was actually a MSR barrier
            format!("{} = {}", instr, self._fmt_ttbr(opts, value, names))
        } else {
            format!("{}", instr)
        }
    }

    // format the node label with all debug info:
    // label="W_00_000: "ldr x2, [x3]": T 0x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_debug(&self, _opts: &GraphOpts, ev_label: &(String, String), rc: (usize, usize)) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        let ev_lab = format!("{}{}", ev_label.0, ev_label.1);
        if let Some(value) = &self.value {
            let q = "?".to_string();
            let addrstr = value.address.as_ref().unwrap_or(&q);
            let valstr = value.value.as_ref().unwrap_or(&q);
            format!(
                "\"{} @ {:?}: \\\"{}\\\": {}\"",
                self.name,
                rc,
                instr,
                format_args!("{}: {} {} ({}): {}", ev_lab, value.prefix, addrstr, value.bytes, valstr)
            )
        } else {
            format!("\"{} @ {:?}: \\\"{}\\\"\"", self.name, rc, instr)
        }
    }

    // format the node label in longform:
    // label="ldr x2, [x3]\lT 0x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_long(&self, opts: &GraphOpts, ev_label: &(String, String), names: &GraphValueNames<u64>) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        let ev_lab = format!("{}{}", ev_label.0, ev_label.1);
        match self.event_kind {
            GraphEventKind::Barrier(BarrierKind::Fault) => format!("\"{}: {}: Fault\"", ev_lab, instr),
            GraphEventKind::Barrier(BarrierKind::Fence) => format!("\"{}: {}\"", ev_lab, self.fmt_barrier(opts, names)),
            GraphEventKind::CacheOp => {
                let q = "?".to_string();
                let addr = if let Some(value) = &self.value { value.value.as_ref().unwrap_or(&q) } else { &q };
                let extra_data = if let Some(value) = &self.value { value.address.as_ref().unwrap_or(&q) } else { &q };

                let addr = u64::from_str_radix(&addr[2..addr.len()], 16).expect("got unknown addr");
                let extra = u64::from_str_radix(&extra_data[2..extra_data.len()], 16).expect("got unknown extra data");
                if instr.contains("va") {
                    format!(
                        "\"{}: {}: page={}\"",
                        ev_lab,
                        instr,
                        named_str_from_addr(opts, &names.va_names, &format!("0x{:x}", addr))
                    )
                } else if instr.contains("ipa") {
                    format!(
                        "\"{}: {}: page={}\"",
                        ev_lab,
                        instr,
                        named_str_from_addr(opts, &names.ipa_names, &format!("0x{:x}", addr))
                    )
                } else if instr.contains("asid") {
                    format!("\"{}: {}: asid=0x{:x}\"", ev_lab, instr, addr >> 48)
                } else if instr.contains("vm") {
                    format!("\"{}: {}: vmid=0x{:x}\"", ev_lab, instr, extra)
                } else {
                    format!("\"{}: {}\"", ev_lab, instr)
                }
            }
            _ => {
                if let Some(value) = &self.value {
                    let q = "?".to_string();
                    let addrstr = value.address.as_ref().unwrap_or(&q);
                    let valstr = value.value.as_ref().unwrap_or(&q);
                    let vastr = if let Some(s) = value.virtual_address.as_ref() {
                        format!("{}/", named_str_from_addr(opts, &names.va_names, s))
                    } else {
                        "".to_string()
                    };
                    format!(
                        "\"{}: {}: {}\"",
                        ev_lab,
                        instr,
                        format_args!(
                            "{} {}{} = {}",
                            value.prefix,
                            vastr,
                            named_str_from_addr(opts, self._name_bag_for_addr(names), addrstr),
                            named_str_from_value(opts, self._name_bag_for_value(names), valstr)
                        )
                    )
                } else {
                    format!("\"{}: {}\"", ev_lab, instr)
                }
            }
        }
    }

    // format the node label in half form:
    // label="T 0x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_medium(&self, opts: &GraphOpts, ev_label: &(String, String), names: &GraphValueNames<u64>) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        let ev_lab = format!("{}{}", ev_label.0, ev_label.1);
        match &self.event_kind {
            GraphEventKind::Barrier(BarrierKind::Fault) => format!("\"{}: {}: Fault\"", ev_lab, instr),
            GraphEventKind::Barrier(BarrierKind::Fence) => format!("\"{}: {}\"", ev_lab, self.fmt_barrier(opts, names)),
            _ => {
                if let Some(value) = &self.value {
                    let q = "?".to_string();
                    let addrstr = value.address.as_ref().unwrap_or(&q);
                    let valstr = value.value.as_ref().unwrap_or(&q);

                    let vastr = if let Some(s) = value.virtual_address.as_ref() {
                        format!("{}/", named_str_from_addr(opts, &names.va_names, s))
                    } else {
                        "".to_string()
                    };

                    format!(
                        "\"{}: {}\"",
                        ev_lab,
                        format_args!(
                            "{} {}{} = {}",
                            value.prefix,
                            vastr,
                            named_str_from_addr(opts, self._name_bag_for_addr(names), addrstr),
                            named_str_from_value(opts, self._name_bag_for_value(names), valstr)
                        )
                    )
                } else {
                    format!("\"??{}:{}\"", self.name, instr)
                }
            }
        }
    }

    // format the node label in shortform:
    // label="T 0x205800"
    #[allow(dead_code)]
    fn fmt_label_short(&self, opts: &GraphOpts, ev_label: &(String, String), names: &GraphValueNames<u64>) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        let ev_lab = format!("{}{}", ev_label.0, ev_label.1);
        match &self.event_kind {
            GraphEventKind::Barrier(BarrierKind::Fault) => format!("\"{}: Fault\"", ev_lab),
            GraphEventKind::Barrier(BarrierKind::Fence) => format!("\"{}: {}\"", ev_lab, self.fmt_barrier(opts, names)),
            GraphEventKind::Translate(TranslateKind { stage, level, .. }) if opts.squash_translation_labels => {
                format!("\"{}: Ts{}l{}\"", ev_lab, stage, level)
            }
            _ => {
                if let Some(value) = &self.value {
                    let q = "?".to_string();
                    let addrstr = value.address.as_ref().unwrap_or(&q);
                    format!(
                        "\"{}: {} {}\"",
                        ev_lab,
                        value.prefix,
                        named_str_from_addr(opts, self._name_bag_for_addr(names), addrstr)
                    )
                } else {
                    format!("\"?{}:{}\"", self.name, instr)
                }
            }
        }
    }
}

fn event_in_shows(shows: &Option<Vec<String>>, ev: &GraphEvent) -> bool {
    if let Some(evs) = shows {
        for show_ev in evs.iter() {
            if show_ev.starts_with('T') {
                /* name like T0:1:s1l3 for translate thread 0, instr 1, s1l3 translate */
                let stripped = show_ev.strip_prefix('T').unwrap();
                let sections: Vec<&str> = stripped.split(':').collect();
                let tid: usize =
                    sections.get(0).expect("expected T0:1:s1l3 format").parse().expect("expected tid to be integer");
                let po: usize =
                    sections.get(1).expect("expected T0:1:s1l3 format").parse().expect("expected po to be integer");
                let sl = sections.get(2).expect("expected T0:1:s1l3 format");
                let stage: usize = sl
                    .chars()
                    .nth(1)
                    .expect("expected stage/level to be sXlY format")
                    .to_string()
                    .parse::<usize>()
                    .expect("expected stage to be integer");
                let level: usize = sl
                    .chars()
                    .nth(3)
                    .expect("expected stage/level to be sXlY format")
                    .to_string()
                    .parse::<usize>()
                    .expect("expected level to be integer");
                if ev.po == po && ev.thread_id == tid {
                    if let GraphEventKind::Translate(TranslateKind { stage: ev_stage, level: ev_level, for_s1 }) =
                        ev.event_kind
                    {
                        if let None | Some(0) = for_s1 {
                            if ev_stage == stage && ev_level == level {
                                return true;
                            }
                        }
                    }
                }
            } else if show_ev == &ev.name {
                return true;
            }
        }
    }

    false
}

impl PositionedGraphNode<'_> {
    // format the node label with all debug info:
    // label="W_00_000: "ldr x2, [x3]": T 0x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_debug(&self, opts: &GraphOpts, rc: (usize, usize), _names: &GraphValueNames<u64>) -> String {
        if let Some(ev) = &self.ev {
            ev.fmt_label_debug(opts, &self.ev_label, rc)
        } else {
            "N/A".to_string()
        }
    }

    // format the node label in longform:
    // label="ldr x2, [x3]\lT 0x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_long(&self, opts: &GraphOpts, names: &GraphValueNames<u64>) -> String {
        if let Some(ev) = &self.ev {
            ev.fmt_label_long(opts, &self.ev_label, names)
        } else {
            "N/A".to_string()
        }
    }

    // format the node label in half form:
    // label="T 0x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_medium(&self, opts: &GraphOpts, names: &GraphValueNames<u64>) -> String {
        if let Some(ev) = &self.ev {
            ev.fmt_label_medium(opts, &self.ev_label, names)
        } else {
            "N/A".to_string()
        }
    }

    // format the node label in shortform:
    // label="T 0x205800"
    #[allow(dead_code)]
    fn fmt_label_short(&self, opts: &GraphOpts, names: &GraphValueNames<u64>) -> String {
        if let Some(ev) = &self.ev {
            ev.fmt_label_short(opts, &self.ev_label, names)
        } else {
            "N/A".to_string()
        }
    }
}

impl Graph {
    fn produce_node_layout<'g>(
        &'g self,
        litmus_opts: &LitmusGraphOpts,
        opts: &GraphOpts,
        pas: HashSet<&String>,
    ) -> GraphLayout<'g> {
        let mut tids = HashSet::new();
        for ev in self.events.values() {
            tids.insert(ev.thread_id);
        }

        let mut thread_ids: Vec<usize> = tids.into_iter().collect();
        thread_ids.sort_unstable();

        let get_pad_or_default = |name: String, default: f64| match &opts.padding {
            Some(hmap) => match hmap.get(&name) {
                Some(f) => {
                    log!(log::GRAPH, format!("using {} for {}", f, &name));
                    *f
                }
                None => default,
            },
            None => default,
        };

        let make_padding = |name: &str, up: f64, down: f64, left: f64, right: f64| Padding {
            up: get_pad_or_default([name, "-", "up"].join(""), up),
            down: get_pad_or_default([name, "-", "down"].join(""), down),
            left: get_pad_or_default([name, "-", "left"].join(""), left),
            right: get_pad_or_default([name, "-", "right"].join(""), right),
        };

        // layout information for the various parts of the graph
        let layout_iw = Layout {
            padding: make_padding("iw", 0.5, 1.0, 0.5, 0.5),
            alignment: Align::Middle,
            pos: None,
            bb_pos: None,
            show: true,
            skinny: false,
        };
        let layout_threads = Layout {
            padding: make_padding("threads", 0.0, 0.0, 0.0, 0.0),
            alignment: Align::Left,
            pos: None,
            bb_pos: None,
            show: true,
            skinny: false,
        };
        let layout_thread = Layout {
            padding: make_padding("thread", 0.0, 0.0, 0.0, 2.0),
            alignment: Align::Left,
            pos: None,
            bb_pos: None,
            show: true,
            skinny: false,
        };
        // space around each instruction for layout space, border and opcode label
        let layout_instr = Layout {
            padding: make_padding("instr", 0.1, 0.45, 0.2, 0.2),
            alignment: Align::Middle,
            pos: None,
            bb_pos: None,
            show: true,
            skinny: false,
        };
        // by aligning events in the middle we make sure arrows up/down the same column are vertical
        let layout_event = Layout {
            padding: make_padding("event", 0.1, 0.1, 0.1, 0.8),
            alignment: Align::Middle,
            pos: None,
            bb_pos: None,
            show: true,
            skinny: false,
        };

        let mut top_level_layout = GraphLayout { children: HashMap::new() };
        let iw_pgn = GridNode::Node(PositionedGraphNode {
            ev: None,
            name: "IW".to_string(),
            ev_label: ("iw".to_string(), "".to_string()),
            style: Style {
                bg_color: "white".to_string(),
                node_shape: "oval".to_string(),
                node_style: "filled".to_string(),
                dimensions: (0.0, 0.0),
            },
            grid_rc: (0, 0),
            label: "\"Initial State\"".to_string(),
        });
        top_level_layout.children.insert((0, 0), GridChild { node: iw_pgn, layout: layout_iw });

        let mut thread_layouts = GraphLayout { children: HashMap::new() };

        // we give each instruction in the graph its own label "a", "b", "c" etc
        // and then each sub-event in that instruction a postfix "a1", "a2" etc
        let mut ev_label_count = 0;
        let ev_labels = "abcdefghijklmnopqrstuvwxyz";

        for tid in thread_ids {
            let mut events: Vec<&GraphEvent> = self.events.values().filter(|ev| ev.thread_id == tid).collect();
            events.sort_by(|ev1, ev2| (ev1.thread_id, ev1.po, ev1.iio).cmp(&(ev2.thread_id, ev2.po, ev2.iio)));

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
                        (last_instr_row, 0),
                        GridChild {
                            node: GridNode::SubCluster(GraphLayout { children: current_thread_instructions }),
                            layout: layout_instr.clone(),
                        },
                    );
                    current_thread_instructions = HashMap::new();

                    if iio_show_count > 0 {
                        ev_label_count += 1;
                    }

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
                            if !opts.show_all_reads && !pas.contains(&addr) && !opts.debug {
                                show = false;
                            }
                        }
                    }
                };

                if let GraphEventKind::Barrier(BarrierKind::Fence) = ev.event_kind {
                    if let Some(i) = &ev.instr {
                        if i.to_lowercase().contains("msr") && !i.to_lowercase().contains("ttbr") && !opts.debug {
                            show = false;
                        }
                    }
                }

                // check file first, so that cmdline can overrule later ...
                if event_in_shows(&litmus_opts.force_show_events, ev) {
                    show = true;
                }

                if event_in_shows(&opts.force_hide_events, ev) {
                    show = false;
                }

                if event_in_shows(&opts.force_show_events, ev) {
                    show = true;
                }

                // if skinny then this node pretends to have 0width and 0height
                // and therefore mostly doesn't influence the layouter later
                let skinny = if show { false } else { opts.compact };

                let rc = if opts.smart_layout {
                    // we fix a layout per instruction:
                    //       0   1   2   3   4   5   6
                    //  0   IF      S2  S2  S2  S2
                    //  1       S1  S2  S2  S2  S2
                    //  2       S1  S2  S2  S2  S2
                    //  3       S1  S2  S2  S2  S2
                    //  4       S1  S2  S2  S2  S2   RW
                    //
                    // or if there's only S1 translates:
                    //       0   1   2   3   4   5
                    //  0   IF  S1  S1  S1  S1  RW
                    match ev.event_kind {
                        GraphEventKind::Ifetch => {
                            iio_phase = 2;
                            iio_col = 0;
                            iio_row += 1;
                        }
                        GraphEventKind::Translate(TranslateKind { stage: 1, .. }) => {
                            iio_phase = 3;
                            iio_col = 1;
                            iio_row += 1;
                        }
                        GraphEventKind::Translate(TranslateKind { stage: 2, .. }) => {
                            if iio_phase < 3 {
                                iio_col = 2;
                                iio_row += 1;
                            } else {
                                iio_col += 1;
                            }
                            iio_phase = 4;
                        }
                        GraphEventKind::Barrier(_)
                        | GraphEventKind::CacheOp
                        | GraphEventKind::ReadMem
                        | GraphEventKind::WriteMem(_) => {
                            iio_phase = 5;
                            //iio_row += 1;
                            iio_col = 99; // put it in its own column
                        }
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
                        }
                    };
                    (iio_row, iio_col)
                } else {
                    // lay out in a square
                    // with rows
                    (iio_show_count / 5, iio_show_count % 5)
                };

                // at this point we don't have enough information about what label to put here
                // later we go over each instruction and put in a longer label
                let label = "\"?\"".to_string();

                if !show {
                    log!(
                        log::GRAPH,
                        format!("hiding node {} ({}:{}:{} {:?})", ev.name, ev.thread_id, ev.po, ev.iio, ev.instr)
                    );
                }

                current_thread_instructions.insert(
                    rc,
                    GridChild {
                        node: GridNode::Node(PositionedGraphNode {
                            ev: Some(*ev),
                            style: event_style(ev),
                            name: ev.name.clone(),
                            ev_label: (
                                ev_labels
                                    .chars()
                                    .nth(ev_label_count)
                                    .expect("Found too many instructions to label events a-z")
                                    .to_string(),
                                format!("{}", 1 + iio_show_count),
                            ),
                            grid_rc: rc,
                            label,
                        }),
                        layout: Layout { show, skinny, ..layout_event.clone() },
                    },
                );

                if show {
                    iio_show_count += 1;
                }
            }

            if !current_thread_instructions.is_empty() {
                let new_child = GridChild {
                    node: GridNode::SubCluster(GraphLayout { children: current_thread_instructions }),
                    layout: layout_instr.clone(),
                };

                thread_layout.children.insert((last_instr_row, 0), new_child);

                if iio_show_count > 0 {
                    ev_label_count += 1;
                }
            }

            thread_layouts.children.insert(
                (0, tid),
                GridChild { node: GridNode::SubCluster(thread_layout), layout: layout_thread.clone() },
            );
        }

        // go over each instruction and refit the labels
        // to add more information to the nodes
        // if there's not enough context in the other shown nodes
        for instr_cluster in thread_layouts.children.values_mut() {
            let instrs = instr_cluster.unwrap_cluster_mut();
            for instr_child in instrs.children.values_mut() {
                let instr_cluster = instr_child.unwrap_cluster_mut();
                let instr_nodes = instr_cluster.iter_nodes_mut(true, false);
                let count_show = instr_nodes.len();

                for instr in instr_nodes {
                    let mut pgn = instr.unwrap_node_mut();
                    // if it's the only event to show for the instruction,
                    // don't have event names 'a1' 'b1' etc just use 'a', 'b'
                    if count_show == 1 {
                        pgn.ev_label = (pgn.ev_label.0.clone(), "".to_string());
                    }

                    #[allow(clippy::if_same_then_else)]
                    if let Some(ev) = &pgn.ev {
                        if opts.debug {
                            pgn.label = pgn.fmt_label_debug(&self.opts, pgn.grid_rc, &self.names);
                        } else if count_show == 1 {
                            // if there is only 1 event always show a long label
                            pgn.label = pgn.fmt_label_long(&self.opts, &self.names);
                        } else if let GraphEventKind::WriteMem(_)
                        | GraphEventKind::ReadMem
                        | GraphEventKind::Barrier(_)
                        | GraphEventKind::CacheOp = ev.event_kind
                        {
                            // the principle explicit write always has a long label
                            pgn.label = pgn.fmt_label_long(&self.opts, &self.names);
                        } else if let GraphEventKind::ReadReg | GraphEventKind::WriteReg = ev.event_kind {
                            pgn.label = pgn.fmt_label_medium(&self.opts, &self.names);
                        } else {
                            pgn.label = pgn.fmt_label_short(&self.opts, &self.names);
                        }
                    }
                }
            }
        }

        let threads_node = GridNode::SubCluster(thread_layouts);
        top_level_layout.children.insert((1, 0), GridChild { node: threads_node, layout: layout_threads });

        if opts.flatten {
            // explode out into a big flat grid,
            // then use that to align rows and columns and layout things
            let mut exploded = top_level_layout.clone();
            let threads = exploded.children.get_mut(&(1, 0)).unwrap().unwrap_cluster_mut();

            // flatten each thread to keep `po` vertical etc
            for thread in threads.children.values_mut() {
                if let GridNode::SubCluster(thread_gl) = &mut thread.node {
                    thread_gl.flatten();
                }
            }

            exploded.accumulate_positions(0, 0);

            for n in exploded.iter_nodes(false, false) {
                let pge = n.unwrap_node();
                if let Some(mut tll_n) = top_level_layout.find_node_mut(&pge.name) {
                    tll_n.layout.pos = n.layout.pos;
                    tll_n.layout.bb_pos = n.layout.bb_pos;

                    let pge2 = tll_n.unwrap_node_mut();
                    pge2.style.dimensions = pge.style.dimensions;
                }
            }
        } else {
            top_level_layout.accumulate_positions(0, 0);
        };

        top_level_layout
    }

    #[allow(clippy::many_single_char_names)]
    fn draw_box<'a>(
        &self,
        f: &mut fmt::Formatter<'_>,
        ident: &str,
        label: &str,
        node: &GridChild<'a>,
        graphstyle: &str,
        style: &str,
    ) -> fmt::Result {
        if let GridNode::SubCluster(cluster) = &node.node {
            let mut tl: (i64, i64) = (i64::MAX, i64::MAX);
            let mut br: (i64, i64) = (0, 0);
            // find top-left
            for n in cluster.iter_nodes(false, true) {
                if let GridNode::Node(pgn) = &n.node {
                    let (nw, nh) = (pgn.compute_width() as i64, pgn.compute_height() as i64);

                    // use the pos of the bounding box
                    // not the centre of the node
                    if let Some((x, y)) = n.layout.bb_pos {
                        let (x, y) = (x as i64, y as i64);

                        if br.0 < x + nw {
                            br.0 = x + nw;
                        }

                        if br.1 < y + nh {
                            br.1 = y + nh;
                        }

                        if x < tl.0 {
                            tl.0 = x;
                        }

                        if y < tl.1 {
                            tl.1 = y;
                        }
                    };
                };
            }

            let (x, y) = tl;
            let (w, h) = (br.0 - tl.0, br.1 - tl.1);

            // border 0.5 inch around events
            // enough for whitespace and a label
            let wiggle = (SCALE / 2.0) as i64;

            let (llx, lly) = (x - wiggle, y + h + wiggle);
            let (urx, ury) = (x + w + wiggle, y - wiggle);

            writeln!(f, "subgraph cluster{} {{", ident)?;
            writeln!(f, "    label = \"{}\";", label)?;
            writeln!(f, "    graph [bb=\"{},{},{},{}\"{}];", llx, -lly, urx, -ury, graphstyle)?;
            writeln!(f, "    {}", style)
        } else {
            panic!("draw_box should be passed a GraphLayout")
        }
    }
}

/// given a relation as a set of pairs of nodes
/// weed out transitive edges
fn transitively_reduce(edges: HashSet<(String, String)>) -> HashSet<(String, String)> {
    // from |-> {to0, to1, to2, ...}
    let mut pairs: HashMap<&String, HashSet<&String>> = HashMap::new();

    for (from, to) in edges.iter() {
        let s = pairs.entry(from).or_insert_with(HashSet::new);
        s.insert(to);
    }

    let mut still_more = true;
    while still_more {
        still_more = false;
        let old_pairs = pairs.clone();
        for (_from, tos) in pairs.iter_mut() {
            for to in tos.clone() {
                if let Some(s) = old_pairs.get(&to) {
                    for trans_to in s.clone() {
                        if tos.contains(&trans_to) {
                            tos.remove(trans_to);
                            still_more = true;
                        }
                    }
                }
            }
        }
    }

    let mut v = HashSet::new();
    for (from, tos) in pairs.into_iter() {
        for to in tos {
            v.insert((from.clone(), to.clone()));
        }
    }

    v
}

/// given a relation as a set of pairs of nodes
/// insert all transitive edges
fn transitively_close(edges: HashSet<(String, String)>) -> HashSet<(String, String)> {
    // from |-> {to0, to1, to2, ...}
    let mut pairs: HashMap<&String, HashSet<&String>> = HashMap::new();

    for (from, to) in edges.iter() {
        let s = pairs.entry(from).or_insert_with(HashSet::new);
        s.insert(to);
    }

    let mut still_more = true;
    while still_more {
        still_more = false;
        let old_pairs = pairs.clone();
        for (_from, tos) in pairs.iter_mut() {
            for to in tos.clone() {
                if let Some(s) = old_pairs.get(to) {
                    for trans_to in s.clone() {
                        if !tos.contains(trans_to) {
                            tos.insert(trans_to);
                            still_more = true;
                        }
                    }
                }
            }
        }
    }

    let mut v = HashSet::new();
    for (from, tos) in pairs.into_iter() {
        for to in tos {
            v.insert((from.clone(), to.clone()));
        }
    }

    v
}

fn simplify_edges(relty: RelType, edges: HashSet<(String, String)>) -> HashSet<(String, String)> {
    match relty {
        RelType::TransReduction => transitively_reduce(edges),
        RelType::TransClosure => transitively_close(edges),
        RelType::Normal => edges,
    }
}

impl fmt::Display for Graph {
    // To build a digraph for each Graph we produce some
    // neato-compatible (with -n 1) graphviz with a fixed grid-like layout.
    //
    // We layout something as follows:
    //
    //         col0    col1    col2    col3    col4    col5    col6    col7
    //
    //                            [Thread #0]
    //        +------------------------------------------------+
    //        |                STR X0,[X1]                     |
    // row0   |          [T]     [T]     [T]     [T]           |
    // row1   |  [T]     [T]     [T]     [T]     [T]           |
    // row2   |  [T]     [T]     [T]     [T]     [T]           |
    // row3   |  [T]     [T]     [T]     [T]     [T]           |
    // row4   |  [T]     [T]     [T]     [T]     [T]     [W]   |
    //        |                                                |
    //        +------------------------------------------------+
    //
    //
    // Nodes are written like [label]
    //
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "digraph Exec {{")?;
        writeln!(f, "    splines=true;")?;
        writeln!(f, "    node [fontsize=44, fontname=aerial];")?;
        writeln!(f, "    edge [fontsize=44, fontname=aerial, arrowsize=2];")?;
        writeln!(f, "    graph [fontsize=40, fontname=aerial];")?;
        log!(log::VERBOSE, "producing dot");

        // keep track of all the PAs that were touched (written to)
        // in the execution, so we can decide whether to show an event later
        // or whether to use an event in layouting.
        let mut mutated_pas = HashSet::new();

        let mut thread_ids = HashSet::new();
        for ev in self.events.values() {
            thread_ids.insert(ev.thread_id);

            // collect PAs from various write events.
            if let GraphEventKind::WriteMem(_) = &ev.event_kind {
                if let Some(v) = &ev.value {
                    if let Some(addr) = &v.address {
                        mutated_pas.insert(addr);
                    }
                }
            }
        }

        // collect all event names which access a location written to in the test
        let mutated_pas_event_names: HashSet<&String> = self
            .events
            .values()
            .flat_map(|ev| match &ev.value {
                Some(GraphValue { address: Some(addr), .. }) if mutated_pas.contains(addr) => Some(&ev.name),
                _ => None,
            })
            .collect();

        log!(log::GRAPH, "producing GraphLayout ...");
        let node_layout = self.produce_node_layout(&self.litmus_opts, &self.opts, mutated_pas);
        let graph_event_nodes = node_layout.iter_nodes(true, false);
        log!(log::GRAPH, "produced node layout");

        if let Some(iw) = node_layout.children.get(&(0, 0)) {
            writeln!(f, "{};", iw.fmt_as_node())?;
        }

        if let Some(GridChild { node: GridNode::SubCluster(thread_clusters), .. }) = node_layout.children.get(&(1, 0)) {
            let mut displayed_event_names: HashSet<String> = HashSet::new();
            displayed_event_names.insert("IW".to_string());

            let displayed_graph_events: Vec<&GraphEvent> = graph_event_nodes
                .iter()
                .flat_map(|c| match c.node {
                    GridNode::Node(PositionedGraphNode { ev: Some(ev), .. }) => Some(ev),
                    _ => None,
                })
                .collect();

            for tid in thread_ids {
                log!(log::GRAPH, &format!("drawing Thread#{}", tid));
                let mut events: Vec<&GraphEvent> = self.events.values().filter(|ev| ev.thread_id == tid).collect();
                events.sort_by(|ev1, ev2| (ev1.thread_id, ev1.po, ev1.iio).cmp(&(ev2.thread_id, ev2.po, ev2.iio)));

                let displayed_thread_events: Vec<&GraphEvent> =
                    displayed_graph_events.clone().into_iter().filter(|ge| ge.thread_id == tid).collect();

                // draw the events and boxes
                if let Some(thread_child) = thread_clusters.children.get(&(0, tid)) {
                    if !displayed_thread_events.is_empty() {
                        let thread_box_label = format!("Thread {}", tid);
                        self.draw_box(
                            f,
                            &format!("{}", tid),
                            &thread_box_label,
                            thread_child,
                            "labeljust=l",
                            "style=dashed;",
                        )?;
                    }

                    if let GridChild { node: GridNode::SubCluster(thread), .. } = thread_child {
                        for ((po_row, _), instr) in thread.children.iter() {
                            if let GridNode::SubCluster(instr_cluster) = &instr.node {
                                if let Some(po) = instr_cluster.po() {
                                    let displayed_instr_events: Vec<&GraphEvent> =
                                        displayed_thread_events.clone().into_iter().filter(|ge| ge.po == po).collect();

                                    if displayed_instr_events.len() > 1 {
                                        self.draw_box(
                                            f,
                                            &format!("{}_{}", tid, po_row),
                                            "",
                                            instr,
                                            "labeljust=l",
                                            "style=dashed;",
                                        )?;
                                    }

                                    for ev in instr_cluster.children.values() {
                                        if ev.layout.show {
                                            if let GridNode::Node(PositionedGraphNode { ev: Some(ev), .. }) = ev.node {
                                                displayed_event_names.insert(ev.name.clone());
                                            }
                                            writeln!(f, "    {};", ev.fmt_as_node())?;
                                        }
                                    }

                                    if displayed_instr_events.len() > 1 {
                                        writeln!(f, "}}")?;
                                    }
                                }
                            }
                        }
                    }

                    if !displayed_thread_events.is_empty() {
                        writeln!(f, "}}")?;
                    }
                }
            }

            log!(log::GRAPH, "finished nodes, now writing relations...");

            if self.opts.control_delimit {
                write!(f, "\x1D")?
            };
            for rel in &self.relations {
                let mut symmetric_edges: HashSet<(String, String)> = HashSet::new();

                if !rel.edges.is_empty() {
                    if self.opts.control_delimit {
                        writeln!(f, "\x1E{}\x1F", rel.name)?
                    };

                    // some of the edges are to hidden nodes
                    // so we simply hide the edges
                    let edges: HashSet<(String, String)> = (&rel.edges)
                        .iter()
                        .filter(|(from, to)| displayed_event_names.contains(from) && displayed_event_names.contains(to))
                        .map(|(from, to)| (from.clone(), to.clone()))
                        .collect();

                    let edges = simplify_edges(rel.ty, edges);

                    log!(log::GRAPH, &format!("drawing relation {} (#{})", rel.name, edges.len()));
                    for (from, to) in edges {
                        // do not show IW -(rf)-> R
                        // when R's addr is not written by the test
                        if let Some(to_event) = &self.events.get(&to) {
                            if !self.opts.debug
                                && rel.name.ends_with("rf")
                                && from == "IW"
                                && !mutated_pas_event_names.contains(&to)
                                && !event_in_shows(&self.opts.force_show_events, to_event)
                            {
                                continue;
                            }
                        }

                        let dir = if rel.edges.contains(&(to.clone(), from.clone())) {
                            if symmetric_edges.contains(&(to.clone(), from.clone())) {
                                continue;
                            } else {
                                symmetric_edges.insert((from.clone(), to.clone()));
                            }
                            "dir=none,"
                        } else {
                            ""
                        };

                        let labelattr =
                            // for vertical, but relatively short, "po" edges
                            // we try fit them "high" up near the tail to make the most use of space
                            if &rel.name == "po" || &rel.name == "po-loc" {
                                "taillabel"
                            } else {
                                "label"
                            };
                        let label = if rel.name != "po" || self.opts.debug {
                            format!("{}=\" {} \",", labelattr, rel.name)
                        } else {
                            "".to_string()
                        };
                        let color = relation_color(&rel.name);
                        writeln!(f, " {} -> {} [{}color={}, {}fontcolor={}];", from, to, dir, color, label, color)?;
                    }
                }
            }
            if self.opts.control_delimit {
                write!(f, "\x1D")?
            }
        }

        log!(log::VERBOSE, "generated graph");
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
fn regname_val<'ir, B: BV>(ev: &Event<B>, symtab: &'ir Symtab) -> Option<Val<B>> {
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
fn concrete_graph_from_candidate<'ir, B: BV>(
    exec: &ExecutionInfo<B>,
    names: GraphValueNames<B>,
    _footprints: &HashMap<B, Footprint>,
    litmus: &Litmus<B>,
    _ifetch: bool,
    opts: &GraphOpts,
    symtab: &'ir Symtab,
) -> Result<Graph, GraphError> {
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
    Frel: Fn(&mut Option<Model<'_, 'ev, B>>, &str, &Vec<&'ev str>) -> GraphRelation,
{
    let mut builtin_relations =
        vec!["po", "rf", "co", "trf", "trf1", "trf2", "same-va-page", "same-ipa-page", "tlbi-same-va-page"];
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
    let cmdline_shows: Vec<String> = opts.shows.clone().unwrap_or_else(Vec::new);
    let litmus_shows: Vec<String> = litmus.graph_opts.shows.clone().unwrap_or_else(Vec::new);
    let cat_shows: Vec<String> = Vec::new();
    let all_rels: HashSet<&str> = if !cmdline_shows.is_empty() {
        cmdline_shows.iter().map(String::as_str).collect()
    } else if !litmus_shows.is_empty() {
        litmus_shows.iter().map(String::as_str).collect()
    } else {
        cat_shows.iter().map(String::as_str).collect()
    };

    log!(log::GRAPH, format!("collected {} shows: {:?}", all_rels.len(), all_rels));

    for rel in all_rels {
        g.relations.push(interpret_rel(&mut model, rel, &event_names));
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
pub fn graph_from_unsat<'ir, 'ev, B: BV>(
    exec: &'ev ExecutionInfo<B>,
    names: GraphValueNames<B>,
    footprints: &HashMap<B, Footprint>,
    litmus: &Litmus<B>,
    ifetch: bool,
    opts: &GraphOpts,
    symtab: &'ir Symtab,
) -> Result<Graph, GraphError> {
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

    match concrete_graph_from_candidate(exec, names, footprints, litmus, ifetch, opts, symtab) {
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
                    gv.address.or_else(|| Some(address.to_string(symtab))),
                    gv.virtual_address,
                    bytes,
                    gv.value.or_else(|| Some(value.to_string(symtab))),
                )
            },
            |_m, rel_name, _events| {
                let (rel_name, relty) = parse_relname_opt(rel_name);
                // when the smt was unsatisfiable we only have the relations from the footprint
                // we can still enumerate those and draw them
                if let Some(rel) = footprint_relations.get(rel_name) {
                    GraphRelation {
                        name: (*rel_name).to_string(),
                        ty: relty,
                        edges: Pairs::from_slice(combined_events.as_slice())
                            .filter(|(ev1, ev2)| rel(ev1, ev2, &exec.thread_opcodes, footprints))
                            .map(|(ev1, ev2)| (ev1.name.clone(), ev2.name.clone()))
                            .collect(),
                    }
                } else {
                    GraphRelation { name: (*rel_name).to_string(), ty: relty, edges: HashSet::new() }
                }
            },
        )),
    }
}

/// Generate a graph from the output of a Z3 invocation that returned sat.
#[allow(clippy::too_many_arguments)]
pub fn graph_from_z3_output<'ir, B: BV>(
    exec: &ExecutionInfo<B>,
    names: GraphValueNames<B>,
    footprints: &HashMap<B, Footprint>,
    z3_output: &str,
    litmus: &Litmus<B>,
    ifetch: bool,
    opts: &GraphOpts,
    symtab: &'ir Symtab,
) -> Result<Graph, GraphError> {
    use GraphError::*;

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
    let model = Model::<B>::parse(&event_names, model_buf).ok_or(SmtParseError)?;

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
            |m, rel_name, events| {
                let (rel_name, relty) = parse_relname_opt(rel_name);
                if let Some(m) = m {
                    match m.interpret_rel(rel_name, events) {
                        Ok(edges) => GraphRelation {
                            name: (*rel_name).to_string(),
                            ty: relty,
                            edges: edges.iter().map(|(from, to)| ((*from).to_string(), (*to).to_string())).collect(),
                        },
                        Err(err) => {
                            eprintln!("Failed to interpret relation '{}': {}", rel_name, err);
                            GraphRelation { name: (*rel_name).to_string(), ty: relty, edges: HashSet::new() }
                        }
                    }
                } else {
                    unreachable!()
                }
            },
        )),
    }
}
