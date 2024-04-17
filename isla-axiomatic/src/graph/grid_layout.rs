use crate::graph::GraphOpts;
use std::collections::{HashMap, HashSet};

use super::graph_events::*;

/// Graphs of executions are laid out in a grid-like structure
/// at the top-level the grid has a top-most row to contain initial writes in
/// and the second row is split into N columns for the N threads
/// then, each thread is split into M rows, one for each instruction instance
///
/// If rendering in a row-based format, then deriving a FlatGridLayout (see below)
/// may be more appropriate
#[derive(Debug, Clone)]
pub struct GridLayout<'ev, A> {
    pub top: Vec<GridNode<'ev, A>>,
    pub threads: Vec<GridThread<'ev, A>>,
}

#[derive(Debug, Clone)]
pub struct GridThread<'ev, A> {
    pub instr_instances: Vec<GridInstrInstance<'ev, A>>,
}

/// each instruction instance is either:
///     - if there's only one event, filled with the id+label of the event
///     - if there's multiple events, but not multi-stage translation, fill with K columns for the K intra-instruction ordered events.
///     - if there is multistage translation or many sysregister interleaved, produce a more fancy inner-grid layout
#[derive(Debug, Clone)]
pub enum GridInstrInstance<'ev, A> {
    SingleEventInstr(GridNode<'ev, A>),
    SingleRowEventsInstr(Vec<GridNode<'ev, A>>),
    MultiRowEventsInstr(Vec<Vec<GridNode<'ev, A>>>),
}

impl<'ev, A> GridInstrInstance<'ev, A> {
    pub fn map_annot<F, B>(self, f: F) -> GridInstrInstance<'ev, B>
    where
        F: Fn(GridNode<'ev, A>) -> GridNode<'ev, B>,
    {
        use GridInstrInstance::*;
        match self {
            SingleEventInstr(n) => SingleEventInstr(f(n)),
            SingleRowEventsInstr(mut r) => SingleRowEventsInstr(r.drain(..).map(&f).collect()),
            MultiRowEventsInstr(mut m) => {
                MultiRowEventsInstr(m.drain(..).map(|mut r| r.drain(..).map(&f).collect()).collect())
            }
        }
    }

    pub fn fill_label(&mut self, opts: &GraphOpts, names: &GraphValueNames<u64>) {
        use GridInstrInstance::*;
        match self {
            SingleEventInstr(ref mut e) => {
                e.fill_label(true, false, opts, names);
            }
            SingleRowEventsInstr(ref mut r) => {
                for e in r {
                    e.fill_label(false, true, opts, names);
                }
            }
            MultiRowEventsInstr(ref mut m) => {
                for r in m {
                    for e in r {
                        e.fill_label(false, true, opts, names);
                    }
                }
            }
        }
    }

    pub fn events(&self) -> Vec<&GridNode<'_, A>> {
        use GridInstrInstance::*;
        match self {
            SingleEventInstr(e) => vec![e],
            SingleRowEventsInstr(r) => r.iter().collect(),
            MultiRowEventsInstr(m) => m.iter().flat_map(|r| r.iter()).collect(),
        }
    }
}

#[derive(Clone)]
pub struct GridNode<'ev, A> {
    pub ev: Option<&'ev GraphEvent>,
    /// the label to put in the box on the graph
    pub label: String,
    /// the (event label, sublabel) pair
    pub ev_label: (String, String),
    /// alignment of the text within the node
    pub alignment: Align,
    pub annot: A,
}

impl<'ev, A: std::fmt::Debug> std::fmt::Debug for GridNode<'ev, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let evlab = format_ev_label(&self.ev_label);
        f.debug_tuple("GridNode").field(&self.annot).field(&evlab).field(&self.label).finish()
    }
}

impl<'ev, A> GridNode<'ev, A> {
    fn fill_label(&mut self, long: bool, multi: bool, opts: &GraphOpts, names: &GraphValueNames<u64>) {
        if let Some(ev) = self.ev {
            if long {
                self.label = ev.fmt_label_long(opts, &self.ev_label, names);
            } else {
                self.label = ev.fmt_label_short(opts, &self.ev_label, names);
            }
        }

        // if only one event in this instance, drop the suffix on the label
        if !multi {
            self.ev_label = (self.ev_label.0.clone(), "".to_string());
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub enum Align {
    Left,
    Middle,
    Right,
}

impl<'ev, A> GridNode<'ev, A> {
    pub fn with_annot<B>(self, annot: B) -> GridNode<'ev, B> {
        GridNode { ev: self.ev, label: self.label, ev_label: self.ev_label, alignment: self.alignment, annot }
    }

    pub fn map_annot<F, B>(self, f: F) -> GridNode<'ev, B>
    where
        F: FnOnce(A) -> B,
    {
        GridNode {
            ev: self.ev,
            label: self.label,
            ev_label: self.ev_label,
            alignment: self.alignment,
            annot: f(self.annot),
        }
    }
}

pub fn event_in_shows(shows: &Option<Vec<String>>, ev: &GraphEvent) -> bool {
    if let Some(evs) = shows {
        for show_ev in evs.iter() {
            if show_ev.starts_with('T') {
                /* name like T0:1:s1l3 for translate thread 0, instr 1, s1l3 translate */
                let stripped = show_ev.strip_prefix('T').unwrap();
                let sections: Vec<&str> = stripped.split(':').collect();
                let tid: usize =
                    sections.first().expect("expected T0:1:s1l3 format").parse().expect("expected tid to be integer");
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

/// given a relation as a set of pairs of nodes
/// weed out transitive edges
fn transitively_reduce(edges: &HashSet<(String, String)>) -> HashSet<(String, String)> {
    // from |-> {to0, to1, to2, ...}
    let mut pairs: HashMap<&String, HashSet<&String>> = HashMap::new();

    for (from, to) in edges.iter() {
        let s = pairs.entry(from).or_default();
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
fn transitively_close(edges: &HashSet<(String, String)>) -> HashSet<(String, String)> {
    // from |-> {to0, to1, to2, ...}
    let mut pairs: HashMap<&String, HashSet<&String>> = HashMap::new();

    for (from, to) in edges.iter() {
        let s = pairs.entry(from).or_default();
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

pub fn simplify_edges(relty: &RelType, edges: &HashSet<(String, String)>) -> HashSet<(String, String)> {
    let modified = match relty.trans {
        RelTransType::TransReduction => transitively_reduce(edges),
        RelTransType::TransClosure => transitively_close(edges),
        RelTransType::Normal => edges.clone(),
    };

    modified
}

fn make_grid_node<'ev>(labels: &mut EventLabeller, ge: &'ev GraphEvent, align: Align) -> GridNode<'ev, ()> {
    let ev_label = labels.next().unwrap();
    GridNode {
        ev: Some(ge),
        // later on we will fill the labels in depending on graph options
        label: "\"?\"".to_string(),
        ev_label,
        // and maybe adjust alignment
        alignment: align,
        annot: (),
    }
}

fn make_multirow<'ev>(labels: &mut EventLabeller, instr_events: &Vec<&'ev GraphEvent>) -> GridInstrInstance<'ev, ()> {
    // here, `instr_events` contains lots of translation/sysreg events
    // TODO: instead of just splitting into rows of 5, try do a logical split
    let mut inner: Vec<Vec<GridNode<'ev, ()>>> = vec![];
    let mut cur_inner_row: Vec<GridNode<'ev, ()>> = vec![];
    for (i, e) in instr_events.iter().enumerate() {
        cur_inner_row.push(make_grid_node(labels, e, Align::Left));

        if i % 5 == 4 {
            inner.push(cur_inner_row.clone());
            cur_inner_row.clear();
        }
    }
    inner.push(cur_inner_row);

    GridInstrInstance::MultiRowEventsInstr(inner)
}

struct EventLabeller {
    char_idx: u32, // the index in the a-z aa-zz aaa-zzz etc sequence
    iid: u32,      // index within the instruction
    cur_prefix: Option<String>,
}

const CHARS: &str = "abcdefghijklmnopqrstuvwxyz";
const NCHARS: usize = CHARS.len();

impl EventLabeller {
    /// Advance the labeller to the next instruction instance
    /// producing a new prefix, and resetting the intra-instruction counter to 0
    fn next_instr(&mut self) {
        self.char_idx += 1;
        self.iid = 0;
        self.cur_prefix = Some(self.prefix())
    }

    /// Computes a prefix from an index
    /// where 0 = a, 25=z, 26=aa, etc
    /// e.g. like a base-26 version of: 0, 1, 00, 01, 10, 11, 000,
    fn prefix(&self) -> String {
        let n: u32 = prefix_len(self.char_idx);
        let m: u32 = self.char_idx - prefix_offset(n);
        let b = NCHARS as u32;
        let mut prefix: Vec<&str> = vec![];

        // now we write out m as a n-length base-NCHARS number
        for i in 0..n {
            let j = ((m / u32::pow(b, i)) % b) as usize;
            prefix.push(&CHARS[j..=j]);
        }

        prefix.reverse();
        prefix.as_slice().join("")
    }
}

impl Default for EventLabeller {
    fn default() -> Self {
        let mut lab = EventLabeller { iid: 0, char_idx: 0, cur_prefix: None };
        lab.cur_prefix = Some(lab.prefix());
        lab
    }
}

/// Given an index into a prefix sequence, compute the len of the output prefix
fn prefix_len(char_idx: u32) -> u32 {
    let mut group = 1;
    let mut tot = 26;
    let mut len = 1;

    while tot < char_idx + 1 {
        group += 1;
        tot += u32::pow(26, group);
        len += 1;
    }

    len
}

/// Given a prefix length, figure out the offset of this length in the full sequence
fn prefix_offset(n: u32) -> u32 {
    // recall that b^n = (b-1)b^0 + (b-1)b^1 + (b-1)b^2 + ... + (b-1)b^(n-1) + 1
    //        ==>  b^n = (b-1)(b^0 + b^1 + .. + b^(n-1)) + 1
    // we don't have a zero-length sequence, so we remove the b^0 term
    // then the offset = (b^1 + b^2 + ... b^(n-1))
    //      ==> offset = (b^n - (b-1)b^0 -1)/(b-1)
    let b = NCHARS as u32;
    (u32::pow(b, n) - (b - 1) - 1) / (b - 1)
}

impl Iterator for EventLabeller {
    type Item = (String, String);
    fn next(&mut self) -> Option<Self::Item> {
        self.cur_prefix.as_ref().map(|p| {
            let i = self.iid;
            self.iid += 1;
            (p.clone(), format!("{}", i))
        })
    }
}

impl<'ev> GridLayout<'ev, ()> {
    pub fn from_graph<'g>(g: &'ev Graph, opts: &GraphOpts) -> Self {
        let mut thread_ids: Vec<usize> =
            g.events.values().map(|ev| ev.thread_id).collect::<HashSet<usize>>().into_iter().collect();
        thread_ids.sort_unstable();

        // TODO: event labelling which is stable under adding/removing events from the graph
        let mut evlabeller = EventLabeller::default();

        let mut threads: Vec<GridThread<'_, ()>> = vec![];
        for tid in thread_ids {
            let mut events: Vec<&GraphEvent> = g.events.values().filter(|ev| ev.thread_id == tid).collect();
            events.sort_by(|ev1, ev2| (ev1.thread_id, ev1.po, ev1.iio).cmp(&(ev2.thread_id, ev2.po, ev2.iio)));

            let mut instr_instances: Vec<GridInstrInstance<'_, ()>> = vec![];
            let mut last_po: Option<usize> = None;
            let mut cur_instr_events: Vec<&GraphEvent> = vec![];

            let push_new_instance =
                |labels: &mut EventLabeller,
                 cur_instr_events: &mut Vec<&'ev GraphEvent>,
                 instr_instances: &mut Vec<GridInstrInstance<'ev, ()>>| {
                    if cur_instr_events.len() == 1 {
                        instr_instances.push(GridInstrInstance::SingleEventInstr(make_grid_node(
                            labels,
                            cur_instr_events[0],
                            Align::Left,
                        )));
                    } else if cur_instr_events.len() < 6 {
                        instr_instances.push(GridInstrInstance::SingleRowEventsInstr(
                            cur_instr_events.iter_mut().map(|e| make_grid_node(labels, e, Align::Left)).collect(),
                        ));
                    } else {
                        instr_instances.push(make_multirow(labels, cur_instr_events));
                    }
                    cur_instr_events.clear();
                    labels.next_instr();
                };

            for ev in events {
                if last_po.is_none() {
                    last_po = Some(ev.po);
                }

                if Some(ev.po) != last_po {
                    push_new_instance(&mut evlabeller, &mut cur_instr_events, &mut instr_instances);
                    last_po = Some(ev.po);
                }

                cur_instr_events.push(ev);
            }
            push_new_instance(&mut evlabeller, &mut cur_instr_events, &mut instr_instances);

            threads.push(GridThread { instr_instances })
        }

        let mut gl = GridLayout { top: vec![], threads };
        gl.fill_labels(opts, &g.names);
        gl
    }

    fn fill_labels(&mut self, opts: &GraphOpts, names: &GraphValueNames<u64>) {
        for t in &mut self.threads {
            for i in &mut t.instr_instances {
                i.fill_label(opts, names)
            }
        }
    }
}

impl<'g, 'ev, A> GridLayout<'ev, A>
where
    'g: 'ev,
{
    /// Given an unannotated layout
    /// compute the (character) widths of every node's labels
    /// and attach them as an annotation
    pub fn annotate_widths<B, F>(mut self, f: F) -> GridLayout<'ev, B>
    where
        F: Fn(&GridNode<'ev, A>) -> B,
    {
        GridLayout {
            top: self
                .top
                .drain(..)
                .map(|n| {
                    let a = f(&n);
                    n.with_annot(a)
                })
                .collect(),
            threads: self
                .threads
                .drain(..)
                .map(|mut t| GridThread {
                    instr_instances: t
                        .instr_instances
                        .drain(..)
                        .map(|i| {
                            i.map_annot(|n| {
                                let a = f(&n);
                                n.with_annot(a)
                            })
                        })
                        .collect(),
                })
                .collect(),
        }
    }

    pub fn events(&'g self) -> Vec<&'g GridNode<'ev, A>> {
        let mut evs: Vec<&'g GridNode<'_, A>> = vec![];
        for t in &self.threads {
            for i in &t.instr_instances {
                evs.append(&mut i.events());
            }
        }
        evs
    }
}

/// Once we have a grid layout, we can unroll it into multicols
/// for easier row-based rendering (e.g. for ASCII output).
#[derive(Debug)]
pub struct FlatGridLayout<'g, 'ev, A> {
    // the grid of multicols
    // as a vec of rows
    // where each row is a vec of multi-column values
    // such that the total columns is the sum of a row's multicolumn spans
    pub grid: Vec<Vec<MultiCol<'g, 'ev, A>>>,
}

// RowIter is used to produce a FlatGridLayout
// by iterating over each rows, turning columns into appropriately sized MultiCols
#[derive(Debug)]
struct RowIter<'g, 'ev, A> {
    gl: &'g GridLayout<'ev, A>,

    // the index of the current instr instance,
    // and the sub-row within that instr instance.
    cur_idx: (usize, usize),

    // number of columns per thread
    col_counts: Vec<usize>,

    // keep track of how many total instrs there are so we know when to stop
    max_instr_idx: usize,
}

#[derive(Copy, Clone)]
pub struct Span {
    pub from: usize,
    pub width: usize,
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.pad(&format!("({}..+{})", self.from, self.width))
    }
}

impl Span {
    /// Merges two Spans into a bigger span
    /// this is an extrapolation merge as the spans need not overlap
    /// i.e. it's the least-upper-bound on which contains both self and other
    fn merge_extrapolate(self, other: Self) -> Self {
        let r1 = self.range();
        let r2 = other.range();
        let r3 = (r1.start.min(r2.start))..(r1.end.max(r2.end));
        Span::from_range(r3)
    }

    fn from_range(r: std::ops::Range<usize>) -> Self {
        Span { from: r.start, width: r.end - r.start }
    }

    fn range(&self) -> std::ops::Range<usize> {
        self.from..self.from + self.width
    }
}

pub struct MultiCol<'g, 'ev, A> {
    pub node: Option<&'g GridNode<'ev, A>>,
    pub span: Span,
}

impl<'g, 'ev, A: std::fmt::Debug> std::fmt::Debug for MultiCol<'g, 'ev, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("MultiCol").field(&self.span).field(&self.node).finish()
    }
}

impl<'g, 'ev> MultiCol<'g, 'ev, usize> {
    /// Given a MultiCol in an annotated flat grid, with some known grid dimensions
    /// work out the character width of this column
    pub fn char_width(&self, dim: &GridDimensions) -> usize {
        let r = self.span.range();
        let widths = r.map(|c| dim.column_widths[c]);

        widths.sum()
    }
}

impl<'g, 'ev, A> RowIter<'g, 'ev, A> {
    pub fn from_layout(gl: &'g GridLayout<'ev, A>) -> Self {
        use GridInstrInstance::*;
        let mut col_counts: Vec<usize> = vec![];
        for t in &gl.threads {
            col_counts.push(
                t.instr_instances
                    .iter()
                    .map(|i| match i {
                        SingleEventInstr(_) => 1,
                        SingleRowEventsInstr(r) => r.len(),
                        MultiRowEventsInstr(g) => g.iter().map(Vec::len).max().unwrap(),
                    })
                    .max()
                    .unwrap(),
            );
        }

        let max_instr_idx = gl.threads.iter().map(|i| i.instr_instances.len()).max().unwrap();

        RowIter { gl, cur_idx: (0, 0), col_counts, max_instr_idx }
    }
}

impl<'g, 'ev, A> RowIter<'g, 'ev, A> {
    // increment the cur_idx counter to the next row
    // if any instr instance in this row has another sub-row, increment to that
    // otherwise, move to the next instr.
    fn inc(&mut self) {
        use GridInstrInstance::*;
        self.cur_idx = (self.cur_idx.0, self.cur_idx.1 + 1);

        let mut found = false;
        for t in &self.gl.threads {
            if let Some(i) = t.instr_instances.get(self.cur_idx.0) {
                match i {
                    SingleEventInstr(_) => (),
                    SingleRowEventsInstr(_) => (),
                    MultiRowEventsInstr(m) => {
                        if m.get(self.cur_idx.1).is_some() {
                            found = true;
                        }
                    }
                }
            }
        }

        if !found {
            self.cur_idx = (self.cur_idx.0 + 1, 0);
        }
    }
}

impl<'g, 'ev, A> Iterator for RowIter<'g, 'ev, A> {
    type Item = Vec<MultiCol<'g, 'ev, A>>;

    fn next(&mut self) -> Option<Self::Item> {
        use GridInstrInstance::*;
        let mut cur_row: Vec<MultiCol<'g, 'ev, A>> = vec![];
        let mut cur_col: usize = 0;

        let push = &mut |n, w| {
            cur_row.push(MultiCol { node: n, span: Span { from: cur_col, width: w } });
            cur_col += w;
        };

        for (tid, t) in self.gl.threads.iter().enumerate() {
            let w = self.col_counts[tid];
            if let Some(tr) = t.instr_instances.get(self.cur_idx.0) {
                match tr {
                    SingleEventInstr(ev) => {
                        if self.cur_idx.1 > 0 {
                            push(None, w);
                        } else {
                            push(Some(ev), w);
                        }
                    }
                    SingleRowEventsInstr(r) => {
                        if self.cur_idx.1 > 0 {
                            push(None, w);
                        } else {
                            let size = r.len();
                            for c in r {
                                push(Some(c), w / size);
                            }
                        }
                    }
                    MultiRowEventsInstr(m) => {
                        if let Some(r) = m.get(self.cur_idx.1) {
                            let size = r.len();
                            for c in r {
                                push(Some(c), w / size);
                            }
                        } else {
                            push(None, w);
                        }
                    }
                }
            } else {
                push(None, w);
            }
        }

        self.inc();

        if self.cur_idx.0 > self.max_instr_idx {
            None
        } else {
            Some(cur_row)
        }
    }
}

impl<'g, 'ev, A> FlatGridLayout<'g, 'ev, A> {
    pub fn from_layout(gl: &'g GridLayout<'ev, A>) -> Self {
        let mut grid: Vec<Vec<MultiCol<'g, 'ev, A>>> = vec![];
        for r in RowIter::from_layout(gl) {
            grid.push(r);
        }
        FlatGridLayout { grid }
    }

    /// counts how many columns there are actually are
    pub fn columns(&self) -> usize {
        self.grid[0].iter().map(|mc| mc.span.width).sum()
    }
}

#[derive(Debug)]
pub struct GridDimensions {
    pub thread_spans: HashMap<usize, Span>,
    pub column_widths: Vec<usize>,
    pub total_columns: usize,
    pub total_rows: usize,
}

impl<'g, 'ev> FlatGridLayout<'g, 'ev, usize> {
    pub fn dimensions(&self) -> GridDimensions {
        let total_columns = self.columns();
        let total_rows = self.grid.len();

        let mut column_widths: Vec<usize> = vec![0; total_columns];
        let mut thread_spans: HashMap<usize, Span> = HashMap::new();

        for r in &self.grid {
            for c in r {
                let mcw: usize = c.node.map_or(0, |n| n.annot);

                // if we have a MultiCol spanning N columns
                //  starting from column M
                // with width W
                // then columns [M..M+N] each have width at least W/N
                let w = mcw / c.span.width;

                for m in c.span.range() {
                    let cw = column_widths.get_mut(m).unwrap();
                    *cw = (*cw).max(w);
                }

                // Update thread_widths for this thread_id to have this width
                c.node.and_then(|gn| {
                    gn.ev.map(|ge| {
                        thread_spans
                            .entry(ge.thread_id)
                            .and_modify(|v: &mut Span| {
                                *v = (*v).merge_extrapolate(c.span);
                            })
                            .or_insert(c.span)
                    })
                });
            }
        }

        GridDimensions { thread_spans, column_widths, total_columns, total_rows }
    }
}

impl GridDimensions {
    pub fn thread_of(&self, col: usize) -> usize {
        for (tid, span) in self.thread_spans.iter() {
            if span.from <= col && col < span.from + span.width {
                return *tid;
            }
        }

        unreachable!("multicol past end of threads")
    }

    pub fn thread_width(&self, tid: usize) -> Option<usize> {
        let span = self.thread_spans.get(&tid)?;
        let r = span.range();
        Some(r.map(|c| self.column_widths[c]).sum())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ev_labeller() {
        let mut evlab = EventLabeller::default();

        // sanity checks
        assert!(prefix_len(25) == 1);
        assert!(prefix_len(26) == 2);
        assert!(prefix_len(600) == 2);
        assert!(prefix_len(26 + 26 * 26 - 1) == 2);
        assert!(prefix_len(26 + 26 * 26) == 3);
        assert!(prefix_offset(1) == 0);
        assert!(prefix_offset(2) == 26);
        assert!(prefix_offset(3) == 26 + 26 * 26 /* == 702 */);

        evlab.char_idx = 0;
        assert!(evlab.prefix() == "a");
        evlab.char_idx = 1;
        assert!(evlab.prefix() == "b");
        evlab.char_idx = 26;
        assert!(evlab.prefix() == "aa");
        evlab.char_idx = 701;
        assert!(evlab.prefix() == "zz");
        evlab.char_idx = 702;
        assert!(evlab.prefix() == "aaa");
    }
}
