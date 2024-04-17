use std::collections::{HashMap, HashSet};
use std::io;

use isla_lib::log;

use super::graph_events::*;
use super::graph_opts::*;
use super::grid_layout::*;

use crate::litmus::LitmusGraphOpts;

/// padding around a child
/// in inches
#[derive(Debug, Clone)]
struct Padding {
    up: f64,
    down: f64,
    left: f64,
    right: f64,
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
enum GVGridNode<'a> {
    Node(PositionedGraphNode<'a>),
    SubCluster(GraphLayout<'a>),
}

#[derive(Debug, Clone)]
struct GVGridChild<'a> {
    /// the node
    node: GVGridNode<'a>,
    /// layout information about the child
    layout: Layout,
}

/// a GraphLayout is a hierarchical row/column layout
#[derive(Debug, Clone)]
struct GraphLayout<'a> {
    children: HashMap<(usize, usize), GVGridChild<'a>>,
}

#[derive(Debug, Clone)]
pub struct Style {
    pub bg_color: String,
    pub node_shape: String,
    pub node_style: String,
    /// the width/height of the node
    pub dimensions: (f64, f64),
}

fn event_style<T>(gn: &GridNode<'_, T>) -> Style {
    // TODO: BS: do we want to colour-code event types?
    // e.g. Ts2 => wheat1, Ts1 => darkslategray1
    if let Some(ev) = gn.ev {
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
    } else {
        Style {
            bg_color: "white".to_string(),
            node_shape: "box".to_string(),
            node_style: "filled".to_string(),
            dimensions: (0.0, 0.0),
        }
    }
}

#[derive(Debug, Clone)]
struct PositionedGraphNode<'ev> {
    ev: GridNode<'ev, usize>,
    /// style information about the node
    /// to be passed to graphviz
    style: Style,
}

impl<'ev> PositionedGraphNode<'ev> {
    fn name(&self) -> String {
        self.ev
            .ev
            .map(|ev| ev.name.clone())
            .or_else(|| if self.ev.ev_label.0 == "IW" { Some("IW".to_string()) } else { None })
            .expect("GraphNode with no name")
    }
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

fn escape_str(s: String) -> String {
    format!("{:?}", s)
}

impl PositionedGraphNode<'_> {
    /// the width (in points) of the actual underlying node shape
    fn compute_width(&self) -> usize {
        (FONTSIZE * 3 / 5) * self.ev.label.len()
    }

    /// the height (in points) of the actual underlying node shape
    fn compute_height(&self) -> usize {
        SCALE as usize
    }
}

impl<'ev> GVGridChild<'ev> {
    /// the width (in points) of the node or the child grid
    fn compute_width(&self) -> usize {
        if self.layout.skinny {
            return 0;
        }

        let ww: usize = points_from_inches(self.layout.padding.left + self.layout.padding.right);
        match &self.node {
            GVGridNode::Node(pgn) => pgn.compute_width() + ww,
            GVGridNode::SubCluster(cluster) => cluster.compute_width() + ww,
        }
    }

    /// the height (in points) of the node or the child grid
    fn compute_height(&self) -> usize {
        if self.layout.skinny {
            return 0;
        }

        let wh: usize = points_from_inches(self.layout.padding.up + self.layout.padding.down);
        match &self.node {
            GVGridNode::Node(pgn) => pgn.compute_height() + wh,
            GVGridNode::SubCluster(cluster) => cluster.compute_height() + wh,
        }
    }

    /// a graphviz line for an event node
    /// in the following format:
    /// R1_79_0 [shape=box,pos="13,17!",label=<LABEL FORMAT>,fillcolor=wheat1,style=filled];
    fn fmt_as_node(&self) -> String {
        if let GVGridNode::Node(pge) = &self.node {
            let node_attrs: Vec<(String, String)> = vec![
                ("fillcolor".to_string(), pge.style.bg_color.to_string()),
                ("style".to_string(), pge.style.node_style.to_string()),
                (
                    "pos".to_string(),
                    if let Some((x, y)) = self.layout.pos { format!("\"{},{}!\"", x, -y) } else { "\"\"".to_string() },
                ),
                ("shape".to_string(), pge.style.node_shape.to_string()),
                ("label".to_string(), escape_str(pge.ev.label.clone())),
                ("width".to_string(), pge.style.dimensions.0.to_string()),
                ("height".to_string(), pge.style.dimensions.1.to_string()),
            ];

            let attrs = node_attrs.iter().map(|(attr, val)| format!("{}={}", attr, val)).collect::<Vec<_>>().join(", ");
            format!("{} [{}]", pge.name(), attrs)
        } else {
            "N/A".to_string()
        }
    }

    #[allow(dead_code)]
    fn unwrap_node(&self) -> &PositionedGraphNode<'ev> {
        if let GVGridNode::Node(n) = &self.node {
            n
        } else {
            panic!("cannot unwrap SubCluster")
        }
    }

    #[allow(dead_code)]
    fn unwrap_cluster(&self) -> &GraphLayout<'ev> {
        if let GVGridNode::SubCluster(n) = &self.node {
            n
        } else {
            panic!("cannot unwrap Node")
        }
    }

    #[allow(dead_code)]
    fn unwrap_node_mut(&mut self) -> &mut PositionedGraphNode<'ev> {
        if let GVGridNode::Node(n) = &mut self.node {
            n
        } else {
            panic!("cannot unwrap SubCluster")
        }
    }

    #[allow(dead_code)]
    fn unwrap_cluster_mut(&mut self) -> &mut GraphLayout<'ev> {
        if let GVGridNode::SubCluster(n) = &mut self.node {
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
                if let Some(GVGridChild { node: GVGridNode::SubCluster(cluster), .. }) = node {
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
        let mut new_children: HashMap<(usize, usize), GVGridChild> = HashMap::new();
        let mut count_subclusters = 0;

        for ((r, c), child_node) in self.children.drain() {
            let row_start = cum_rows.get(&r).unwrap_or(&0);
            let col_start = cum_cols.get(&c).unwrap_or(&0);
            let (row_start, col_start) = (*row_start as usize, *col_start as usize);
            match child_node.node {
                GVGridNode::SubCluster(mut cluster) => {
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

        for (&(r, c), child) in self.children.iter_mut() {
            let (x, y) = (cum_widths[&c], cum_heights[&r]);
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
                GVGridNode::Node(ref mut pgn) => {
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
                GVGridNode::SubCluster(ref mut cluster) => {
                    child.layout.bb_pos = Some((x, y));
                    child.layout.pos = Some((x, y));
                    cluster.accumulate_positions(xleft + wxl, y + wyu);
                }
            };
        }
    }

    fn iter_nodes<'a>(&'a self, only_visible: bool, only_real: bool) -> Vec<&GVGridChild<'a>> {
        let mut nodes: Vec<&GVGridChild<'a>> = Vec::new();

        for c in self.children.values() {
            if !c.layout.show && only_visible {
                continue;
            }

            if c.layout.skinny && only_real {
                continue;
            }

            match &c.node {
                GVGridNode::Node(_) => nodes.push(c),
                GVGridNode::SubCluster(cluster) => {
                    let sub_nodes = cluster.iter_nodes(only_visible, only_real);
                    nodes.extend(sub_nodes);
                }
            }
        }

        nodes
    }

    fn iter_nodes_mut(&mut self, only_visible: bool, only_real: bool) -> Vec<&mut GVGridChild<'g>> {
        let mut nodes: Vec<&mut GVGridChild<'g>> = Vec::new();

        for c in self.children.values_mut() {
            if !c.layout.show && only_visible {
                continue;
            }

            if c.layout.skinny && only_real {
                continue;
            }

            match c.node {
                GVGridNode::Node(_) => nodes.push(c),
                GVGridNode::SubCluster(ref mut cluster) => {
                    let sub_nodes = cluster.iter_nodes_mut(only_visible, only_real);
                    nodes.extend(sub_nodes);
                }
            }
        }

        nodes
    }

    fn find_node_mut(&mut self, name: &str) -> Option<&mut GVGridChild<'g>> {
        for n in self.iter_nodes_mut(false, false) {
            if let GVGridNode::Node(pge) = &n.node {
                if pge.name() == name {
                    return Some(n);
                }
            }
        }

        None
    }

    fn po(&self) -> Option<usize> {
        for c in self.iter_nodes(false, false) {
            if let GVGridNode::Node(pgn) = &c.node {
                if let Some(ev) = pgn.ev.ev {
                    return Some(ev.po);
                }
            }
        }

        None
    }

    #[allow(dead_code)]
    fn opcode(&self) -> Option<&String> {
        for c in self.iter_nodes(false, false) {
            if let GVGridNode::Node(pgn) = &c.node {
                if let Some(ev) = pgn.ev.ev {
                    return Some(ev.instr.as_ref().unwrap_or(&ev.opcode));
                }
            }
        }

        None
    }
}

impl PositionedGraphNode<'_> {
    // format the node label with all debug info:
    // label="W_00_000: "ldr x2, [x3]": T 0x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_debug(&self, opts: &GraphOpts, rc: (usize, usize), _names: &GraphValueNames<u64>) -> String {
        if let Some(ev) = &self.ev.ev {
            ev.fmt_label_debug(opts, &self.ev.ev_label, rc)
        } else {
            "N/A".to_string()
        }
    }

    // format the node label in longform:
    // label="ldr x2, [x3]\lT 0x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_long(&self, opts: &GraphOpts, names: &GraphValueNames<u64>) -> String {
        if let Some(ev) = &self.ev.ev {
            ev.fmt_label_long(opts, &self.ev.ev_label, names)
        } else {
            "N/A".to_string()
        }
    }

    // format the node label in half form:
    // label="T 0x205800 (8): 3146947"
    #[allow(dead_code)]
    fn fmt_label_medium(&self, opts: &GraphOpts, names: &GraphValueNames<u64>) -> String {
        if let Some(ev) = &self.ev.ev {
            ev.fmt_label_medium(opts, &self.ev.ev_label, names)
        } else {
            "N/A".to_string()
        }
    }

    // format the node label in shortform:
    // label="T 0x205800"
    #[allow(dead_code)]
    fn fmt_label_short(&self, opts: &GraphOpts, names: &GraphValueNames<u64>) -> String {
        if let Some(ev) = &self.ev.ev {
            ev.fmt_label_short(opts, &self.ev.ev_label, names)
        } else {
            "N/A".to_string()
        }
    }
}

fn produce_node_layout<'ev>(
    graph: &'ev Graph,
    _litmus_opts: &LitmusGraphOpts,
    opts: &GraphOpts,
    _pas: HashSet<&String>,
) -> GraphLayout<'ev> {
    use GridInstrInstance::*;
    let grid: GridLayout<'ev, usize> = GridLayout::from_graph(graph, opts).annotate_widths(|gn| gn.label.len());

    let mut tids = HashSet::new();
    for ev in graph.events.values() {
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
    let iw_pgn = GVGridNode::Node(PositionedGraphNode {
        ev: GridNode {
            ev: None,
            ev_label: ("IW".to_string(), "".to_string()),
            alignment: Align::Middle,
            label: "Initial State".to_string(),
            annot: 2,
        },
        style: Style {
            bg_color: "white".to_string(),
            node_shape: "oval".to_string(),
            node_style: "filled".to_string(),
            dimensions: (0.0, 0.0),
        },
    });
    top_level_layout.children.insert((0, 0), GVGridChild { node: iw_pgn, layout: layout_iw });

    let mut thread_layouts = GraphLayout { children: HashMap::new() };

    let push_new = &mut |rc: (usize, usize), gn: GridNode<'ev, usize>, layout: &mut GraphLayout<'ev>| {
        let style = event_style(&gn);
        layout.children.insert(
            rc,
            GVGridChild { node: GVGridNode::Node(PositionedGraphNode { ev: gn, style }), layout: layout_event.clone() },
        );
    };

    for (tid, t) in grid.threads.into_iter().enumerate() {
        let mut thread = GraphLayout { children: HashMap::new() };
        for (iid, i) in t.instr_instances.into_iter().enumerate() {
            let mut instr = GraphLayout { children: HashMap::new() };
            match i {
                SingleEventInstr(e) => {
                    push_new((0, 0), e, &mut instr);
                }
                SingleRowEventsInstr(r) => {
                    for (ci, gn) in r.into_iter().enumerate() {
                        push_new((0, ci), gn, &mut instr);
                    }
                }
                MultiRowEventsInstr(m) => {
                    let mut subinstr = GraphLayout { children: HashMap::new() };

                    for (ridx, r) in m.into_iter().enumerate() {
                        for (cidx, gn) in r.into_iter().enumerate() {
                            push_new((ridx, cidx), gn, &mut subinstr);
                        }
                    }
                }
            }
            thread
                .children
                .insert((iid, 0), GVGridChild { node: GVGridNode::SubCluster(instr), layout: layout_instr.clone() });
        }
        thread_layouts
            .children
            .insert((0, tid), GVGridChild { node: GVGridNode::SubCluster(thread), layout: layout_thread.clone() });
    }

    let threads_node = GVGridNode::SubCluster(thread_layouts);
    top_level_layout.children.insert((1, 0), GVGridChild { node: threads_node, layout: layout_threads });

    if opts.flatten {
        // explode out into a big flat grid,
        // then use that to align rows and columns and layout things
        let mut exploded = top_level_layout.clone();
        let threads = exploded.children.get_mut(&(1, 0)).unwrap().unwrap_cluster_mut();

        // flatten each thread to keep `po` vertical etc
        for thread in threads.children.values_mut() {
            if let GVGridNode::SubCluster(thread_gl) = &mut thread.node {
                thread_gl.flatten();
            }
        }

        exploded.accumulate_positions(0, 0);

        for n in exploded.iter_nodes(false, false) {
            let pge = n.unwrap_node();
            if let Some(tll_n) = top_level_layout.find_node_mut(&pge.name()) {
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
fn draw_box(
    _graph: &Graph,
    f: &mut dyn io::Write,
    ident: &str,
    label: &str,
    node: &GVGridChild<'_>,
    graphstyle: &str,
    style: &str,
) -> io::Result<()> {
    if let GVGridNode::SubCluster(cluster) = &node.node {
        let mut tl: (i64, i64) = (i64::MAX, i64::MAX);
        let mut br: (i64, i64) = (0, 0);
        // find top-left
        for n in cluster.iter_nodes(false, true) {
            if let GVGridNode::Node(pgn) = &n.node {
                let (nw, nh) = (pgn.compute_width() as i64, pgn.compute_height() as i64);

                // use the pos of the bounding box
                // not the centre of the node
                if let Some((x, y)) = n.layout.bb_pos {
                    let (x, y) = (x, y);

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
pub fn draw_graph_gv(f: &mut dyn io::Write, graph: &Graph, _opts: &GraphOpts) -> io::Result<()> {
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
    for ev in graph.events.values() {
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
    let mutated_pas_event_names: HashSet<&String> = graph
        .events
        .values()
        .flat_map(|ev| match &ev.value {
            Some(GraphValue { address: Some(addr), .. }) if mutated_pas.contains(addr) => Some(&ev.name),
            _ => None,
        })
        .collect();

    log!(log::GRAPH, "producing GraphLayout ...");
    let node_layout = produce_node_layout(graph, &graph.litmus_opts, &graph.opts, mutated_pas);
    let graph_event_nodes = node_layout.iter_nodes(true, false);
    log!(log::GRAPH, "produced node layout");

    if let Some(iw) = node_layout.children.get(&(0, 0)) {
        writeln!(f, "{};", iw.fmt_as_node())?;
    }

    if let Some(GVGridChild { node: GVGridNode::SubCluster(thread_clusters), .. }) = node_layout.children.get(&(1, 0)) {
        let mut displayed_event_names: HashSet<String> = HashSet::new();
        displayed_event_names.insert("IW".to_string());

        let displayed_graph_events: Vec<&GraphEvent> = graph_event_nodes
            .iter()
            .flat_map(|c| match c.node {
                GVGridNode::Node(PositionedGraphNode { ev: GridNode { ev: Some(ev), .. }, .. }) => Some(ev),
                _ => None,
            })
            .collect();

        for tid in thread_ids {
            log!(log::GRAPH, &format!("drawing Thread#{}", tid));
            let mut events: Vec<&GraphEvent> = graph.events.values().filter(|ev| ev.thread_id == tid).collect();
            events.sort_by(|ev1, ev2| (ev1.thread_id, ev1.po, ev1.iio).cmp(&(ev2.thread_id, ev2.po, ev2.iio)));

            let displayed_thread_events: Vec<&GraphEvent> =
                displayed_graph_events.clone().into_iter().filter(|ge| ge.thread_id == tid).collect();

            // draw the events and boxes
            if let Some(thread_child) = thread_clusters.children.get(&(0, tid)) {
                if !displayed_thread_events.is_empty() {
                    let thread_box_label = format!("Thread {}", tid);
                    draw_box(
                        graph,
                        f,
                        &format!("{}", tid),
                        &thread_box_label,
                        thread_child,
                        "labeljust=l",
                        "style=dashed;",
                    )?;
                }

                if let GVGridChild { node: GVGridNode::SubCluster(thread), .. } = thread_child {
                    for ((po_row, _), instr) in thread.children.iter() {
                        if let GVGridNode::SubCluster(instr_cluster) = &instr.node {
                            if let Some(po) = instr_cluster.po() {
                                let displayed_instr_events: Vec<&GraphEvent> =
                                    displayed_thread_events.clone().into_iter().filter(|ge| ge.po == po).collect();

                                if displayed_instr_events.len() > 1 {
                                    draw_box(
                                        graph,
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
                                        if let GVGridNode::Node(PositionedGraphNode {
                                            ev: GridNode { ev: Some(ev), .. },
                                            ..
                                        }) = ev.node
                                        {
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

        // we don't draw the full relations
        // instead, some events are hidden
        // then what's left we might transitively reduce/close etc
        // and finally, we might hide some edges if they're superimposed on another.
        let mut draw_relations: HashMap<String, HashSet<(String, String)>> = HashMap::new();

        for rel in &graph.relations {
            if !rel.edges.is_empty() {
                let edges = &rel.all_edges;

                // hide edges between hidden nodes
                let edges: HashSet<(String, String)> = edges
                    .iter()
                    .filter(|(from, to)| displayed_event_names.contains(from) && displayed_event_names.contains(to))
                    .map(|(from, to)| (from.clone(), to.clone()))
                    .collect();

                // now perform any transitive simplifications
                let edges = simplify_edges(&rel.ty, &edges);
                draw_relations.insert(rel.name.clone(), edges);
            }
        }

        // now hide edges that are superceded by others
        // need a copy of the original because the priority might be transitive...
        let orig = draw_relations.clone();
        for rel in &graph.relations {
            if !rel.edges.is_empty() {
                let pairs = draw_relations.get_mut(&rel.name).unwrap();
                for (e1, e2) in pairs.clone() {
                    let k = (e1, e2);
                    for preferred_rel_name in rel.ty.preferred.iter() {
                        let s = String::from(*preferred_rel_name);
                        match orig.get(&s) {
                            // if any "preferred" relation also contains the edge (e1,e2) then don't show this one.
                            Some(preferred_rel) if preferred_rel.contains(&k) => {
                                pairs.remove(&k);
                            }
                            _ => (),
                        }
                    }
                }
            }
        }

        log!(log::GRAPH, "finished nodes, now writing relations...");

        if graph.opts.control_delimit {
            write!(f, "\x1D")?
        };

        for rel in &graph.relations {
            let mut symmetric_edges: HashSet<(String, String)> = HashSet::new();

            if !rel.edges.is_empty() {
                if graph.opts.control_delimit {
                    writeln!(f, "\x1E{}\x1F", rel.name)?
                };

                // some of the edges are to hidden nodes
                // so we simply hide the edges, and re-compute the reductions
                let edges: &HashSet<(String, String)> = draw_relations.get(&rel.name).unwrap();

                log!(log::GRAPH, &format!("drawing relation {} (#{})", rel.name, edges.len()));
                for (from, to) in edges {
                    // do not show IW -(rf)-> R
                    // when R's addr is not written by the test
                    if let Some(to_event) = &graph.events.get(to) {
                        if !graph.opts.debug
                            && rel.name.ends_with("rf")
                            && from == "IW"
                            && !mutated_pas_event_names.contains(&to)
                            && !event_in_shows(&graph.opts.force_show_events, to_event)
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
                    let label = if rel.name != "po" || graph.opts.debug {
                        format!("{}=\" {} \",", labelattr, rel.name)
                    } else {
                        "".to_string()
                    };
                    let color = relation_color(&rel.name);
                    writeln!(f, " {} -> {} [{}color={}, {}fontcolor={}];", from, to, dir, color, label, color)?;
                }
            }
        }
        if graph.opts.control_delimit {
            write!(f, "\x1D")?
        }
    }

    log!(log::VERBOSE, "generated graph");
    writeln!(f, "}}")
}
