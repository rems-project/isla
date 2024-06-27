use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use isla_lib::bitvector::BV;
use isla_lib::ir::*;
use isla_lib::smt::Event;

use crate::axiomatic::relations;
use crate::axiomatic::{AxEvent, ThreadId};
use crate::litmus::LitmusGraphOpts;
use crate::litmus::{instruction_from_objdump, Objdump};
use crate::page_table::PageAttrs;

use super::graph_opts::*;
use super::grid_layout::simplify_edges;

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
    pub fn populate_values(&mut self) {
        let mut hm = HashMap::new();
        hm.extend(self.va_names.iter().map(|(i, s)| (*i, s.clone())));
        hm.extend(self.ipa_names.iter().map(|(i, s)| (*i, s.clone())));
        hm.extend(self.pa_names.iter().map(|(i, s)| (*i, s.clone())));
        self.value_names = hm;
    }

    pub fn populate_addrs(&mut self) {
        let mut hm = HashMap::new();
        hm.extend(self.s1_ptable_names.iter().map(|(i, s)| (*i, s.clone())));
        hm.extend(self.s2_ptable_names.iter().map(|(i, s)| (*i, s.clone())));
        hm.extend(self.pa_names.iter().map(|(i, s)| (*i, s.clone())));
        self.paddr_names = hm;
    }
}

impl<B: BV> GraphValueNames<B> {
    pub fn to_u64(&self) -> GraphValueNames<u64> {
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
    pub prefix: String,
    pub address: Option<String>,
    pub virtual_address: Option<String>,
    pub bytes: String,
    pub value: Option<String>,
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
    pub instr: Option<String>,
    pub opcode: String,
    pub po: usize,
    pub iio: usize,
    pub thread_id: ThreadId,
    pub name: String,
    pub value: Option<GraphValue>,
    pub event_kind: GraphEventKind,
}

pub fn event_kind<B: BV>(_objdump: &Objdump, ev: &AxEvent<B>) -> GraphEventKind {
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

pub fn update_event_kinds(evs: &mut HashMap<String, GraphEvent>) {
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

pub fn try_guess_descriptor(opts: &GraphOpts, names: &HashMap<u64, String>, desc: u64) -> String {
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

pub fn named_str_from_value(opts: &GraphOpts, names: &HashMap<u64, String>, v: &str) -> String {
    if v.len() < 2 {
        return v.to_string();
    }

    // symbolic values start with a v, and should be left unchanged
    if v.starts_with('v') {
        return v.to_string();
    }

    if !v.starts_with("#x") && !v.starts_with("0x") {
        panic!("ill-formed bitvector: '{}'", v)
    }

    match u64::from_str_radix(&v[2..v.len()], 16) {
        Err(_) => v.to_string(),
        Ok(i) => match names.get(&i) {
            Some(s) => s.clone(),
            None => try_guess_descriptor(opts, names, i),
        },
    }
}

pub fn named_str_from_addr(_opts: &GraphOpts, names: &HashMap<u64, String>, v: &str) -> String {
    if v.len() < 2 {
        return v.to_string();
    }

    match u64::from_str_radix(&v[2..v.len()], 16) {
        Err(_) => v.to_string(),
        Ok(i) => match names.get(&i) {
            Some(s) => s.clone(),
            None => v.to_string(),
        },
    }
}

pub fn str_from_value<B: BV>(v: &Val<B>) -> String {
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
    pub fn from_axiomatic<B: BV>(ev: &AxEvent<B>, objdump: &Objdump, value: Option<GraphValue>) -> Self {
        let (instr, opcode) = if let Some(opcode) = ev.opcode {
            (instruction_from_objdump(&format!("{:x}", opcode), objdump), format!("{:x}", opcode))
        } else {
            (None, "none".to_string())
        };
        GraphEvent {
            instr,
            opcode,
            po: ev.instruction_index,
            iio: ev.intra_instruction_index,
            thread_id: ev.thread_id,
            name: ev.name.clone(),
            value,
            event_kind: event_kind(objdump, ev),
        }
    }
}

pub fn format_ev_label(ev_label: &(String, String)) -> String {
    format!("{}{}", ev_label.0, ev_label.1)
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
            instr.to_string()
        }
    }

    // format the node label with all debug info:
    // label="W_00_000: "ldr x2, [x3]": T 0x205800 (8): 3146947"
    #[allow(dead_code)]
    pub fn fmt_label_debug(&self, _opts: &GraphOpts, ev_label: &(String, String), rc: (usize, usize)) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        let ev_lab = format_ev_label(ev_label);
        if let Some(value) = &self.value {
            let q = "?".to_string();
            let addrstr = value.address.as_ref().unwrap_or(&q);
            let valstr = value.value.as_ref().unwrap_or(&q);
            format!(
                "{} @ {:?}: \\{}\\: {}",
                self.name,
                rc,
                instr,
                format_args!("{}: {} {} ({}): {}", ev_lab, value.prefix, addrstr, value.bytes, valstr)
            )
        } else {
            format!("{} @ {:?}: \\{}\\", self.name, rc, instr)
        }
    }

    // format the node label in longform:
    // label="ldr x2, [x3]\lT 0x205800 (8): 3146947"
    #[allow(dead_code)]
    pub fn fmt_label_long(
        &self,
        opts: &GraphOpts,
        ev_label: &(String, String),
        names: &GraphValueNames<u64>,
    ) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        let ev_lab = format_ev_label(ev_label);
        match self.event_kind {
            GraphEventKind::Barrier(BarrierKind::Fault) => format!("{}: {}: Fault", ev_lab, instr),
            GraphEventKind::Barrier(BarrierKind::Fence) => format!("{}: {}", ev_lab, self.fmt_barrier(opts, names)),
            GraphEventKind::CacheOp => {
                let q = "?".to_string();
                let addr = if let Some(value) = &self.value { value.value.as_ref().unwrap_or(&q) } else { &q };
                let extra_data = if let Some(value) = &self.value { value.address.as_ref().unwrap_or(&q) } else { &q };

                let addr = u64::from_str_radix(&addr[2..addr.len()], 16).expect("got unknown addr");
                let extra = u64::from_str_radix(&extra_data[2..extra_data.len()], 16).expect("got unknown extra data");
                if instr.contains("va") {
                    format!(
                        "{}: \"{}\": page={}",
                        ev_lab,
                        instr,
                        named_str_from_addr(opts, &names.va_names, &format!("0x{:x}", addr))
                    )
                } else if instr.contains("ipa") {
                    format!(
                        "{}: \"{}\": page={}",
                        ev_lab,
                        instr,
                        named_str_from_addr(opts, &names.ipa_names, &format!("0x{:x}", addr))
                    )
                } else if instr.contains("asid") {
                    format!("{}: \"{}\": asid=0x{:x}", ev_lab, instr, addr >> 48)
                } else if instr.contains("vm") {
                    format!("{}: \"{}\": vmid=0x{:x}", ev_lab, instr, extra)
                } else {
                    format!("{}: \"{}\"", ev_lab, instr)
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
                        "{}: \"{}\": {}",
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
                    format!("{}: \"{}\"", ev_lab, instr)
                }
            }
        }
    }

    // format the node label in half form:
    // label="T 0x205800 (8): 3146947"
    #[allow(dead_code)]
    pub fn fmt_label_medium(
        &self,
        opts: &GraphOpts,
        ev_label: &(String, String),
        names: &GraphValueNames<u64>,
    ) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        let ev_lab = format!("{}{}", ev_label.0, ev_label.1);
        match &self.event_kind {
            GraphEventKind::Barrier(BarrierKind::Fault) => format!("{}: {}: Fault", ev_lab, instr),
            GraphEventKind::Barrier(BarrierKind::Fence) => format!("{}: {}", ev_lab, self.fmt_barrier(opts, names)),
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
                        "{}: {}",
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
                    format!("??{}:\"{}\"", self.name, instr)
                }
            }
        }
    }

    // format the node label in shortform:
    // label="T 0x205800"
    #[allow(dead_code)]
    pub fn fmt_label_short(
        &self,
        opts: &GraphOpts,
        ev_label: &(String, String),
        names: &GraphValueNames<u64>,
    ) -> String {
        let instr = self.instr.as_ref().unwrap_or(&self.opcode);
        let ev_lab = format_ev_label(ev_label);
        match &self.event_kind {
            GraphEventKind::Barrier(BarrierKind::Fault) => format!("{}: Fault", ev_lab),
            GraphEventKind::Barrier(BarrierKind::Fence) => format!("{}: {}", ev_lab, self.fmt_barrier(opts, names)),
            GraphEventKind::Translate(TranslateKind { stage, level, .. }) if opts.squash_translation_labels => {
                format!("{}: Ts{}l{}", ev_lab, stage, level)
            }
            _ => {
                if let Some(value) = &self.value {
                    let q = "?".to_string();
                    let addrstr = value.address.as_ref().unwrap_or(&q);
                    format!(
                        "{}: {} {}",
                        ev_lab,
                        value.prefix,
                        named_str_from_addr(opts, self._name_bag_for_addr(names), addrstr)
                    )
                } else {
                    format!("{}: \"{}\": {}", ev_lab, instr, self.name)
                }
            }
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
    /// the edges to actually display in the graph
    pub edges: HashSet<(String, String)>,
    /// all of the underlying edges
    pub all_edges: HashSet<(String, String)>,
}

impl GraphRelation {
    pub fn simplify(mut self) -> GraphRelation {
        self.edges = simplify_edges(&self.ty, &self.edges);
        self
    }
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

pub fn relation_color(rel: &str) -> &'static str {
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
pub enum RelTransType {
    TransClosure,
    TransReduction,
    Normal,
}

#[derive(Debug, Clone)]
pub struct RelType {
    /// Whether this relation should be drawn transitively reduced or closed or neither.
    pub trans: RelTransType,
    /// the list of other relations that take preference to this one
    /// i.e. if going to draw (e1 Rel e2) check that no (e1, e2) is in any preferred relation
    pub preferred: Vec<&'static str>,
}

/// given a relation name return (base, type)
pub fn parse_relname_opt(rel: &str) -> (&str, RelType) {
    let mut relname = rel;
    let mut relty = RelType { trans: RelTransType::Normal, preferred: Vec::new() };

    if rel.ends_with('-') {
        relname = &rel[0..rel.len() - 1];
        relty.trans = RelTransType::TransReduction;
    } else if rel.ends_with('+') {
        relname = &rel[0..rel.len() - 1];
        relty.trans = RelTransType::TransClosure;
    } else if rel.ends_with('~') {
        relname = &rel[0..rel.len() - 1];
    } else {
        let trans_reductions: HashSet<String> =
            GraphOpts::DEFAULT_REL_TRANSITIVE_REDUCE.iter().cloned().map(String::from).collect();
        if trans_reductions.contains(rel) {
            relty.trans = RelTransType::TransReduction;
        }

        for (r1, r2) in GraphOpts::DEFAULT_REL_PRIORITY {
            if *r2 == rel {
                relty.preferred.push(r1);
            }
        }
    }

    (relname, relty)
}

impl Graph {
    pub fn between(&self, ev1: String, ev2: String) -> Vec<&GraphRelation> {
        let mut rels = Vec::new();
        let k = (ev1, ev2);
        for r in &self.relations {
            if r.edges.contains(&k) {
                rels.push(r);
            }
        }
        rels
    }
}
