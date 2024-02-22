use std::io;

use super::grid_layout::{Align, FlatGridLayout, GridLayout, MultiCol};
use super::{graph_events::*, GraphOpts};

mod combinators {
    pub struct Combinations<'a, A> {
        index: (usize, usize),
        slice: &'a [A],
    }

    impl<'a, A> Combinations<'a, A> {
        fn inc(&mut self) {
            self.index = (self.index.0, self.index.1 + 1);
            if self.index.1 >= self.slice.len() {
                self.index = (self.index.0 + 1, self.index.0 + 2);
            }
        }

        pub fn from_slice(slice: &'a [A]) -> Self {
            Combinations { index: (0, 1), slice }
        }
    }

    impl<'a, A> Iterator for Combinations<'a, A> {
        type Item = (&'a A, &'a A);

        fn next(&mut self) -> Option<Self::Item> {
            if self.index.0 >= self.slice.len() - 1 {
                return None;
            };

            let v1 = &self.slice[self.index.0];
            let v2 = &self.slice[self.index.1];

            self.inc();
            Some((v1, v2))
        }
    }
}

fn write_aligned(f: &mut dyn io::Write, alignment: Align, w: usize, msg: &String) -> io::Result<()> {
    match alignment {
        Align::Left => write!(f, "{:<width$}", msg, width = w),
        Align::Middle => write!(f, "{:^width$}", msg, width = w),
        Align::Right => write!(f, "{:>width$}", msg, width = w),
    }
}

fn write_node<A>(f: &mut dyn io::Write, n: &MultiCol<'_, '_, A>, w: usize) -> io::Result<()> {
    match n.node {
        None => write_aligned(f, Align::Left, w, &"".to_string()),
        Some(gn) => write_aligned(f, gn.alignment, w, &gn.label),
    }
}

type ChainNode<'ev> = &'ev (String, Option<String>);
type Relation = String;

#[derive(Debug)]
struct RelationChain<'ev> {
    anchor: ChainNode<'ev>,
    chain: Vec<(Relation, ChainNode<'ev>)>,
}

impl<'ev> IntoIterator for RelationChain<'ev> {
    type Item = (Relation, ChainNode<'ev>);
    type IntoIter = std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.chain.into_iter()
    }
}

#[derive(Debug)]
enum ChainResult<'ev> {
    Missing,
    Split(RelationChain<'ev>),
    Appended,
}

impl<'ev> ChainResult<'ev> {
    fn unwrap_appended(self) {
        match self {
            Self::Appended => (),
            _ => panic!("unwrap_appended non-Appended ChainResult"),
        }
    }
}

impl<'ev> RelationChain<'ev> {
    fn empty(anchor: ChainNode<'ev>) -> Self {
        RelationChain { anchor, chain: vec![] }
    }

    fn last(&self) -> Option<ChainNode<'ev>> {
        if let Some(e) = self.chain.last() {
            Some(e.1)
        } else {
            Some(self.anchor)
        }
    }

    /// given an edge (a, R, b) follow this chain until `a`
    /// then either append (b, R) to the end of the chain
    /// or fork into two new chains
    fn insert_or_split(&mut self, a: ChainNode<'ev>, r: String, b: ChainNode<'ev>) -> ChainResult<'ev> {
        if self.last() == Some(a) {
            self.chain.push((r, b));
            ChainResult::Appended
        } else {
            // if not at the end, might be in the middle
            let mut split = RelationChain::empty(self.anchor);

            let mut check_split = false;
            for (chain_r, chain_e) in self.chain.iter() {
                if check_split {
                    if *chain_r == r && *chain_e == b {
                        return ChainResult::Appended;
                    } else {
                        split.chain.push((r.clone(), b));
                        return ChainResult::Split(split);
                    }
                }

                split.chain.push((chain_r.clone(), *chain_e));

                if *chain_e == a {
                    // found [..., a, ...] in the chain
                    // either it's [..., a, (r, b), ...] so we can skip
                    // or it's [..., a, (!r, !b), ...] and we must split
                    // but do not know until the next iteration
                    // (which we know must exist, because this wasn't the last())
                    check_split = true;
                }
            }

            ChainResult::Missing
        }
    }
}

#[derive(Debug)]
struct RelationChains<'ev> {
    chains: Vec<RelationChain<'ev>>,
}

/// Collect together unbroken chains of events in the execution
impl<'ev> RelationChains<'ev> {
    fn insert(&mut self, a: ChainNode<'ev>, r: String, b: ChainNode<'ev>) {
        let mut found = false;
        let mut new_chains: Vec<RelationChain<'ev>> = vec![];
        for c in self.chains.iter_mut() {
            match c.insert_or_split(a, r.clone(), b) {
                ChainResult::Split(split) => {
                    new_chains.push(split);
                    found = true;
                    break;
                }
                ChainResult::Appended => {
                    found = true;
                    break;
                }
                ChainResult::Missing => (),
            }
        }

        if !found {
            let mut chain = RelationChain::empty(a);
            chain.insert_or_split(a, r, b).unwrap_appended();
            new_chains.push(chain);
        }

        self.chains.append(&mut new_chains);
    }
}

impl<'ev> IntoIterator for RelationChains<'ev> {
    type Item = RelationChain<'ev>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.chains.into_iter()
    }
}

fn write_chain(f: &mut dyn io::Write, chain: RelationChain<'_>) -> io::Result<()> {
    write!(f, "  {}", chain.anchor.0)?;
    for (r, b) in chain {
        write!(f, " -({})-> {}", r, b.0.clone())?;
    }
    writeln!(f, ";")?;
    Ok(())
}

pub fn draw_graph_ascii(f: &mut dyn io::Write, graph: &Graph, opts: &GraphOpts) -> io::Result<()> {
    let layout = GridLayout::from_graph(graph, opts);
    let events: Vec<(String, Option<String>)> =
        layout.events().into_iter().map(|gn| (format_ev_label(&gn.ev_label), gn.ev.map(|e| e.name.clone()))).collect();
    let nthreads = layout.threads.len();
    let annot = layout.annotate_widths(|n| n.label.len());
    let flat = FlatGridLayout::from_layout(&annot);
    let grid_dimensions = flat.dimensions();

    // write Thread~N headers
    for tid in 0..nthreads {
        write_aligned(f, Align::Middle, grid_dimensions.thread_width(tid).unwrap(), &format!("Thread {}", tid))?;
        write!(f, " ")?;
    }

    writeln!(f)?;

    // now write each of the rows
    for r in flat.grid {
        for c in r {
            let w = c.char_width(&grid_dimensions);
            write_node(f, &c, w)?;
            write!(f, " ")?;
        }
        writeln!(f)?;
    }

    writeln!(f)?;

    // now draw out the relations in a cycle-ish way
    writeln!(f, "relations: ")?;

    let combinations = combinators::Combinations::from_slice(&events);
    let mut chains = RelationChains { chains: vec![] };

    for (a, b) in combinations {
        if let (Some(e1), Some(e2)) = (a.1.clone(), b.1.clone()) {
            // collect all relations between (e1, e2) and render them as r1&r2&r3&r4
            let rels = graph.between(e1.clone(), e2.clone());
            let rel_names: Vec<String> = rels.into_iter().map(|r| r.name.clone()).collect();
            let anded = rel_names.join("&");

            if !anded.is_empty() {
                chains.insert(a, anded, b);
            }
        }
    }

    // now we have collected the chains, render them all out
    for chain in chains {
        write_chain(f, chain)?;
    }

    Ok(())
}
