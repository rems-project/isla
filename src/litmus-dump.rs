// BSD -Clause License
//
// Copyright (c) 2022-2023 Thibaut Pérami
// Copyright (c) 2020-2023 Alasdair Armstrong
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

use isla_lib::smt::EnumMember;
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::ffi::OsStr;
use std::fmt::Display;
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::ops::Range;
use std::path::PathBuf;
use std::process::{self, Command};
use std::time::Instant;

use isla_axiomatic::footprint_analysis::{footprint_analysis, Footprint};
use isla_axiomatic::litmus::exp;
use isla_axiomatic::litmus::Litmus;
use isla_axiomatic::run_litmus;
use isla_axiomatic::run_litmus::{LitmusRunOpts, LitmusSetup, PCLimitMode};
use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::config::ISAConfig;
use isla_lib::init::{initialize_architecture, InitArchWithConfig};
use isla_lib::ir::{AssertionMode, Name, SharedState, Symtab, Val};
use isla_lib::log;
use isla_lib::memory::{Address, Memory, Region};
use isla_lib::simplify;
use isla_lib::simplify::{EventTree, Taints, WriteOpts};
use isla_lib::smt::smtlib::{Def, Exp, Ty};
use isla_lib::smt::{Accessor, EnumId, EvPath, Event, Sym};
use isla_lib::zencode;

use pretty::{docs, DocAllocator, DocBuilder, Pretty};

mod opts;
use opts::CommonOpts;

/** This command provide a way to have isla preprocess a litmus test (or later
    an objdump) and dump enough information so that concurrency model
    implementations not inside isla can run the test without having to look at
    either the Sail specification or the litmus test file.
    Such a dump must describe:
    - The precise initial state of the processor (register and memory).
    - Enough of the instruction semantics to run the test (in the form of isla traces)
    - Enough footprint information to recover the dependency between instruction
    - The required predicate.
    - Optional: Page Table setup constraints (not sure which model runner will need it.

    In particular, the instruction semantic much be wide enough that any
    sensible concurrency model will not go out of the covered semantics. The
    traces will contain the necessary assumptions, so going out of the covered
    semantics will result in an explicit failure and not an implicit
    unsoundness.

*/

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    process::exit(code)
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optopt("", "footprint-config", "load custom config for footprint analysis", "<file>");
    opts.optopt(
        "",
        "cache",
        "A directory to cache intermediate results. The default is TMPDIR if set, otherwise /tmp",
        "<path>",
    );
    opts.optopt("o", "output", "Output file", "<file>");
    opts.optopt("f", "format", "Output Format", "coq|human");
    opts.optopt("", "memory", "Add a max memory consumption (in megabytes)", "<n>");

    let now = Instant::now();

    // Parsing the options
    let mut hasher = Sha256::new();
    let (matches, orig_arch) = opts::parse::<B64>(&mut hasher, &opts);

    // Get the litmus test
    let test_file = if !matches.free.is_empty() {
        PathBuf::from(matches.free[0].clone())
    } else {
        eprintln!("Please provide a test file");
        opts::print_usage(&opts, "test", 1);
    };

    // Load the architecture
    let CommonOpts { num_threads, mut arch, symtab, type_info, isa_config, source_path: _ } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &orig_arch);

    let iarch = initialize_architecture(&mut arch, symtab, type_info, &isa_config, AssertionMode::Optimistic, true);
    let iarch_config = InitArchWithConfig::from_initialized(&iarch, &isa_config);
    let shared_state = &iarch.shared_state;
    let symtab = &shared_state.symtab;
    let type_info = &shared_state.type_info;

    // Huge hack, just load an entirely separate copy of the architecture for footprint analysis
    let CommonOpts {
        num_threads: _,
        arch: mut farch,
        symtab: fsymtab,
        type_info: ftype_info,
        isa_config: _,
        source_path: _,
    } = opts::parse_with_arch(&mut hasher, &opts, &matches, &orig_arch);

    let footprint_config = if let Some(file) = matches.opt_str("footprint-config") {
        match ISAConfig::from_file(&mut hasher, file, matches.opt_str("toolchain").as_deref(), &fsymtab, &ftype_info) {
            Ok(isa_config) => Some(isa_config),
            Err(e) => {
                eprintln!("{}", e);
                return 1;
            }
        }
    } else {
        None
    };
    let footprint_config = if footprint_config.is_some() {
        log!(log::VERBOSE, "Using separate footprint config".to_string());
        footprint_config.as_ref().unwrap()
    } else {
        &isa_config
    };

    let fiarch =
        initialize_architecture(&mut farch, fsymtab, ftype_info, footprint_config, AssertionMode::Optimistic, true);
    let fiarch_config = InitArchWithConfig::from_initialized(&fiarch, footprint_config);

    let arch_hash = hasher.result();
    log!(log::VERBOSE, &format!("Archictecture + config hash: {:x}", arch_hash));
    log!(log::VERBOSE, &format!("Parsing took: {}ms", now.elapsed().as_millis()));

    // Create a cache directory.
    let cache = matches.opt_str("cache").map(PathBuf::from).unwrap_or_else(std::env::temp_dir);
    fs::create_dir_all(&cache).expect("Failed to create cache directory if missing");
    if !cache.is_dir() {
        eprintln!("Invalid cache directory");
        return 1;
    }

    // Load litmus test
    let litmus_text = if test_file.extension() == Some(OsStr::new("litmus")) {
        let mut opt_args = Vec::new();
        if
        /*armv8_page_tables*/
        false {
            opt_args.push("--armv8-page-tables")
        };
        let output =
            Command::new("isla-litmus").args(&opt_args).arg(&test_file).output().expect("Failed to invoke isla-litmus");

        if output.status.success() {
            String::from_utf8_lossy(&output.stdout).to_string()
        } else {
            eprintln!(
                "Failed to translate litmus file: {}\n{}",
                test_file.display(),
                String::from_utf8_lossy(&output.stderr)
            );
            process::exit(1);
        }
    } else {
        match fs::read_to_string(&test_file) {
            Ok(litmus) => litmus,
            Err(msg) => {
                eprintln!("Failed to read litmus file: {}\n{}", test_file.display(), msg);
                process::exit(1);
            }
        }
    };

    let litmus = match Litmus::parse(&litmus_text, &symtab, &type_info, &isa_config) {
        Ok(litmus) => litmus,
        Err(msg) => {
            eprintln!("Failed to parse litmus file: {}\n{}", test_file.display(), msg);
            process::exit(1);
        }
    };

    let memory: Option<u64> = match matches.opt_get("memory") {
        Ok(memory) => memory,
        Err(e) => {
            eprintln!("Failed to parse --memory: {}", e);
            return 1;
        }
    };

    let opts = LitmusRunOpts {
        num_threads,
        timeout: None,
        memory,
        ignore_ifetch: true,
        exhaustive: true,
        armv8_page_tables: false,
        merge_translations: None,
        remove_uninteresting_translates: None,
        pc_limit: None,
        pc_limit_mode: PCLimitMode::Error,
    };

    let setup = run_litmus::run_litmus_setup::<B64, _, ()>(&opts, &litmus, &iarch_config, |_| true).unwrap();

    let footprints =
        footprint_analysis(opts.num_threads, &setup.threads, &fiarch_config, Some(cache.as_ref())).unwrap();

    // From now on we have all the information we need, we just need to print it
    let format = matches.opt_str("format").unwrap_or_else(|| String::from("human"));
    match matches.opt_str("output") {
        Some(file) => {
            let mut file: File = File::create(file.as_str()).unwrap_or_else(|err| {
                eprintln!("Couldn't open {} for writing: {}", file.as_str(), err);
                process::exit(1)
            });
            print_litmus(&mut file, format.as_str(), &setup, &footprints, &shared_state);
        }
        None => {
            let mut stdout = std::io::stdout();
            print_litmus(&mut stdout, format.as_str(), &setup, &footprints, &shared_state);
        }
    }

    0
}

fn get_simplified_evtree<B: BV>(traces: &[EvPath<B>]) -> Result<EventTree<B>, ()> {
    let mut evtree: Option<EventTree<B>> = None;
    for events in traces {
        if let Some(ref mut evtree) = evtree {
            evtree.add_events(events)
        } else {
            evtree = Some(EventTree::from_events(events))
        }
    }
    if let Some(mut evtree) = evtree {
        simplify::hide_initialization_tree(&mut evtree);
        simplify::remove_extra_register_fields_tree(&mut evtree);
        simplify::remove_repeated_register_reads_tree(&mut evtree);
        simplify::remove_unused_register_assumptions_tree(&mut evtree);
        simplify::remove_unused_tree(&mut evtree);
        simplify::propagate_forwards_used_once_tree(&mut evtree);
        simplify::commute_extract_tree(&mut evtree);
        simplify::eval_tree(&mut evtree);

        return Ok(evtree);
    } else {
        Err(())
    }
}

fn print_litmus<W: Write>(
    writer: &mut W,
    format: &str,
    setup: &LitmusSetup<B64>,
    footprints: &HashMap<B64, Footprint>,
    shared_state: &SharedState<B64>,
) {
    let mut bwriter = BufWriter::with_capacity(usize::pow(2, 23), writer);
    if format == "coq" {
        print_coq(&mut bwriter, setup, footprints, shared_state)
        // Coq stuff
    } else if format == "human" {
        // Human readable format
        print_human(&mut bwriter, setup, footprints, shared_state)
    } else {
        eprintln!("Unknown format \"{}\". Supported format are:\n - \"coq\" for Coq datatypes from isla-lang\n - \"human\" for a human readable output", format);
    }
    bwriter.flush().unwrap();
}

fn print_human_memory<W: Write, B: BV>(writer: &mut W, memory: &Memory<B>) {
    write!(writer, "Memory:").unwrap();
    for region in memory.regions() {
        match region {
            Region::Constrained(r, _) => {
                write!(writer, "From {:x} to {:x}: constrained memory\n", r.start, r.end).unwrap()
            }
            Region::Symbolic(r) => write!(writer, "From {:x} to {:x}: symbolic memory\n", r.start, r.end).unwrap(),
            Region::SymbolicCode(r) => {
                write!(writer, "From {:x} to {:x}: symbolic code memory\n", r.start, r.end).unwrap()
            }
            Region::Concrete(r, contents) => {
                write!(writer, "From {:x} to {:x}: concrete memory:\n", r.start, r.end).unwrap();
                // hackish hexdump implementation, feel free to replace with something nicer
                // One can replace 8 by 16 or another block size if needed
                let mut start = r.start;
                let end = r.end;
                let mut last_zero = false;
                let mut last_dots = false;
                while start < end {
                    let all_zero = (0..8).fold(true, |b, i| b && (contents.get(&(start + i)) == None));
                    if all_zero {
                        if last_dots {
                            start = ((start / 8) + 1) * 8;
                            continue;
                        }
                        if last_zero {
                            write!(writer, "  {:16x} :          . . .\n", start / 8 * 8).unwrap();
                            last_dots = true;
                            start = ((start / 8) + 1) * 8;
                            continue;
                        }
                    }
                    let line_end = if start / 8 == end / 8 { end % 8 } else { 8 };
                    write!(writer, "  {:16x} :", start / 8 * 8).unwrap();
                    for _ in 0..(start % 8) {
                        write!(writer, " __").unwrap()
                    }
                    for i in (start % 8)..line_end {
                        write!(writer, " {:02x}", contents.get(&(start + i)).unwrap_or(&0)).unwrap();
                    }
                    write!(writer, "\n").unwrap();
                    start = ((start / 8) + 1) * 8;
                    last_zero = all_zero;
                    last_dots = false;
                }
            }
            Region::Custom(r, _) => write!(writer, "From {:x} to {:x}: custom memory\n", r.start, r.end).unwrap(),
        }
    }
    write!(writer, "\n\n").unwrap();
}

fn print_human<W: Write, B: BV>(
    writer: &mut W,
    setup: &LitmusSetup<B>,
    footprints: &HashMap<B, Footprint>,
    shared_state: &SharedState<B>,
) {
    let write_opts = WriteOpts { define_enum: false, hide_uninteresting: true, ..WriteOpts::default() };
    for (tid, thread) in setup.threads.iter().enumerate() {
        let evtree = get_simplified_evtree(thread).unwrap_or_else(|()| {
            eprintln!("Some thread didn't have a trace");
            process::exit(1)
        });
        write!(writer, "Thread {}:\n", tid).unwrap();
        simplify::write_event_tree(writer, &evtree, shared_state, &write_opts);
        write!(writer, "\n\n\n").unwrap();
    }
    write!(writer, "Final Assertion:\n{:?}\n\n\n", setup.final_assertion).unwrap();

    print_human_memory(writer, &setup.memory);

    for (opcode, footprint) in footprints {
        write!(writer, "opcode {:08x}, ", opcode).unwrap();
        footprint.pretty(writer, &shared_state.symtab).unwrap();
        write!(writer, "\n").unwrap();
    }
}

fn print_coq<W: Write>(
    writer: &mut W,
    setup: &LitmusSetup<B64>,
    footprints: &HashMap<B64, Footprint>,
    shared_state: &SharedState<B64>,
) {
    writeln!(writer, "From isla_lang Require Import lang.").unwrap();
    writeln!(writer, "From isla_lang Require Import traces.").unwrap();
    writeln!(writer, "From isla_lang Require Import litmus.").unwrap();
    writeln!(writer, "From stdpp Require Import strings.").unwrap();
    writeln!(writer, "From stdpp Require Import gmap.").unwrap();
    writeln!(writer).unwrap();

    let arena = pretty::Arena::<()>::new();
    let coqpp = CoqPrettyPrinter::new(&arena, &shared_state.symtab, &shared_state);
    for (tid, thread) in setup.threads.iter().enumerate() {
        let evtree = get_simplified_evtree(thread).unwrap_or_else(|()| {
            eprintln!("Some thread didn't have a trace");
            process::exit(1)
        });
        coqpp.definition(format!("thread{}", tid), &evtree).render(120, writer).unwrap();
    }

    let threads = coqpp.list((0..setup.threads.len()).map(|tid| arena.text(format!("thread{}", tid))));

    coqpp.definition("threads", threads).render(120, writer).unwrap();
    writeln!(writer).unwrap();

    // writeln!(writer, "Import Litmus.").unwrap();
    writeln!(writer, "Section Assert.").unwrap();
    writeln!(writer, "Import Litmus.Assert.").unwrap();
    coqpp.definition("final_assert", &setup.final_assertion).render(120, writer).unwrap();
    writeln!(writer, "End Assert.\n\n").unwrap();

    writeln!(writer, "Section Memory.").unwrap();
    writeln!(writer, "Import Litmus.Memory.").unwrap();
    coqpp.definition("memory", &setup.memory).render(120, writer).unwrap();
    writeln!(writer, "End Memory.\n\n").unwrap();

    writeln!(writer, "Section Footprint.").unwrap();
    writeln!(writer, "Import Litmus.Footprint.").unwrap();
    for (opcode, fp) in footprints {
        coqpp.definition(format!("ftprt{:x}", opcode), fp).render(120, writer).unwrap();
    }

    coqpp
        .definition(
            "footprints",
            coqpp.intmap(footprints.iter().map(|(opcode, _)| (opcode, coqpp.text(format!("ftprt{:x}", opcode)))), 64),
        )
        .render(120, writer)
        .unwrap();
    writeln!(writer, "End Footprint.\n\n").unwrap();
}

/// A Coq pretty printer is a fat point that adds a symbol table to pretty document allocator
struct CoqPrettyPrinter<'a, D>
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    alloc: &'a D,
    symtab: &'a Symtab<'a>,
    shared_state: &'a SharedState<'a, B64>,
}

impl<'a, D: ?Sized + DocAllocator<'a, ()>> Clone for CoqPrettyPrinter<'a, D> {
    fn clone(self: &CoqPrettyPrinter<'a, D>) -> CoqPrettyPrinter<'a, D> {
        CoqPrettyPrinter { alloc: self.alloc, symtab: self.symtab, shared_state: self.shared_state }
    }
}
impl<'a, D: ?Sized + DocAllocator<'a, ()>> Copy for CoqPrettyPrinter<'a, D> {}

trait PrettyCoq<'a, D>
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()>;

    #[inline]
    fn prettyp(self, coqpp: CoqPrettyPrinter<'a, D>) -> DocBuilder<'a, D, ()>
    where
        Self: Sized,
    {
        self.pretty_coq(coqpp, true)
    }

    #[inline]
    fn prettynp(self, coqpp: CoqPrettyPrinter<'a, D>) -> DocBuilder<'a, D, ()>
    where
        Self: Sized,
    {
        self.pretty_coq(coqpp, false)
    }
}

macro_rules! pretty_coq_ref {
    ($typ : ty) => {
        impl<'a, 'b, D> PrettyCoq<'a, D> for &'b $typ
        where
            D: ?Sized + DocAllocator<'a, ()>,
        {
            #[inline]
            fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
                (*self).pretty_coq(coqpp, parens)
            }
        }
    };
}

impl<'a, D: ?Sized + DocAllocator<'a, ()>> PrettyCoq<'a, D> for DocBuilder<'a, D, ()> {
    fn pretty_coq(self, _coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        if parens {
            self.parens()
        } else {
            self
        }
    }
}

impl<'a, D> CoqPrettyPrinter<'a, D>
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn new(alloc: &'a D, symtab: &'a Symtab<'a>, shared_state: &'a SharedState<'a, B64>) -> CoqPrettyPrinter<'a, D> {
        CoqPrettyPrinter { alloc, symtab, shared_state }
    }

    fn text<U: Into<Cow<'a, str>>>(self, data: U) -> DocBuilder<'a, D, ()> {
        self.alloc.text(data)
    }

    fn as_string<T: Display>(self, t: T) -> DocBuilder<'a, D, ()> {
        self.alloc.as_string(t)
    }

    fn listn<I>(self, elems: I, nest: isize) -> DocBuilder<'a, D, ()>
    where
        D: Sized,
        D::Doc: Clone,
        I: IntoIterator,
        I::Item: PrettyCoq<'a, D>,
    {
        docs![
            self.alloc,
            Line_,
            self.alloc.intersperse(elems.into_iter().map(|e| e.prettynp(self)), docs![self.alloc, ";", Line]),
        ]
        .nest(nest)
        .append(Line_)
        .brackets()
        .group()
    }

    fn list<I>(self, elems: I) -> DocBuilder<'a, D, ()>
    where
        D: Sized,
        D::Doc: Clone,
        I: IntoIterator,
        I::Item: PrettyCoq<'a, D>,
    {
        self.listn(elems, 2)
    }

    fn bits<I: Into<i128>>(self, val: I, len: u32) -> DocBuilder<'a, D, ()> {
        self.text(format!("BV {} {:#x}", len, val.into()))
    }

    fn bools(self, b: &[bool]) -> DocBuilder<'a, D, ()> {
        assert!(b.len() <= 128);
        let mut ret: i128 = 0;
        for i in 0..b.len() {
            if b[i] {
                ret += 1 << i;
            }
        }
        self.bits(ret, b.len() as u32)
    }

    fn print_n<N: Display>(self, n: N) -> DocBuilder<'a, D, ()> {
        self.as_string(n)
    }

    fn print_field<N: Display, T: PrettyCoq<'a, D>>(self, name: N, value: T) -> DocBuilder<'a, D, ()> {
        docs![self.alloc, self.as_string(name), " :=", Line, value.prettynp(self), ";"].nest(2).group()
    }

    // Integer map as function from bitvector for now
    fn intmap<I, K, V>(self, elems: I, size: u64) -> DocBuilder<'a, D, ()>
    where
        D: Sized,
        I: IntoIterator<Item = (K, V)>,
        K: std::fmt::LowerHex,
        V: PrettyCoq<'a, D>,
    {
        docs![
            self.alloc,
            "fun b : bv ",
            self.print_n(size),
            " =>",
            HardLine,
            "match b with",
            HardLine,
            self.alloc.intersperse(
                elems.into_iter().map(|(addr, val)| docs![
                    self.alloc,
                    format!("| BV _ 0x{:x} => Some ", addr),
                    val.prettyp(self)
                ]),
                HardLine
            ),
            HardLine,
            "| _ => None",
            HardLine,
            "end"
        ]
        .nest(2)
        .group()
    }

    fn definition<N, T>(self, name: N, body: T) -> DocBuilder<'a, D, ()>
    where
        N: Into<Cow<'a, str>>,
        T: PrettyCoq<'a, D>,
    {
        docs![self.alloc, "Definition ", self.text(name), " :=", Line, body.prettynp(self).group(), "."]
            .nest(2)
            .group()
            .append(HardLine)
            .append(HardLine)
    }

    fn pair<F, S>(self, fst: F, snd: S) -> DocBuilder<'a, D, ()>
    where
        F: PrettyCoq<'a, D>,
        S: PrettyCoq<'a, D>,
    {
        docs![self.alloc, "(", fst.prettynp(self), ",", Line, snd.prettynp(self), ")"].nest(2).group()
    }
}

#[derive(Copy, Clone)]
struct Line;
impl<'a, D, A> Pretty<'a, D, A> for Line
where
    A: 'a,
    D: ?Sized + DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.line()
    }
}

#[derive(Copy, Clone)]
struct Line_;
impl<'a, D, A> Pretty<'a, D, A> for Line_
where
    A: 'a,
    D: ?Sized + DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.line_()
    }
}

#[derive(Copy, Clone)]
struct HardLine;
impl<'a, D, A> Pretty<'a, D, A> for HardLine
where
    A: 'a,
    D: ?Sized + DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.hardline()
    }
}

// fn pretty_coq_definition<'a, D, A, N, T>(alloc: &'a D, name: N, term: T) -> DocBuilder<'a, D, A>
// where
//     D: DocAllocator<'a, A>,
//     D::Doc: Clone,
//     A: Clone,
//     N: Into<Cow<'a, str>>,
//     T: Pretty<'a, D, A>,
// {
//     pretty_coq_func_def(alloc, name, iter::empty::<Line>(), term)
// }

// fn pretty_coq_func_def<'a, D, A, N, B, T>(alloc: &'a D, name: N, binders: B, term: T) -> DocBuilder<'a, D, A>
// where
//     D: DocAllocator<'a, A>,
//     D::Doc: Clone,
//     A: Clone,
//     N: Into<Cow<'a, str>>,
//     B: IntoIterator,
//     B::Item: Pretty<'a, D, A>,
//     T: Pretty<'a, D, A>,
// {
//     let binders =
//         docs![alloc, Line, alloc.concat(binders.into_iter().map(|e| docs![alloc, e, Line])), ":="].nest(2).group();
//     let body = docs![alloc, binders, Line, term, "."].nest(2).group();
//     docs![alloc, "Definition ", alloc.text(name), body, HardLine, HardLine, HardLine]
// }

macro_rules! record {
    ($coqpp: expr $(, $names:expr, $elems: expr)* $(,)?) => {{
        docs![$coqpp.alloc, "{|", $(Line, $coqpp.print_field($names, $elems),)*]
            .nest(2).append(Line).append("|}").group()
    }}
}

fn pretty_coq_parens<'a, D, A, T>(alloc: &'a D, elem: T, enable: bool) -> DocBuilder<'a, D, A>
where
    A: 'a,
    D: ?Sized + DocAllocator<'a, A>,
    T: Pretty<'a, D, A>,
{
    if enable {
        elem.pretty(alloc).parens().nest(2).group()
    } else {
        elem.pretty(alloc).nest(2).group()
    }
}

macro_rules! parens {
    ($alloc: expr, $enable : expr, $first: expr $(, $rest: expr)* $(,)?) => {{
        pretty_coq_parens($alloc, docs![$alloc, $first $(, $rest)*], $enable)
    }}
}

impl<'a, 'b, D> PrettyCoq<'a, D> for Sym
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        coqpp.as_string(self)
    }
}
pretty_coq_ref!(Sym);

impl<'a, 'b, D> PrettyCoq<'a, D> for EnumId
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        self.to_name().prettyp(coqpp)
    }
}
pretty_coq_ref!(EnumId);

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Ty
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        use Ty::*;
        match self {
            Bool => coqpp.text("Ty_Bool"),
            BitVec(size) => {
                parens![coqpp.alloc, parens, "Ty_BitVec ", coqpp.print_n(size)]
            }
            Enum(e) => {
                parens![coqpp.alloc, parens, "Ty_Enum ", e.prettyp(coqpp)]
            }
            Array(ty1, ty2) => {
                parens![coqpp.alloc, parens, "Ty_Array", Line, ty1.prettyp(coqpp), Line, ty2.prettyp(coqpp)]
            }
            _ => coqpp.text("\"Unsupported type\""),
        }
    }
}

impl<'a, D> PrettyCoq<'a, D> for B64
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        parens![coqpp.alloc, parens, coqpp.bits(self.lower_u64(), self.len())]
    }
}
pretty_coq_ref!(B64);

impl<'a, D> PrettyCoq<'a, D> for bool
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        if self {
            coqpp.text("true")
        } else {
            coqpp.text("false")
        }
    }
}
pretty_coq_ref!(bool);

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b EnumMember
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        let members =
            coqpp.shared_state.type_info.enums.get(&self.enum_id.to_name()).expect("Failed to get enumeration");
        members[self.member].prettyp(coqpp)
    }
}

macro_rules! binop {
    ($coqpp: expr, $parens : expr, $op: expr, $e1 : expr, $e2 : expr) => {{
        parens![
            $coqpp.alloc,
            $parens,
            "Binop ",
            $op,
            Line,
            $e1.prettyp($coqpp),
            Line,
            $e2.prettyp($coqpp),
            Line,
            "Mk_annot"
        ]
    }};
}

macro_rules! unop {
    ($coqpp: expr, $parens : expr, $op: expr, $e : expr) => {{
        parens![$coqpp.alloc, $parens, "Unop ", $op, Line, $e.prettyp($coqpp), Line, "Mk_annot"]
    }};
}

macro_rules! manyop {
    ($coqpp: expr, $parens : expr, $op: expr, $e1 : expr, $e2 : expr) => {{
        parens![
            $coqpp.alloc,
            $parens,
            "Manyop ",
            $op,
            " ",
            $coqpp.listn([$e1.prettynp($coqpp), $e2.prettynp($coqpp)], 0),
            " Mk_annot"
        ]
    }};
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Exp<Sym>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        use Exp::*;
        match self {
            Var(v) => parens![coqpp.alloc, parens, "EVal_Sym ", v.prettyp(coqpp)],
            Bits(vb) => parens![coqpp.alloc, parens, "EVal_Bits (", coqpp.bools(&vb), ")"],
            Bits64(b) => parens![coqpp.alloc, parens, "EVal_Bits ", b.prettyp(coqpp)],
            Enum(e) => parens![coqpp.alloc, parens, "EVal_Enum ", e.prettyp(coqpp)],
            Bool(b) => parens![coqpp.alloc, parens, "EVal_Bool ", b.prettyp(coqpp)],
            Eq(e1, e2) => binop!(coqpp, parens, "Eq", e1, e2),
            Neq(e1, e2) => {
                // TODO maybe support neq in isla_lang
                parens![coqpp.alloc, parens, "Unop Not", Line, binop!(coqpp, parens, "Eq", e1, e2), Line, "Mk_annot"]
            }
            And(e1, e2) => manyop!(coqpp, parens, "And", e1, e2),
            Or(e1, e2) => manyop!(coqpp, parens, "Or", e1, e2),
            Not(e) => unop!(coqpp, parens, "Not", e),
            Bvnot(e) => unop!(coqpp, parens, "Bvnot", e),
            Bvand(e1, e2) => manyop!(coqpp, parens, "(Bvmanyarith Bvand)", e1, e2),
            Bvor(e1, e2) => manyop!(coqpp, parens, "(Bvmanyarith Bvor)", e1, e2),
            Bvxor(e1, e2) => manyop!(coqpp, parens, "(Bvmanyarith Bvxor)", e1, e2),
            Bvnand(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvnand)", e1, e2),
            Bvnor(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvnor)", e1, e2),
            Bvxnor(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvxnor)", e1, e2),
            Bvneg(e) => unop!(coqpp, parens, "Bvneg", e),
            Bvadd(e1, e2) => manyop!(coqpp, parens, "(Bvmanyarith Bvadd)", e1, e2),
            Bvsub(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvsub)", e1, e2),
            Bvmul(e1, e2) => manyop!(coqpp, parens, "(Bvmanyarith Bvmul)", e1, e2),
            Bvudiv(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvudiv)", e1, e2),
            Bvsdiv(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvsdiv)", e1, e2),
            Bvurem(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvurem)", e1, e2),
            Bvsrem(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvsrem)", e1, e2),
            Bvsmod(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvsmod)", e1, e2),
            Bvult(e1, e2) => binop!(coqpp, parens, "(Bvcomp Bvult)", e1, e2),
            Bvslt(e1, e2) => binop!(coqpp, parens, "(Bvcomp Bvslt)", e1, e2),
            Bvule(e1, e2) => binop!(coqpp, parens, "(Bvcomp Bvule)", e1, e2),
            Bvsle(e1, e2) => binop!(coqpp, parens, "(Bvcomp Bvsle)", e1, e2),
            Bvuge(e1, e2) => binop!(coqpp, parens, "(Bvcomp Bvuge)", e1, e2),
            Bvsge(e1, e2) => binop!(coqpp, parens, "(Bvcomp Bvsge)", e1, e2),
            Bvugt(e1, e2) => binop!(coqpp, parens, "(Bvcomp Bvugt)", e1, e2),
            Bvsgt(e1, e2) => binop!(coqpp, parens, "(Bvcomp Bvsgt)", e1, e2),
            Extract(a, b, e) => unop!(coqpp, parens, format!("(Extract {} {})", a, b), e),
            ZeroExtend(a, e) => unop!(coqpp, parens, format!("(ZeroExtend {})", a), e),
            SignExtend(a, e) => unop!(coqpp, parens, format!("(SignExtend {})", a), e),
            Bvshl(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvshl)", e1, e2),
            Bvlshr(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvlshr)", e1, e2),
            Bvashr(e1, e2) => binop!(coqpp, parens, "(Bvarith Bvashr)", e1, e2),
            Concat(e1, e2) => manyop!(coqpp, parens, "Concat", e1, e2),
            Ite(cond, e1, e2) => parens![
                coqpp.alloc,
                parens,
                "Ite",
                Line,
                cond.prettyp(coqpp),
                Line,
                e1.prettyp(coqpp),
                Line,
                e2.prettyp(coqpp)
            ],
            _ => coqpp.text("\"Unsupported expression\""),
        }
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Def
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        use Def::*;
        match self {
            DeclareConst(v, ty) => {
                parens![coqpp.alloc, parens, "DeclareConst ", v.prettyp(coqpp), Line, ty.prettyp(coqpp)]
            }
            DefineConst(v, exp) => {
                parens![coqpp.alloc, parens, "DefineConst ", v.prettyp(coqpp), Line, exp.prettyp(coqpp)]
            }
            Assert(exp) => parens![coqpp.alloc, parens, "Assert", Line, exp.prettyp(coqpp)],
            DefineEnum(name, size) => {
                let members = coqpp.shared_state.type_info.enums.get(name).expect("Failed to get enumeration");
                parens![
                    coqpp.alloc,
                    parens,
                    "DefineEnum ",
                    name.prettyp(coqpp),
                    Line,
                    size.to_string(),
                    Line,
                    coqpp.list(members.iter()),
                ]
            }
            _ => coqpp.text("\"Unsupported definition\""),
        }
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Val<B64>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        use Val::*;
        match self {
            Symbolic(sym) => {
                parens![coqpp.alloc, parens, "RVal_Symbolic ", sym.prettyp(coqpp)]
            }
            Bits(b) => parens![coqpp.alloc, parens, "RVal_Bits ", b.prettyp(coqpp)],
            I64(i) => {
                parens![coqpp.alloc, parens, "RVal_Bits ", coqpp.bits(*i, 64).parens()]
            }
            I128(i) => parens![coqpp.alloc, parens, "RVal_Bits ", coqpp.bits(*i, 128).parens()],
            Bool(b) => parens![coqpp.alloc, parens, "RVal_Bool ", b.prettyp(coqpp)],
            Enum(e) => parens![coqpp.alloc, parens, "RVal_Enum ", e.prettyp(coqpp)],
            MixedBits(_) => coqpp.text("\"Unsupported mixed bits register value\""),
            String(s) => parens![coqpp.alloc, parens, "RegVal_String \"", s.clone(), "\")"],
            Unit => coqpp.text("RegVal_Unit"),
            Vector(v) => parens![coqpp.alloc, parens, "RegVal_Vector", Line, coqpp.list(v)],
            List(v) => parens![coqpp.alloc, parens, "RegVal_List", Line, coqpp.list(v), ")"],
            Struct(h) => parens![
                coqpp.alloc,
                parens,
                "RegVal_Struct ",
                coqpp.list(h.iter().map(|(name, val)| coqpp.pair(name, val)))
            ],
            Ctor(name, v) => {
                parens![coqpp.alloc, parens, "RegVal_Constructor ", name.prettyp(coqpp), Line, v.prettyp(coqpp)]
            }
            Poison => coqpp.text("RegVal_Poison"),
            _ => coqpp.text("\"Unsupported register value\""),
        }
    }
}

impl<'a, D> PrettyCoq<'a, D> for Name
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        docs![coqpp.alloc, "\"", zencode::decode(coqpp.symtab.to_str(self)), "\""]
    }
}
pretty_coq_ref!(Name);

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Accessor
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        use Accessor::*;
        match self {
            Field(name) => parens![coqpp.alloc, parens, "Field ", name.prettyp(coqpp)],
        }
    }
}

impl<'a, 'b, D, T> PrettyCoq<'a, D> for &'b Option<T>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
    &'b T: PrettyCoq<'a, D>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        match self {
            Some(t) => parens![coqpp.alloc, parens, "Some", Line, t.prettyp(coqpp)],
            None => coqpp.text("None"),
        }
    }
}

macro_rules! regevent {
    ($coqpp: expr, $parens : expr, $name : expr, $n: expr, $acc : expr, $val : expr) => {{
        parens![
            $coqpp.alloc,
            $parens,
            $name,
            Line,
            $n.prettyp($coqpp),
            Line,
            $coqpp.list($acc),
            Line,
            $val.prettyp($coqpp),
            Line,
            "Mk_annot"
        ]
    }};
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Event<B64>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        use Event::*;
        match self {
            Smt(def, _, _) => parens![coqpp.alloc, parens, "Smt", Line, def.prettyp(coqpp), Line, "Mk_annot"],
            ReadReg(n, acc, val) => regevent!(coqpp, parens, "ReadReg", n, acc, val),
            WriteReg(n, acc, val) => regevent!(coqpp, parens, "WriteReg", n, acc, val),
            AssumeReg(n, acc, val) => regevent!(coqpp, parens, "AssumeReg", n, acc, val),
            ReadMem { value, read_kind, address, bytes, tag_value, opts: _, region: _ } => parens![
                coqpp.alloc,
                parens,
                "ReadMem",
                Line,
                value.prettyp(coqpp),
                Line,
                read_kind.prettyp(coqpp),
                Line,
                address.prettyp(coqpp),
                Line,
                coqpp.print_n(bytes),
                Line,
                tag_value.prettyp(coqpp),
                Line,
                "Mk_annot"
            ],
            WriteMem { value, write_kind, address, data, bytes, tag_value, opts: _, region: _ } => parens![
                coqpp.alloc,
                parens,
                "WriteMem",
                Line,
                Val::Symbolic(*value).prettyp(coqpp),
                Line,
                write_kind.prettyp(coqpp),
                Line,
                address.prettyp(coqpp),
                Line,
                data.prettyp(coqpp),
                Line,
                coqpp.print_n(bytes),
                Line,
                tag_value.prettyp(coqpp),
                Line,
                "Mk_annot"
            ],
            Cycle => parens![coqpp.alloc, parens, "Cycle Mk_annot"],
            Branch { address } => {
                parens![coqpp.alloc, parens, "BranchAddress", Line, address.prettyp(coqpp), Line, "Mk_annot"]
            }
            Instr(opcode) => parens![coqpp.alloc, parens, "Instr", Line, opcode.prettyp(coqpp), Line, "Mk_annot"],
            Function { name, call } => {
                if *call {
                    parens![coqpp.alloc, parens, "Call", Line, name.prettyp(coqpp), Line, "Mk_annot"]
                } else {
                    parens![coqpp.alloc, parens, "Return", Line, name.prettyp(coqpp), Line, "Mk_annot"]
                }
            }
            Abstract { name, primitive, args, return_value } => parens![
                coqpp.alloc,
                parens,
                if *primitive { "AbstractPrimop" } else { "AbstractCall" },
                Line,
                name.prettyp(coqpp),
                Line,
                return_value.prettyp(coqpp),
                Line,
                coqpp.list(args),
                Line,
                "Mk_annot"
            ],
            _ => coqpp.text("\"Unsupported event \""),
        }
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b EventTree<B64>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        let doc = coqpp
            .alloc
            .intersperse(self.prefix.iter().map(|ev| ev.prettynp(coqpp)), docs![coqpp.alloc, " :t:", HardLine]);
        let doc = docs![coqpp.alloc, doc, " :t:", HardLine];
        if self.forks.is_empty() {
            doc.append(coqpp.text("tnil"))
        } else {
            doc.append(docs![coqpp.alloc, "tcases", Line, coqpp.list(&self.forks)].nest(1))
        }
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b exp::Loc<u64>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        use exp::Loc::*;
        match self {
            Register { reg, thread_id } => {
                parens![coqpp.alloc, parens, "Register ", reg.prettyp(coqpp), " ", coqpp.print_n(thread_id)]
            }
            LastWriteTo { address, bytes } => {
                parens![coqpp.alloc, parens, "LastWriteTo ", address.prettyp(coqpp), " ", coqpp.print_n(bytes)]
            }
        }
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b exp::Exp<u64>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        use exp::Exp::*;
        match self {
            EqLoc(loc, exp) => {
                parens![coqpp.alloc, parens, "EqLoc", Line, loc.prettyp(coqpp), Line, exp.prettyp(coqpp)]
            }
            Loc(addr) => parens![coqpp.alloc, parens, "Loc ", addr.prettyp(coqpp)],
            Label(s) => parens![coqpp.alloc, parens, "Label \"", coqpp.as_string(s), "\""],
            True => parens![coqpp.alloc, parens, "Bool true"],
            False => parens![coqpp.alloc, parens, "Bool false"],
            Bin(_) => coqpp.text("\"Unsupported Bin in final assertion expression\""),
            Hex(_) => coqpp.text("\"Unsupported Hex in final assertion expression\""),
            Bits64(val, len) => parens![coqpp.alloc, parens, "Bits (", coqpp.bits(*val, *len), ")"],
            Nat(n) => parens![coqpp.alloc, parens, "Nat ", coqpp.print_n(n)],
            And(exps) => parens![coqpp.alloc, parens, "And ", coqpp.list(exps)],
            Or(exps) => parens![coqpp.alloc, parens, "Or ", coqpp.list(exps)],
            Not(exp) => parens![coqpp.alloc, parens, "Not", Line, exp.prettyp(coqpp)],
            Implies(exp1, exp2) => {
                parens![coqpp.alloc, parens, "Imp", Line, exp1.prettyp(coqpp), Line, exp2.prettyp(coqpp)]
            }
            _ => coqpp.text("\"Unsupported final assertion expression\""),
        }
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for u8
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        parens![coqpp.alloc, parens, coqpp.bits(self, 8),]
    }
}
pretty_coq_ref!(u8);

impl<'a, 'b, D> PrettyCoq<'a, D> for u64
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        parens![coqpp.alloc, parens, coqpp.bits(self, 64),]
    }
}
pretty_coq_ref!(u64);

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Range<Address>
where
    D: ?Sized + DocAllocator<'a, ()>,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        parens![coqpp.alloc, parens, "mrng", Line, self.start.prettyp(coqpp), Line, self.end.prettyp(coqpp),]
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Region<B64>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, parens: bool) -> DocBuilder<'a, D, ()> {
        match self {
            Region::Constrained(range, _) => parens![coqpp.alloc, parens, "Constrained", Line, range.prettyp(coqpp)],
            Region::Symbolic(range) => parens![coqpp.alloc, parens, "Symbolic", Line, range.prettyp(coqpp)],
            Region::SymbolicCode(range) => parens![coqpp.alloc, parens, "SymbolicCode", Line, range.prettyp(coqpp)],
            Region::Concrete(range, contents) => {
                parens![
                    coqpp.alloc,
                    parens,
                    "Concrete",
                    Line,
                    range.prettyp(coqpp),
                    Line,
                    coqpp.intmap(contents, 64).prettyp(coqpp)
                ]
            }
            Region::Custom(range, _) => parens![coqpp.alloc, parens, "Custom", Line, range.prettyp(coqpp)],
        }
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Memory<B64>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        coqpp.list(self.regions())
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b [Accessor]
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        coqpp.list(self)
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b (Name, Vec<Accessor>)
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        let (reg, fields) = self;
        record![coqpp, "register", *reg, "fields", fields.as_slice()]
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b HashSet<(Name, Vec<Accessor>)>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        coqpp.list(self.iter())
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Taints
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        let Taints { registers, memory } = self;
        record![coqpp, "regs", registers, "mem", *memory]
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b (Option<Name>, Name)
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        coqpp.pair(&self.0, self.1)
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b HashSet<(Option<Name>, Name)>
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        coqpp.list(self.iter())
    }
}

impl<'a, 'b, D> PrettyCoq<'a, D> for &'b Footprint
where
    D: DocAllocator<'a, ()>,
    D::Doc: Clone,
{
    fn pretty_coq(self, coqpp: CoqPrettyPrinter<'a, D>, _parens: bool) -> DocBuilder<'a, D, ()> {
        record![
            coqpp,
            "writes_data",
            &self.write_data_taints,
            "memory_address",
            &self.mem_addr_taints,
            "branch_dep",
            &self.branch_addr_taints,
            "register_reads",
            &self.register_reads,
            "register_writes",
            &self.register_writes,
            "register_writes_tainted",
            &self.register_writes_tainted,
            "register_write_ignored",
            &self.register_writes_ignored,
            "is_store",
            self.is_store,
            "is_load",
            self.is_load,
            "is_branch",
            self.is_branch,
            "is_exclusive",
            self.is_exclusive,
        ]
    }
}
