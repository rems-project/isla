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

use crossbeam::queue::SegQueue;
use sha2::{Digest, Sha256};

use std::collections::HashMap;
use std::collections::HashSet;
use std::error::Error;
use std::ffi::OsStr;
use std::fmt;
use std::fs::{self, File};
use std::io::{prelude::*, BufReader, Lines};
use std::path::{Path, PathBuf};
use std::process::{self, exit, Command};
use std::thread;
use std::time::Instant;

use isla_axiomatic::graph::{
    draw_graph_ascii, draw_graph_gv, graph_from_unsat, graph_from_z3_output, Graph, GraphMode, GraphOpts,
    GraphValueNames,
};

use isla_axiomatic::axiomatic::{final_state_from_z3_output, FinalLocValuesError};
use isla_axiomatic::litmus::exp::{collect_locs, Loc as LitmusLoc};
use isla_axiomatic::litmus::Litmus;
use isla_axiomatic::page_table::{name_initial_walk_bitvectors, VirtualAddress};
use isla_axiomatic::run_litmus;
use isla_axiomatic::run_litmus::{LitmusRunOpts, PCLimitMode};
use isla_lib::bitvector::{b129::B129, BV};
use isla_lib::config::ISAConfig;
use isla_lib::error::IslaError;
use isla_lib::init::{initialize_architecture, InitArchWithConfig};
use isla_lib::ir::*;
use isla_lib::log;
use isla_mml::memory_model;
use isla_mml::smt::{compile_memory_model, SexpArena};

mod opts;
use opts::CommonOpts;

use std::sync::atomic::{AtomicBool, Ordering};

static FAILURE: AtomicBool = AtomicBool::new(false);

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    process::exit(code)
}

type FinalState = HashMap<LitmusLoc<String>, Val<B129>>;

#[derive(Debug)]
enum AxResult {
    /// Allowed(final_state, Option<Candidate graph>)
    Allowed(Option<FinalState>, Option<Box<Graph>>),
    Forbidden(Option<FinalState>, Option<Box<Graph>>),
    Error(Option<Box<Graph>>, String),
}

impl AxResult {
    fn short_name(&self) -> &'static str {
        use AxResult::*;
        match self {
            Allowed(_, _) => "allowed",
            Forbidden(_, _) => "forbidden",
            Error(_, _) => "error",
        }
    }

    fn is_allowed(&self) -> bool {
        matches!(self, AxResult::Allowed(_, _))
    }

    fn is_forbidden(&self) -> bool {
        matches!(self, AxResult::Forbidden(_, _))
    }

    fn is_error(&self) -> bool {
        matches!(self, AxResult::Error(_, _))
    }

    fn matches(&self, other: &AxResult) -> bool {
        use AxResult::*;
        match (self, other) {
            (Allowed(_, _), Allowed(_, _)) => true,
            (Forbidden(_, _), Forbidden(_, _)) => true,
            (Error(_, _), Error(_, _)) => true,
            (_, _) => false,
        }
    }

    fn final_state(&self) -> Option<&'_ FinalState> {
        use AxResult::*;
        match self {
            Allowed(s, _) => s.as_ref(),
            Forbidden(s, _) => s.as_ref(),
            Error(_, _) => None,
        }
    }
}

struct GroupIndex<'a, A> {
    i: usize,
    group_id: usize,
    num_groups: usize,
    buf: &'a [A],
}

impl<'a, A> GroupIndex<'a, A> {
    fn new(buf: &'a [A], group_id: usize, num_groups: usize) -> Self {
        GroupIndex { i: 0, group_id, num_groups, buf }
    }
}

impl<'a, A> Iterator for GroupIndex<'a, A> {
    type Item = &'a A;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.buf.get((self.i * self.num_groups) + self.group_id);
        self.i += 1;
        result
    }
}

fn make_cmdline_opts() -> getopts::Options {
    let mut opts = opts::common_opts();

    opts.optflag("", "herd7", "Output in a herd7-compatible way");
    opts.optopt("", "isla-litmus", "Path to isla-litmus binary", "<path>");
    opts.optopt(
        "",
        "litmus-translator",
        "Path to litmus-translator binary (takes precedence over isla-litmus)",
        "<path>",
    );
    opts.optopt("", "footprint-config", "load custom config for footprint analysis", "<file>");
    opts.optmulti("", "variant", "model variants", "<variant>");
    opts.optopt("", "thread-groups", "number threads per group", "<n>");
    opts.optopt("", "only-group", "only perform jobs for one thread group", "<n>");
    opts.optopt("s", "timeout", "Add a timeout (in seconds)", "<n>");
    opts.optopt("", "pc-limit", "Limit the number of times each instruction can be visited", "<n>");
    opts.optopt("", "pc-limit-mode", "What to do when the pc-limit is exceeded (default error)", "<error|discard>");
    opts.optopt("", "memory", "Add a max memory consumption (in megabytes)", "<n>");
    opts.optopt("m", "model", "Memory model in cat format", "<path>");
    opts.optflag("", "ifetch", "Generate ifetch events");
    opts.optflag("", "armv8-page-tables", "Automatically set up ARMv8 page tables");
    opts.optflag("", "merge-translations", "Merge consecutive translate events into a single event");
    opts.optflag("", "merge-split-stages", "Split stages when merging translations");
    opts.optopt("", "remove-uninteresting", "Remove uninteresting translate events", "all/safe");
    opts.optflag("e", "exhaustive", "Attempt to exhaustively enumerate all possible rf combinations");
    opts.optmulti("", "extra-smt", "additional SMT appended to each candidate", "<file>");
    opts.optopt("", "check-sat-using", "Use z3 tactic for checking satisfiablity", "tactic");
    opts.optopt("", "latex", "generate latex version of input files in specified directory", "<path>");
    opts.optopt("", "graph", "Draw graphs of executions", "<ascii|dot|none>");
    add_graph_opts(&mut opts);
    opts.optopt("", "refs", "references to compare output with", "<path>");
    opts.optopt(
        "",
        "cache",
        "A directory to cache intermediate results. The default is TMPDIR if set, otherwise /tmp",
        "<path>",
    );

    opts
}

/// add graph-specific options
fn add_graph_opts(opts: &mut getopts::Options) {
    opts.optopt("", "dot", "Place generated graphviz dot files in specified directory", "<path>");
    opts.optflag("", "temp-dot", "Generate graphviz dot files in TMPDIR or /tmp");

    opts.optflag("", "graph-show-forbidden", "Try draw graph of forbidden executions too");

    opts.optflag("", "graph-debug", "Show everything, all trace events and full information in the nodes");
    opts.optopt("", "graph-shows", "Overwrite showed relations", "<show,show,...>");
    opts.optflag(
        "",
        "graph-human-readable",
        "Try generate human-readable strings instead of bitvectors where possible",
    );
    opts.optopt(
        "",
        "graph-padding",
        "Overwrite default padding",
        "<iw-left=4,threads-down=2,...,(iw|threads|thread|instr|event)-(up|down|left|right)=value,...>",
    );
    opts.optopt("", "graph-force-show-events", "Overwrite hiding of event", "<ev1,ev2,...>");
    opts.optopt("", "graph-force-hide-events", "Overwrite hiding of event", "<ev1,ev2,...>");
    opts.optflag("", "graph-show-all-reads", "Always show read events (including translations and ifetches)");
    opts.optflag(
        "",
        "graph-flatten",
        "Flatten the graph, algining all rows and columns across all threads and instructions",
    );
    opts.optflag(
        "",
        "graph-squash-translation-labels",
        "Squash translation event labels from `T s1:pte3(x)` into `Ts1l3` to save space in diagrams",
    );
    opts.optflag(
        "",
        "view",
        "Open graphviz dot files in default image viewer. Implies --temp-dot unless --dot is set.",
    );

    opts.optflag("", "no-z3-model", "do not generate a graph (DEPRECATED, use --graph=none instead)");
}

fn isla_main() -> i32 {
    use AxResult::*;
    let now = Instant::now();
    let opts = make_cmdline_opts();

    let mut hasher = Sha256::new();
    let (matches, orig_arch) = opts::parse::<B129>(&mut hasher, &opts);

    if !matches.opt_present("model") {
        eprintln!("Required argument 'model' not provided.");
        exit(1);
    }

    let CommonOpts { num_threads, mut arch, symtab, type_info, isa_config, source_path } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &orig_arch);
    let use_model_reg_init = !matches.opt_present("no-model-reg-init");

    // Huge hack, just load an entirely separate copy of the architecture for footprint analysis
    let CommonOpts {
        num_threads: _,
        arch: mut farch,
        symtab: fsymtab,
        type_info: ftype_info,
        isa_config: _,
        source_path: _,
    } = opts::parse_with_arch(&mut hasher, &opts, &matches, &orig_arch);

    let iarch = initialize_architecture(
        &mut arch,
        symtab,
        type_info,
        &isa_config,
        AssertionMode::Optimistic,
        use_model_reg_init,
    );
    let iarch_config = InitArchWithConfig::from_initialized(&iarch, &isa_config);

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

    let fiarch = initialize_architecture(
        &mut farch,
        fsymtab,
        ftype_info,
        footprint_config,
        AssertionMode::Optimistic,
        use_model_reg_init,
    );
    let fiarch_config = InitArchWithConfig::from_initialized(&fiarch, footprint_config);

    let arch_hash = hasher.result();
    log!(log::VERBOSE, &format!("Architecture + config hash: {:x}", arch_hash));
    log!(log::VERBOSE, &format!("Parsing took: {}ms", now.elapsed().as_millis()));

    let use_ifetch = matches.opt_present("ifetch");
    let armv8_page_tables = matches.opt_present("armv8-page-tables");
    let merge_translations =
        if matches.opt_present("merge-translations") { Some(matches.opt_present("merge-split-stages")) } else { None };
    let remove_uninteresting_translates = match matches.opt_str("remove-uninteresting").as_deref() {
        Some("all") => Some(false),
        Some("safe") => Some(true),
        Some(mode) => {
            eprintln!("Invalid option for --remove-uninteresting flag: {}. Must be either 'all' or 'safe'", mode);
            return 1;
        }
        None => None,
    };

    let pc_limit: Option<usize> = match matches.opt_get("pc-limit") {
        Ok(limit) => limit,
        Err(e) => {
            eprintln!("Invalid option for --pc-limit flag. {}", e);
            return 1;
        }
    };
    let pc_limit_mode: PCLimitMode = match matches.opt_str("pc-limit-mode").as_deref() {
        Some("error") | None => PCLimitMode::Error,
        Some("discard") => PCLimitMode::Discard,
        _ => {
            eprintln!("Unknown value for --pc-limit-mode flag. Accepted values are 'error' and 'discard'");
            return 1;
        }
    };

    let graph_flatten = matches.opt_present("graph-flatten");
    let graph_dbg_info = matches.opt_present("graph-debug");
    let graph_human_readable = matches.opt_present("graph-human-readable");
    let graph_shows = matches.opt_str("graph-shows");
    let graph_show_all_reads = matches.opt_present("graph-show-all-reads");
    let graph_squash_translations = matches.opt_present("graph-squash-translation-labels");
    let graph_padding = matches.opt_str("graph-padding");
    let graph_force_show_events = matches.opt_str("graph-force-show-events");
    let graph_force_hide_events = matches.opt_str("graph-force-hide-events");
    let graph_show_forbidden = matches.opt_present("graph-show-forbidden");
    let graph_mode = matches.opt_str("graph");

    let dot_path = match matches.opt_str("dot").map(PathBuf::from) {
        Some(path) => {
            if !path.is_dir() {
                eprintln!("Invalid directory for dot file output");
                return 1;
            }
            Some(path)
        }
        None => {
            if matches.opt_present("temp-dot") || matches.opt_present("view") {
                Some(std::env::temp_dir())
            } else {
                None
            }
        }
    };

    let view = matches.opt_present("view");
    let print_like_herd7 = matches.opt_present("herd7");

    let graph_mode = match graph_mode {
        None => GraphMode::Disabled,
        Some(m) if m == "ascii" => GraphMode::ASCII,
        Some(m) if m == "dot" => GraphMode::Dot,
        Some(m) if m == "none" => GraphMode::Disabled,
        Some(m) => panic!("--graph unknown mode '{}', must be one of {{ascii,dot,none}}", m),
    };

    if graph_mode != GraphMode::Disabled && !dot_path.is_some() {
        panic!("with --graph, must give a --dot path");
    }

    if matches.opt_present("no-z3-model") && graph_mode != GraphMode::Disabled {
        panic!("cannot generate graph with --no-z3-model");
    }

    let get_z3_model = !matches.opt_present("no-z3-model");

    let isla_litmus_path = matches.opt_str("isla-litmus");
    let litmus_translator_path = matches.opt_str("litmus-translator");

    let cache = matches.opt_str("cache").map(PathBuf::from).unwrap_or_else(std::env::temp_dir);
    fs::create_dir_all(&cache).expect("Failed to create cache directory if missing");
    if !cache.is_dir() {
        eprintln!("Invalid cache directory");
        return 1;
    }

    let check_sat_using = matches.opt_str("check-sat-using");

    let latex_path = match matches.opt_str("latex").map(PathBuf::from) {
        Some(path) => {
            if !path.is_dir() {
                eprintln!("Invalid directory for latex file output");
                return 1;
            }
            Some(path)
        }
        None => None,
    };

    let exhaustive = matches.opt_present("exhaustive");

    let timeout: Option<u64> = match matches.opt_get("timeout") {
        Ok(timeout) => timeout,
        Err(e) => {
            eprintln!("Failed to parse --timeout: {}", e);
            return 1;
        }
    };

    let memory: Option<u64> = match matches.opt_get("memory") {
        Ok(memory) => memory,
        Err(e) => {
            eprintln!("Failed to parse --memory: {}", e);
            return 1;
        }
    };

    let refs = if let Some(refs_file) = matches.opt_str("refs") {
        match process_refs(&refs_file) {
            Ok(refs) => refs,
            Err(e) => {
                eprintln!("Error when reading {}:\n{}", refs_file, e);
                return 1;
            }
        }
    } else {
        HashMap::new()
    };

    // Get all the tests from the command line
    let mut tests = Vec::new();
    for path in matches.free.iter().map(PathBuf::from) {
        if path.extension() == Some(OsStr::new("toml")) || path.extension() == Some(OsStr::new("litmus")) {
            tests.push(path)
        } else if let Err(e) = process_at_file(&path, &mut tests) {
            eprintln!("Error when reading list of tests from {}:\n{}", path.display(), e);
            return 1;
        }
    }

    // Load and compile the memory model
    let mm_file = &matches.opt_str("model").unwrap();
    let mut mm_symtab = memory_model::Symtab::new();
    let mut mm_arena = memory_model::ExpArena::new();
    let mm = match memory_model::load_memory_model(mm_file, &mut mm_arena, &mut mm_symtab) {
        Ok(mm) => mm,
        Err(message) => {
            eprintln!("{}", message);
            return 1;
        }
    };
    let mut sexps = SexpArena::new();
    let accessors = match mm.accessors(iarch.shared_state.typedefs(), &mm_arena, &mut sexps, &mut mm_symtab) {
        Ok(accessors) => accessors,
        Err(compile_error) => {
            eprintln!("{}", memory_model::format_error(&compile_error));
            return 1;
        }
    };
    let mut mm_compiled = Vec::new();
    let variants = matches.opt_strs("variant");
    if let Err(compile_error) = compile_memory_model(
        &mm,
        iarch.shared_state.typedefs(),
        &mm_arena,
        &variants,
        &mut sexps,
        &mut mm_symtab,
        &mut mm_compiled,
    ) {
        eprintln!("{}", memory_model::format_error(&compile_error));
        return 1;
    }

    let extra_smt = match matches
        .opt_strs("extra-smt")
        .iter()
        .map(|file| match std::fs::read_to_string(file) {
            Ok(contents) => Ok((file.to_string(), contents)),
            Err(err) => Err(err),
        })
        .collect::<Result<Vec<_>, _>>()
    {
        Ok(extra_smt) => extra_smt,
        Err(msg) => {
            eprintln!("Error reading file for --extra-smt: {}", msg);
            return 1;
        }
    };

    let (threads_per_test, thread_groups) = {
        match matches.opt_get_default("thread-groups", 1) {
            Ok(n) => {
                if num_threads % n == 0 {
                    (num_threads / n, n)
                } else {
                    eprintln!("The number of threads must be divisible by the value of --thread-groups");
                    return 1;
                }
            }
            Err(e) => {
                eprintln!("Could not parse --threads-per-test option: {}", e);
                opts::print_usage(&opts, "", 1)
            }
        }
    };
    let only_group: Option<usize> = matches.opt_get("only-group").unwrap();

    thread::scope(|scope| {
        for group_id in 0..thread_groups {
            if only_group.is_some() && group_id != only_group.unwrap() {
                continue;
            }

            // These ensure that only references are captured by the closure in scope.spawn below
            let tests = &tests;
            let refs = &refs;
            let iarch = &iarch_config;
            let shared_state = &iarch.shared_state;
            let symtab = &shared_state.symtab;
            let type_info = &shared_state.type_info;
            let fiarch = &fiarch_config;
            let isa_config = &isa_config;
            let source_path = &source_path;
            let cache = &cache;
            let dot_path = &dot_path;
            let latex_path = &latex_path;
            let sexps = &sexps;
            let graph_mode = graph_mode;
            let mm_compiled = &mm_compiled;
            let mm_symtab = &mm_symtab;
            let accessors = &accessors;
            let extra_smt = &extra_smt;
            let graph_shows = graph_shows.as_ref();
            let graph_padding = graph_padding.as_ref();
            let graph_force_show_events = graph_force_show_events.as_ref();
            let graph_force_hide_events = graph_force_hide_events.as_ref();
            let check_sat_using = check_sat_using.as_deref();
            let isla_litmus_path = isla_litmus_path.as_ref();
            let litmus_translator_path = litmus_translator_path.as_ref();

            scope.spawn(move || {
                for (i, litmus_file) in GroupIndex::new(tests, group_id, thread_groups).enumerate() {
                    let litmus = if litmus_file.extension() == Some(OsStr::new("litmus")) {
                        // first try Ben Stokes' `litmus-translator` tool
                        let mut translator_path =
                            litmus_translator_path.cloned().unwrap_or_else(|| "litmus-translator".to_string());

                        let mut opt_args = Vec::new();
                        if armv8_page_tables {
                            opt_args.push("-variant");
                            opt_args.push("VMSA");
                        }

                        let mut poutput = Command::new(&translator_path).args(&opt_args).arg(litmus_file).output();

                        // if that fails, fall back to isla-litmus
                        if let Err(e) = poutput {
                            log!(
                                log::LITMUS,
                                &format!("failed to invoke {}: {}, trying isla-litmus instead...", &translator_path, e)
                            );

                            translator_path = isla_litmus_path.cloned().unwrap_or_else(|| "isla-litmus".to_string());

                            opt_args.clear();
                            if armv8_page_tables {
                                opt_args.push("--armv8-page-tables")
                            };

                            poutput = Command::new(&translator_path).args(&opt_args).arg(litmus_file).output()
                        }

                        // if still an error, report to user as a hard failure
                        let output = {
                            match poutput {
                                Err(e) => panic!(
                                    "could not find litmus-translator or isla-litmus to convert .litmus file: {}",
                                    e
                                ),
                                Ok(o) => o,
                            }
                        };

                        if output.status.success() {
                            let translated_litmus_src = String::from_utf8_lossy(&output.stdout).to_string();
                            log!(log::LITMUS, &format!("translated litmus =\n{}", &translated_litmus_src));
                            translated_litmus_src
                        } else {
                            eprintln!(
                                "Failed to translate litmus file (using {}): {}\n{}",
                                &translator_path,
                                litmus_file.display(),
                                String::from_utf8_lossy(&output.stderr)
                            );
                            continue;
                        }
                    } else {
                        match fs::read_to_string(litmus_file) {
                            Ok(litmus) => litmus,
                            Err(msg) => {
                                eprintln!("Failed to read litmus file: {}\n{}", litmus_file.display(), msg);
                                continue;
                            }
                        }
                    };

                    let litmus = match Litmus::parse(&litmus, symtab, type_info, isa_config) {
                        Ok(litmus) => litmus,
                        Err(msg) => {
                            eprintln!("Failed to parse litmus file: {}\n{}", litmus_file.display(), msg);
                            continue;
                        }
                    };

                    if let Some(path) = latex_path {
                        let latex_file_buf = path.join(format!("{}.tex", litmus.name));
                        let latex_file = latex_file_buf.as_path();
                        log!(
                            log::VERBOSE,
                            &format!("generating latex for test {}: {}", litmus.name, litmus.latex_id())
                        );

                        match std::fs::File::create(latex_file) {
                            Ok(mut handle) => litmus.latex(&mut handle, &shared_state.symtab).unwrap(),
                            Err(msg) => eprintln!(
                                "Failed to create litmus test '{}' latex writer file: {}\n{}",
                                litmus.name,
                                latex_file_buf.display(),
                                msg
                            ),
                        }

                        // when writing LaTeX don't run the tests
                        continue;
                    }

                    let now = Instant::now();
                    let result_queue = SegQueue::new();

                    let opts = LitmusRunOpts {
                        num_threads: threads_per_test,
                        timeout,
                        pc_limit,
                        pc_limit_mode,
                        memory,
                        ignore_ifetch: !use_ifetch,
                        exhaustive,
                        armv8_page_tables,
                        merge_translations,
                        remove_uninteresting_translates,
                    };

                    let mut graph_show_regs: HashSet<String> =
                        GraphOpts::DEFAULT_SHOW_REGS.iter().cloned().map(String::from).collect();
                    if opts.armv8_page_tables {
                        graph_show_regs.extend(GraphOpts::ARMV8_ADDR_TRANS_SHOW_REGS.iter().cloned().map(String::from));
                    }

                    let padding: Option<HashMap<String, f64>> = graph_padding.map(|padstr| {
                        padstr
                            .split(',')
                            .map(|padeq| match *padeq.split('=').collect::<Vec<&str>>().as_slice() {
                                [lhs, rhs] => (
                                    lhs.to_string(),
                                    rhs.parse::<f64>().unwrap_or_else(|_| {
                                        panic!("--graph-padding value must be a valid 64-bit float")
                                    }),
                                ),
                                _ => panic!("--graph-padding must be of form name-direction=value"),
                            })
                            .collect()
                    });

                    let graph_opts = GraphOpts {
                        mode: graph_mode,
                        show_regs: graph_show_regs,
                        flatten: graph_flatten,
                        debug: graph_dbg_info,
                        show_all_reads: graph_show_all_reads,
                        shows: graph_shows.map(|s| s.split(',').map(String::from).collect()),
                        padding,
                        human_readable_values: graph_human_readable,
                        force_show_events: graph_force_show_events.map(|s| s.split(',').map(String::from).collect()),
                        force_hide_events: graph_force_hide_events.map(|s| s.split(',').map(String::from).collect()),
                        squash_translation_labels: graph_squash_translations,
                        control_delimit: false,
                    };

                    let final_assertion_locs = {
                        let mut locs: HashSet<&LitmusLoc<String>> = HashSet::new();
                        collect_locs(&litmus.final_assertion, &mut locs);
                        locs
                    };

                    let run_info = run_litmus::smt_output_per_candidate::<B129, _, _, FinalLocValuesError>(
                        &format!("g{}t{}", group_id, i),
                        &opts,
                        &litmus,
                        &graph_opts,
                        iarch,
                        fiarch,
                        sexps,
                        mm_compiled,
                        mm_symtab,
                        accessors,
                        extra_smt,
                        check_sat_using,
                        get_z3_model,
                        cache,
                        &|exec, memory, all_addrs, tables, footprints, z3_output| {
                            let final_state: Option<FinalState> = if get_z3_model {
                                final_state_from_z3_output(&litmus, &exec, &final_assertion_locs, z3_output)
                                    .map(Some)
                                    .unwrap_or_else(|e| {
                                        log!(
                                            log::VERBOSE,
                                            format!("warning: failed to get final state for execution: {}", e)
                                        );
                                        None
                                    })
                            } else {
                                None
                            };

                            let mut names = GraphValueNames {
                                s1_ptable_names: HashMap::new(),
                                s2_ptable_names: HashMap::new(),
                                pa_names: HashMap::new(),
                                ipa_names: HashMap::new(),
                                va_names: HashMap::new(),
                                value_names: HashMap::new(),
                                paddr_names: HashMap::new(),
                            };

                            // collect names from translation-table-walks for each VA
                            for (table_name, (base, kind)) in tables {
                                for (va_name, va) in &litmus.symbolic_addrs {
                                    name_initial_walk_bitvectors(
                                        if kind == &"stage 1" {
                                            &mut names.s1_ptable_names
                                        } else if kind == &"stage 2" {
                                            &mut names.s2_ptable_names
                                        } else {
                                            panic!("unknown table kind (must be stage 1 or stage 2)")
                                        },
                                        va_name,
                                        VirtualAddress::from_u64(*va),
                                        table_name,
                                        *base,
                                        memory,
                                    )
                                }
                            }

                            // collect names for each IPA/PA variable in the pagetable
                            // assuming 4k pages
                            for (name, val) in all_addrs {
                                if name.starts_with("pa") {
                                    names.pa_names.insert(B129::new(*val, 64), name.clone());
                                    names.pa_names.insert(B129::new(*val >> 12, 42), format!("page({})", name));
                                } else if name.starts_with("ipa") {
                                    names.ipa_names.insert(B129::new(*val, 64), name.clone());
                                    names.ipa_names.insert(B129::new(*val >> 12, 42), format!("page({})", name));
                                } else {
                                    names.va_names.insert(B129::new(*val, 64), name.clone());
                                    names.va_names.insert(B129::new(*val >> 12, 42), format!("page({})", name));
                                }
                            }

                            if z3_output.starts_with("sat") {
                                let graph = if graph_mode != GraphMode::Disabled {
                                    match graph_from_z3_output(
                                        &exec,
                                        names,
                                        footprints,
                                        z3_output,
                                        &litmus,
                                        use_ifetch,
                                        &graph_opts,
                                        symtab,
                                    ) {
                                        Ok(graph) => Some(Box::new(graph)),
                                        Err(err) => {
                                            eprintln!("Failed to generate graph: {}", err);
                                            None
                                        }
                                    }
                                } else {
                                    None
                                };
                                result_queue.push(Allowed(final_state, graph));
                            } else if z3_output.starts_with("sat") {
                            } else {
                                let graph = if graph_mode != GraphMode::Disabled && graph_show_forbidden {
                                    match graph_from_unsat(
                                        &exec,
                                        names,
                                        footprints,
                                        &litmus,
                                        use_ifetch,
                                        &graph_opts,
                                        shared_state,
                                    ) {
                                        Ok(graph) => Some(Box::new(graph)),
                                        Err(err) => {
                                            eprintln!("Failed to generate graph: {}", err);
                                            None
                                        }
                                    }
                                } else {
                                    None
                                };

                                if z3_output.starts_with("unsat") {
                                    result_queue.push(Forbidden(final_state, graph));
                                } else {
                                    result_queue.push(Error(graph, z3_output.to_string()));
                                }
                            }
                            Ok(())
                        },
                    );

                    let ref_result = refs.get(&litmus.name);

                    if let Err(err) = run_info {
                        let msg = format!("{}", err);
                        eprintln!(
                            "{}",
                            err.source_loc().message(source_path.as_ref(), symtab.files(), &msg, true, true)
                        );
                        print_results(
                            print_like_herd7,
                            &litmus,
                            shared_state,
                            now,
                            &[Error(None, "".to_string())],
                            ref_result,
                        );
                        continue;
                    }

                    let mut results: Vec<AxResult> = Vec::new();
                    while let Some(result) = result_queue.pop() {
                        results.push(result)
                    }

                    print_results(print_like_herd7, &litmus, shared_state, now, &results, ref_result);

                    for (i, allowed) in results.iter().enumerate() {
                        let (maybe_graph, state) = match allowed {
                            Allowed(_, graph) => (graph, "allow"),
                            Forbidden(_, graph) => (graph, "forbid"),
                            Error(graph, _) => (graph, "err"),
                        };

                        if let Some(graph) = maybe_graph {
                            match graph_opts.mode {
                                GraphMode::Disabled => (),
                                GraphMode::Dot => {
                                    if let Some(dot_path) = dot_path {
                                        let dot_file_buf =
                                            dot_path.join(format!("{}_{}_{}.dot", litmus.name, state, i + 1));
                                        let dot_file = dot_file_buf.as_path();
                                        log!(
                                            log::VERBOSE,
                                            &format!(
                                                "generating dot for execution #{} for {}: path {}",
                                                i + 1,
                                                litmus.name,
                                                dot_file.display()
                                            )
                                        );

                                        match std::fs::File::create(dot_file) {
                                            Ok(mut dotf) => {
                                                match draw_graph_gv(&mut dotf, graph, &graph_opts) {
                                                    Ok(()) => (),
                                                    Err(e) => {
                                                        eprintln!("failed to render graph: {e}");
                                                        continue;
                                                    }
                                                };
                                            }
                                            Err(e) => {
                                                let dp = dot_file.display();
                                                eprintln!("failed to open {dp}: {e}");
                                                continue;
                                            }
                                        }

                                        if view {
                                            Command::new("neato")
                                                .args(["-n", "-Tpng", "-o", &format!("{}_{}.png", litmus.name, i + 1)])
                                                .arg(dot_file)
                                                .output()
                                                .expect("Failed to invoke dot");

                                            Command::new("xdg-open")
                                                .arg(format!("{}_{}.png", litmus.name, i + 1))
                                                .output()
                                                .expect("Failed to invoke xdg-open");
                                        }
                                    }
                                }
                                GraphMode::ASCII => {
                                    // make sure to take the stdout lock and flush stdout (e.g. from printing results) before printing graph
                                    // so that the two don't stomp over each other (e.g. from another thread)
                                    // the Lock<> structs contain a re-entrant mutex, so this is safe.
                                    let mut stdout = std::io::stdout().lock();
                                    let mut stderr = std::io::stderr().lock();
                                    let outcome: Result<(), std::io::Error> = [
                                        stdout.flush(),
                                        writeln!(&mut stderr),
                                        writeln!(&mut stderr, "Candidate {}/{} ({}):", i + 1, results.len(), state),
                                        writeln!(&mut stderr),
                                        draw_graph_ascii(&mut stderr, graph, &graph_opts),
                                    ]
                                    .into_iter()
                                    .collect();
                                    match outcome {
                                        Ok(()) => (),
                                        Err(e) => {
                                            eprintln!("failed to render graph: {e}");
                                            continue;
                                        }
                                    };
                                }
                            }
                        }
                    }
                }
            });
        }
    });

    if FAILURE.load(Ordering::Relaxed) {
        1
    } else {
        0
    }
}

#[allow(unused)]
fn print_results_legacy(name: &str, start_time: Instant, results: &[AxResult], expected: Option<&AxResult>) {
    if results.is_empty() {
        let prefix = format!("{} no executions {}", name, start_time.elapsed().as_millis());
        println!("{:.<100} \x1b[95m\x1b[1merror\x1b[0m", prefix);
        return;
    }

    let got = if let Some(err) = results.iter().find(|result| result.is_error()) {
        err
    } else if let Some(allowed) = results.iter().find(|result| result.is_allowed()) {
        allowed
    } else {
        results.first().unwrap()
    };

    if let AxResult::Error(_, z3_output) = got {
        eprintln!("Error in parsing smt output to get allowed/forbidden ...");
        eprintln!("z3 head: '{}'...", &z3_output[0..std::cmp::min(15, z3_output.len())]);
        let mut seen_error: bool = false;
        for line in z3_output.lines() {
            if line.starts_with("(error ") {
                if !seen_error {
                    eprintln!("z3 errors:");
                    seen_error = true;
                }
                eprintln!("{}", line);
            }
        }
    }

    let count = format!("{} of {}", results.iter().filter(|result| result.is_allowed()).count(), results.len());

    let prefix = if let Some(reference) = expected {
        format!(
            "{} {} ({}) reference: {} {}ms ",
            name,
            got.short_name(),
            count,
            reference.short_name(),
            start_time.elapsed().as_millis()
        )
    } else {
        format!("{} {} ({}) {}ms ", name, got.short_name(), count, start_time.elapsed().as_millis())
    };

    let result = if let Some(reference) = expected {
        if got.matches(reference) {
            "\x1b[92m\x1b[1mok\x1b[0m"
        } else if got.is_error() {
            FAILURE.store(true, Ordering::Relaxed);
            "\x1b[95m\x1b[1merror\x1b[0m"
        } else {
            FAILURE.store(true, Ordering::Relaxed);
            "\x1b[91m\x1b[1mfail\x1b[0m"
        }
    } else {
        "\x1b[93m\x1b[1m?\x1b[0m"
    };

    println!("{:.<100} {}", prefix, result)
}

/// prints out the final set of collected executions in herdtools-compliant style.
fn print_results_herd7<'ir>(
    litmus: &Litmus<B129>,
    shared_state: &SharedState<'ir, B129>,
    start_time: Instant,
    results: &[AxResult],
    expected: Option<&AxResult>,
) {
    let positive = results.iter().filter(|r| r.is_allowed()).count();
    let negative = results.iter().filter(|r| r.is_forbidden()).count();

    // get a witness error/allow/forbid result
    let got_error = results.iter().find(|result| result.is_error());
    let got_allowed = results.iter().find(|result| result.is_allowed());
    let got_forbidden = results.iter().find(|result| result.is_forbidden());

    let state = if got_error.is_some() {
        "Error"
    } else if got_allowed.is_some() {
        // can't know if result is 'Required', even if negative == 0, as we only know *some* rf was allowed, not all.
        // TODO: BS: ... maybe, unless we have --exhaustive ?
        "Allowed"
    } else if got_forbidden.is_some() {
        "Forbidden"
    } else if results.is_empty() {
        "Error"
    } else {
        "Error"
    };

    println!("Test {} {}", litmus.name, state);
    println!("States {}", results.len());

    for r in results {
        match r.final_state() {
            Some(state) => {
                for (r, v) in state {
                    print!("{}={};", r.display(&shared_state.symtab), v.to_string(shared_state));
                }
                println!();
            }
            None => {
                println!("???;");
            }
        }
    }

    let condition = if results.is_empty() {
        println!("Empty");
        "Error"
    } else if results.iter().all(AxResult::is_allowed) {
        println!("Ok");
        "Always"
    } else if results.iter().any(AxResult::is_allowed) {
        println!("Ok");
        "Sometimes"
    } else {
        println!("No");
        "Never"
    };

    println!("Witnesses");
    println!("Positive: {} Negative: {}", positive, negative);
    println!(
        "Condition exists {}",
        litmus.final_assertion.display(&shared_state.symtab, litmus.final_assertion.precedence())
    );
    println!("Observation {} {} {} {}", litmus.name, condition, positive, negative);

    if let Some(hash) = &litmus.hash {
        println!("Hash={}", hash);
    }

    println!("Time {}ms", start_time.elapsed().as_millis());

    let got = got_error.or(got_error).or(got_forbidden).or(got_allowed);

    if let Some(AxResult::Error(_, z3_output)) = got {
        eprintln!("Error in parsing smt output to get allowed/forbidden ...");
        eprintln!("z3 head: '{}'...", &z3_output[0..std::cmp::min(15, z3_output.len())]);
        let mut seen_error: bool = false;
        for line in z3_output.lines() {
            if line.starts_with("(error ") {
                if !seen_error {
                    eprintln!("z3 errors:");
                    seen_error = true;
                }
                eprintln!("{}", line);
            }
        }
    }

    if let Some(reference) = expected {
        println!("Model Reference {} {}", litmus.name, reference.short_name());

        // backwards-compat: print out reference on stderr
        let status = if let Some(got) = got {
            if got.matches(reference) {
                "\x1b[92m\x1b[1mok\x1b[0m"
            } else if got.is_error() {
                FAILURE.store(true, Ordering::Relaxed);
                "\x1b[95m\x1b[1merror\x1b[0m"
            } else {
                FAILURE.store(true, Ordering::Relaxed);
                "\x1b[91m\x1b[1mfail\x1b[0m"
            }
        } else {
            "\x1b[91m\x1b[1merror\x1b[0m"
        };
        let count = format!("{} of {}", positive, results.len());
        let prefix = format!(
            "{} {} ({}) reference: {} {}ms ",
            litmus.name,
            got.map(AxResult::short_name).unwrap_or("error"),
            count,
            reference.short_name(),
            start_time.elapsed().as_millis()
        );
        eprintln!("{:.<100} {}", prefix, status);
    }
}

fn print_results<'ir>(
    herd_style: bool,
    litmus: &Litmus<B129>,
    shared_state: &SharedState<'ir, B129>,
    start_time: Instant,
    results: &[AxResult],
    expected: Option<&AxResult>,
) {
    if herd_style {
        print_results_herd7(litmus, shared_state, start_time, results, expected)
    } else {
        print_results_legacy(&litmus.name, start_time, results, expected)
    }
}

#[derive(Debug)]
pub enum AtLineSourceInfo {
    WithSourceInfo(PathBuf, usize),
    Unknown,
}

impl fmt::Display for AtLineSourceInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AtLineSourceInfo::WithSourceInfo(at_file_name, lineno) => {
                write!(f, "{}:{}", at_file_name.display(), lineno)
            }
            AtLineSourceInfo::Unknown => write!(f, "??:??"),
        }
    }
}

#[derive(Debug)]
pub enum AtLineError {
    IoError(AtLineSourceInfo, std::io::Error),
    MalformedLine(AtLineSourceInfo, String),
    NestedAtFile(Vec<AtLineSourceInfo>, Box<AtLineError>),
}

impl AtLineError {
    fn with_source_info(self, at_file_name: PathBuf, lineno: usize) -> Self {
        match self {
            AtLineError::IoError(AtLineSourceInfo::Unknown, e) => {
                AtLineError::IoError(AtLineSourceInfo::WithSourceInfo(at_file_name, lineno), e)
            }
            AtLineError::MalformedLine(AtLineSourceInfo::Unknown, s) => {
                AtLineError::MalformedLine(AtLineSourceInfo::WithSourceInfo(at_file_name, lineno), s)
            }
            AtLineError::NestedAtFile(mut v, e) => {
                let new_v = {
                    v.push(AtLineSourceInfo::WithSourceInfo(at_file_name, lineno));
                    v
                };
                AtLineError::NestedAtFile(new_v, e)
            }
            _ => panic!("can't attach source info to AtLineError which already has source info"),
        }
    }

    fn nest(self) -> Self {
        match self {
            AtLineError::IoError(_, _) => AtLineError::NestedAtFile(vec![], Box::new(self)),
            AtLineError::MalformedLine(_, _) => AtLineError::NestedAtFile(vec![], Box::new(self)),
            AtLineError::NestedAtFile(_, _) => self,
        }
    }

    fn bad_line(line: &str) -> Self {
        AtLineError::MalformedLine(AtLineSourceInfo::Unknown, line.into())
    }
}

impl fmt::Display for AtLineError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AtLineError::MalformedLine(si, line) => {
                write!(f, "could not parse at-file {}: malformed line: {}", si, line)
            }
            AtLineError::IoError(si, err) => write!(f, "could not parse at-file {}: io error: {}", si, err),
            AtLineError::NestedAtFile(v, e) => {
                let mut r = v.iter().map(|si| format!("in {}", si)).collect::<Vec<String>>();

                r.reverse();
                write!(f, "{}: {}", r.join(", "), e)
            }
        }
    }
}

impl From<std::io::Error> for AtLineError {
    fn from(e: std::io::Error) -> Self {
        AtLineError::IoError(AtLineSourceInfo::Unknown, e)
    }
}

impl Error for AtLineError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

fn process_at_line<P: AsRef<Path>>(root: P, line: &str, tests: &mut Vec<PathBuf>) -> Result<(), AtLineError> {
    let pathbuf = root.as_ref().join(&line);
    let name = pathbuf.file_name().ok_or_else(|| AtLineError::bad_line(line))?.to_string_lossy();
    let fs_extension = pathbuf.extension().map(|s| s.to_string_lossy());
    if name.starts_with('@') {
        process_at_file(&pathbuf, tests).map_err(|e| e.nest())
    } else {
        match fs_extension {
            Some(extension) if extension == "litmus" || extension == "toml" => {
                tests.push(pathbuf);
                Ok(())
            }
            _ if line.is_empty() => Ok(()),
            _ => Err(AtLineError::bad_line(line)),
        }
    }
}

fn process_at_file<P: AsRef<Path>>(path: P, tests: &mut Vec<PathBuf>) -> Result<(), AtLineError> {
    let at_file_path = fs::canonicalize(path)?;
    let fd = File::open(&at_file_path)?;
    let reader = BufReader::new(fd);

    let root = at_file_path.parent().unwrap();
    for (i, line) in reader.lines().enumerate() {
        let line = line?;
        if !line.starts_with('#') && !line.is_empty() {
            process_at_line(&root, &line, tests).map_err(|e| e.with_source_info(at_file_path.clone(), i + 1))?;
        }
    }

    Ok(())
}

#[derive(Debug)]
pub enum RefsError {
    BadTestLine(String),
    BadExpected(String),
    BadStatesLine(String),
    BadResultLine(String),
    UnexpectedEof,
}

impl fmt::Display for RefsError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use RefsError::*;
        match self {
            BadTestLine(line) => write!(f, "Expected test name on line: {}", line),
            BadExpected(text) => write!(f, "Expected `Allowed` or `Forbidden` got: {}", text),
            BadStatesLine(line) => write!(f, "Expected a line containing `States <n>`: {}", line),
            BadResultLine(line) => write!(f, "Expected a line starting with either `Ok or No`: {}", line),
            UnexpectedEof => write!(f, "Unexpected end-of-file"),
        }
    }
}

impl Error for RefsError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

fn parse_states_line(lines: &mut Lines<BufReader<File>>) -> Result<usize, Box<dyn Error>> {
    use RefsError::*;
    if let Some(line) = lines.next() {
        let line = line?;
        if line.starts_with("States") {
            let num_states = line.split_whitespace().nth(1).ok_or_else(|| BadStatesLine(line.to_string()))?;
            Ok(num_states.parse()?)
        } else {
            Err(BadStatesLine(line).into())
        }
    } else {
        Err(UnexpectedEof.into())
    }
}

fn negate_result(result: AxResult) -> AxResult {
    match result {
        AxResult::Allowed(_, _) => AxResult::Forbidden(None, None),
        AxResult::Forbidden(_, _) => AxResult::Allowed(None, None),
        _ => panic!("Result other than allowed or forbidden in negate_result"),
    }
}

fn parse_result_line(lines: &mut Lines<BufReader<File>>, expected: AxResult) -> Result<AxResult, Box<dyn Error>> {
    use RefsError::*;
    if let Some(line) = lines.next() {
        let line = line?;
        if line.starts_with("Ok") {
            Ok(expected)
        } else if line.starts_with("No") {
            Ok(negate_result(expected))
        } else {
            Err(BadResultLine(line).into())
        }
    } else {
        Err(UnexpectedEof.into())
    }
}

fn parse_expected(expected: &str) -> Result<Option<AxResult>, RefsError> {
    if expected == "Allowed" {
        Ok(Some(AxResult::Allowed(None, None)))
    } else if expected == "Forbidden" || expected == "Required" {
        // Required is used when the litmus test has an assertion
        // which must be true for all traces, but we have already
        // re-written forall X into ~(exists(~X)) where ~X must be
        // forbidden.
        Ok(Some(AxResult::Forbidden(None, None)))
    } else if expected == "Error" {
        Ok(None)
    } else {
        Err(RefsError::BadExpected(expected.to_string()))
    }
}

fn process_refs<P: AsRef<Path>>(path: P) -> Result<HashMap<String, AxResult>, Box<dyn Error>> {
    use RefsError::*;
    let mut refs = HashMap::new();

    let fd = File::open(&path)?;
    let reader = BufReader::new(fd);
    let mut lines = reader.lines();

    while let Some(line) = lines.next() {
        let line = line?;
        if line.starts_with("Test") {
            let test = line.split_whitespace().nth(1).ok_or_else(|| BadTestLine(line.to_string()))?;
            if let Some(expected) =
                line.split_whitespace().nth(2).ok_or_else(|| BadTestLine(line.to_string())).and_then(parse_expected)?
            {
                let num_states = parse_states_line(&mut lines)?;
                for _ in 0..num_states {
                    lines.next();
                }
                let result = parse_result_line(&mut lines, expected)?;
                refs.insert(test.to_string(), result);
            }
        }
    }

    Ok(refs)
}
