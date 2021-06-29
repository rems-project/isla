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
use crossbeam::thread;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::error::Error;
use std::ffi::OsStr;
use std::fmt;
use std::fs::{self, File};
use std::io::{prelude::*, BufReader, Lines};
use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::time::Instant;

use isla_axiomatic::cat_config::tcx_from_config;
use isla_axiomatic::graph::{graph_from_z3_output, Graph};
use isla_axiomatic::litmus::Litmus;
use isla_axiomatic::page_table::{name_initial_walk_bitvectors, VirtualAddress};
use isla_axiomatic::run_litmus;
use isla_axiomatic::run_litmus::LitmusRunOpts;
use isla_cat::cat;
use isla_lib::bitvector::b64::B64;
use isla_lib::config::ISAConfig;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::log;

mod opts;
use opts::CommonOpts;

use std::sync::atomic::{AtomicBool, Ordering};

static FAILURE: AtomicBool = AtomicBool::new(false);

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    process::exit(code)
}

#[derive(Debug)]
enum AxResult {
    Allowed(Option<Box<Graph>>),
    Forbidden,
    Error,
}

impl AxResult {
    fn short_name(&self) -> &'static str {
        use AxResult::*;
        match self {
            Allowed(_) => "allowed",
            Forbidden => "forbidden",
            Error => "error",
        }
    }

    fn is_allowed(&self) -> bool {
        matches!(self, AxResult::Allowed(_))
    }

    fn is_error(&self) -> bool {
        matches!(self, AxResult::Error)
    }

    fn matches(&self, other: &AxResult) -> bool {
        use AxResult::*;
        match (self, other) {
            (Allowed(_), Allowed(_)) => true,
            (Forbidden, Forbidden) => true,
            (Error, Error) => true,
            (_, _) => false,
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

#[derive(Debug)]
pub enum ResultError {}

impl fmt::Display for ResultError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ResultError")
    }
}

impl Error for ResultError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

fn isla_main() -> i32 {
    use AxResult::*;
    let now = Instant::now();

    let mut opts = opts::common_opts();
    opts.optopt("t", "test", "A litmus test (.litmus or .toml), or a file containing a list of tests", "<path>");
    opts.optopt("", "footprint-config", "load custom config for footprint analysis", "<file>");
    opts.optopt("", "thread-groups", "number threads per group", "<n>");
    opts.optopt("", "only-group", "only perform jobs for one thread group", "<n>");
    opts.optopt("s", "timeout", "Add a timeout (in seconds)", "<n>");
    opts.reqopt("m", "model", "Memory model in cat format", "<path>");
    opts.optflag("", "ifetch", "Generate ifetch events");
    opts.optflag("", "armv8-page-tables", "Automatically set up ARMv8 page tables");
    opts.optflag("", "merge-translations", "Merge consecutive translate events into a single event");
    opts.optflag("e", "exhaustive", "Attempt to exhaustively enumerate all possible rf combinations");
    opts.optopt("", "check-sat-using", "Use z3 tactic for checking satisfiablity", "tactic");
    opts.optopt("", "dot", "Generate graphviz dot files in specified directory", "<path>");
    opts.optflag("", "temp-dot", "Generate graphviz dot files in TMPDIR or /tmp");
    opts.optflag(
        "",
        "view",
        "Open graphviz dot files in default image viewer. Implies --temp-dot unless --dot is set.",
    );
    opts.optopt("", "refs", "references to compare output with", "<path>");
    opts.optopt(
        "",
        "cache",
        "A directory to cache intermediate results. The default is TMPDIR if set, otherwise /tmp",
        "<path>",
    );

    let mut hasher = Sha256::new();
    let (matches, orig_arch) = opts::parse::<B64>(&mut hasher, &opts);
    let CommonOpts { num_threads, mut arch, symtab, isa_config } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &orig_arch);

    // Huge hack, just load an entirely separate copy of the architecture for footprint analysis
    let CommonOpts { num_threads: _, arch: mut farch, symtab: fsymtab, isa_config: _ } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &orig_arch);

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    let footprint_config = if let Some(file) = matches.opt_str("footprint-config") {
        match ISAConfig::from_file(&mut hasher, file, &fsymtab) {
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

    let Initialized { regs: fregs, lets: flets, shared_state: fshared_state } =
        initialize_architecture(&mut farch, fsymtab, &footprint_config, AssertionMode::Optimistic);

    let arch_hash = hasher.result();
    log!(log::VERBOSE, &format!("Archictecture + config hash: {:x}", arch_hash));
    log!(log::VERBOSE, &format!("Parsing took: {}ms", now.elapsed().as_millis()));

    let use_ifetch = matches.opt_present("ifetch");
    let armv8_page_tables = matches.opt_present("armv8-page-tables");
    let merge_translations = matches.opt_present("merge-translations");

    let cache = matches.opt_str("cache").map(PathBuf::from).unwrap_or_else(std::env::temp_dir);
    fs::create_dir_all(&cache).expect("Failed to create cache directory if missing");
    if !cache.is_dir() {
        eprintln!("Invalid cache directory");
        return 1;
    }

    let check_sat_using = matches.opt_str("check-sat-using");

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

    let exhaustive = matches.opt_present("exhaustive");

    let timeout: Option<u64> = match matches.opt_get("timeout") {
        Ok(timeout) => timeout,
        Err(e) => {
            eprintln!("Failed to parse --timeout: {}", e);
            return 1;
        }
    };

    let mut tests = Vec::new();
    if let Some(path) = matches.opt_str("test").map(PathBuf::from) {
        if path.extension() == Some(OsStr::new("toml")) || path.extension() == Some(OsStr::new("litmus")) {
            tests.push(path)
        } else if let Err(e) = process_at_file(&path, &mut tests) {
            eprintln!("Error when reading list of tests from {}:\n{}", path.display(), e);
            return 1;
        }
    }

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

    let cat = match cat::load_cat(&matches.opt_str("model").unwrap()) {
        Ok(mut cat) => {
            cat.unshadow(&mut cat::Shadows::new());
            let mut tcx = tcx_from_config(&isa_config);
            match cat::infer_cat(&mut tcx, cat) {
                Ok(cat) => cat,
                Err(e) => {
                    eprintln!("Type error in cat: {:?}\n", e);
                    return 1;
                }
            }
        }
        Err(e) => {
            eprintln!("Error in cat file: {}\n", e);
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
                opts::print_usage(&opts, 1)
            }
        }
    };
    let only_group: Option<usize> = matches.opt_get("only-group").unwrap();

    thread::scope(|scope| {
        for group_id in 0..thread_groups {
            if only_group.is_some() && group_id != only_group.unwrap() {
                continue;
            }

            let tests = &tests;
            let refs = &refs;
            let cat = &cat;
            let regs = &regs;
            let lets = &lets;
            let fregs = &fregs;
            let flets = &flets;
            let shared_state = &shared_state;
            let fshared_state = &fshared_state;
            let isa_config = &isa_config;
            let cache = &cache;
            let dot_path = &dot_path;
            let check_sat_using = check_sat_using.as_deref();

            scope.spawn(move |_| {
                for (i, litmus_file) in GroupIndex::new(tests, group_id, thread_groups).enumerate() {
                    let litmus = if litmus_file.extension() == Some(OsStr::new("litmus")) {
                        let output = Command::new("isla-litmus")
                            .arg(litmus_file)
                            .output()
                            .expect("Failed to invoke isla-litmus");

                        if output.status.success() {
                            String::from_utf8_lossy(&output.stdout).to_string()
                        } else {
                            eprintln!(
                                "Failed to translate litmus file: {}\n{}",
                                litmus_file.display(),
                                String::from_utf8_lossy(&output.stderr)
                            );
                            continue;
                        }
                    } else {
                        fs::read_to_string(&litmus_file).expect("Failed to read test file")
                    };

                    let litmus = match Litmus::parse(&litmus, &shared_state.symtab, isa_config) {
                        Ok(litmus) => litmus,
                        Err(msg) => {
                            eprintln!("Failed to parse litmus file: {}\n{}", litmus_file.display(), msg);
                            continue;
                        }
                    };

                    let now = Instant::now();
                    let result_queue = SegQueue::new();

                    let opts = LitmusRunOpts {
                        num_threads: threads_per_test,
                        timeout,
                        ignore_ifetch: !use_ifetch,
                        exhaustive,
                        armv8_page_tables,
                        merge_translations,
                    };

                    let run_info = run_litmus::smt_output_per_candidate::<B64, _, _, ResultError>(
                        &format!("g{}t{}", group_id, i),
                        &opts,
                        &litmus,
                        cat,
                        regs.clone(),
                        lets.clone(),
                        shared_state,
                        isa_config,
                        fregs.clone(),
                        flets.clone(),
                        fshared_state,
                        footprint_config,
                        check_sat_using,
                        cache,
                        &|exec, memory, footprints, z3_output| {
                            let mut names = HashMap::new();
                            for (va_name, va) in &litmus.symbolic_addrs {
                                name_initial_walk_bitvectors(
                                    &mut names,
                                    va_name,
                                    VirtualAddress::from_u64(*va),
                                    isa_config.page_table_base,
                                    memory,
                                )
                            }

                            if z3_output.starts_with("sat") {
                                let graph = if dot_path.is_some() {
                                    match graph_from_z3_output(exec, &names, footprints, z3_output, &litmus, &cat) {
                                        Ok(graph) => Some(Box::new(graph)),
                                        Err(err) => {
                                            eprintln!("Failed to generate graph: {}", err);
                                            None
                                        }
                                    }
                                } else {
                                    None
                                };
                                result_queue.push(Allowed(graph));
                            } else if z3_output.starts_with("unsat") {
                                result_queue.push(Forbidden);
                            } else {
                                result_queue.push(Error);
                            }
                            Ok(())
                        },
                    );

                    let ref_result = refs.get(&litmus.name);

                    if let Err(msg) = run_info {
                        println!("{msg:?}: {msg}", msg=msg);
                        print_results(&litmus.name, now, &[Error], ref_result);
                        continue;
                    }

                    let mut results: Vec<AxResult> = Vec::new();
                    while let Ok(result) = result_queue.pop() {
                        results.push(result)
                    }

                    print_results(&litmus.name, now, &results, ref_result);

                    if let Some(dot_path) = dot_path {
                        for (i, allowed) in results.iter().filter(|result| result.is_allowed()).enumerate() {
                            if let Allowed(Some(graph)) = allowed {
                                let dot_file = dot_path.join(format!("{}_{}.dot", litmus.name, i + 1));
                                std::fs::write(&dot_file, graph.to_string()).expect("Failed to write dot file");

                                if view {
                                    Command::new("dot")
                                        .args(&["-Tpng", "-o", &format!("{}_{}.png", litmus.name, i + 1)])
                                        .arg(&dot_file)
                                        .output()
                                        .expect("Failed to invoke dot");

                                    Command::new("xdg-open")
                                        .arg(format!("{}_{}.png", litmus.name, i + 1))
                                        .output()
                                        .expect("Failed to invoke xdg-open");
                                }
                            }
                        }
                    }
                }
            });
        }
    })
    .unwrap();

    if FAILURE.load(Ordering::Relaxed) {
        1
    } else {
        0
    }
}

fn print_results(name: &str, start_time: Instant, results: &[AxResult], expected: Option<&AxResult>) {
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

#[derive(Debug)]
pub enum AtLineError {
    NoParse(usize, String),
}

impl fmt::Display for AtLineError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AtLineError::NoParse(lineno, line) => write!(f, "Could not parse line {}: {}", lineno, line),
        }
    }
}

impl Error for AtLineError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

fn process_at_line<P: AsRef<Path>>(
    root: P,
    line: &str,
    tests: &mut Vec<PathBuf>,
) -> Option<Result<(), Box<dyn Error>>> {
    let pathbuf = root.as_ref().join(&line);
    let extension = pathbuf.extension()?.to_string_lossy();
    if pathbuf.file_name()?.to_string_lossy().starts_with('@') {
        Some(process_at_file(&pathbuf, tests))
    } else if extension == "litmus" || extension == "toml" {
        tests.push(pathbuf);
        Some(Ok(()))
    } else {
        None
    }
}

fn process_at_file<P: AsRef<Path>>(path: P, tests: &mut Vec<PathBuf>) -> Result<(), Box<dyn Error>> {
    let mut pathbuf = fs::canonicalize(path)?;
    let fd = File::open(&pathbuf)?;
    let reader = BufReader::new(fd);
    pathbuf.pop();

    for (i, line) in reader.lines().enumerate() {
        let line = line?;
        if !line.starts_with('#') && !line.is_empty() {
            match process_at_line(&pathbuf, &line, tests) {
                Some(Ok(())) => (),
                Some(err) => return err,
                None => return Err(AtLineError::NoParse(i, line).into()),
            }
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
            Ok(usize::from_str_radix(num_states, 10)?)
        } else {
            Err(BadStatesLine(line).into())
        }
    } else {
        Err(UnexpectedEof.into())
    }
}

fn negate_result(result: AxResult) -> AxResult {
    match result {
        AxResult::Allowed(_) => AxResult::Forbidden,
        AxResult::Forbidden => AxResult::Allowed(None),
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

fn parse_expected(expected: &str) -> Result<AxResult, RefsError> {
    if expected == "Allowed" {
        Ok(AxResult::Allowed(None))
    } else if expected == "Forbidden" || expected == "Required" {
        // Required is used when the litmus test has an assertion
        // which must be true for all traces, but we have already
        // re-written forall X into ~(exists(~X)) where ~X must be
        // forbidden.
        Ok(AxResult::Forbidden)
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
            let expected =
                line.split_whitespace().nth(2).ok_or_else(|| BadTestLine(line.to_string())).and_then(parse_expected)?;
            let num_states = parse_states_line(&mut lines)?;
            for _ in 0..num_states {
                lines.next();
            }
            let result = parse_result_line(&mut lines, expected)?;
            refs.insert(test.to_string(), result);
        }
    }

    Ok(refs)
}
