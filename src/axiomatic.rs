// MIT License
//
// Copyright (c) 2019 Alasdair Armstrong
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use sha2::{Digest, Sha256};
use crossbeam::queue::SegQueue;
use crossbeam::thread;
use std::collections::HashMap;
use std::fmt;
use std::fs::{self, File};
use std::io::{prelude::*, BufReader, Lines};
use std::error::Error;
use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::time::Instant;

use isla_axiomatic::run_litmus;
use isla_axiomatic::litmus::Litmus;
use isla_cat::cat;
use isla_lib::log;
use isla_lib::concrete::B64;
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    process::exit(code)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum AxResult {
    Allowed,
    Forbidden,
    Error,
}

struct GroupIndex<'a, A> {
    i: usize,
    group_id: usize,
    num_groups: usize,
    buf: &'a [A]
}

impl<'a, A> GroupIndex<'a, A> {
    fn new(buf: &'a [A], group_id: usize, num_groups: usize) -> Self {
        GroupIndex {
            i: 0,
            group_id,
            num_groups,
            buf,
        }
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

fn isla_main() -> i32 {
    use AxResult::*;
    let now = Instant::now();

    let mut opts = opts::common_opts();
    opts.optopt("t", "tests", "an @file that points to litmus tests", "<path>");
    opts.optopt("", "thread-groups", "number threads per group", "<n>");
    opts.optopt("", "only-group", "only perform jobs for one thread group", "<n>");
    opts.optopt("", "timeout", "Add a timeout (in seconds)", "<n>");
    opts.reqopt("m", "model", "Memory model in cat format", "<path>");
    opts.optopt("", "refs", "references to compare output with", "<path>");
    opts.optopt("", "cache", "A directory to cache intermediate results. The default is TMPDIR if set, otherwise /tmp", "<path>");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse::<B64>(&mut hasher, &opts);
    let CommonOpts { num_threads, mut arch, symtab, isa_config } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let arch_hash = hasher.result();
    log!(log::VERBOSE, &format!("Archictecture + config hash: {:x}", arch_hash));
    log!(log::VERBOSE, &format!("Parsing took: {}ms", now.elapsed().as_millis()));

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    let cache = matches.opt_str("cache").map(PathBuf::from).unwrap_or_else(|| std::env::temp_dir());
    if !cache.is_dir() {
        eprintln!("Invalid cache directory");
        return 1
    }

    let timeout: Option<u64> = match matches.opt_get("timeout") {
        Ok(timeout) => timeout,
        Err(e) => {
            eprintln!("Failed to parse --timeout: {}", e);
            return 1
        }
    };

    let mut tests = Vec::new();
    if let Some(at_file) = matches.opt_str("tests") {
        if let Err(e) = process_at_file(&at_file, &mut tests) {
            eprintln!("Error when reading {}:\n{}", at_file, e);
            return 1
        }
    }

    let refs = if let Some(refs_file) = matches.opt_str("refs") {
        match process_refs(&refs_file) {
            Ok(refs) => refs,
            Err(e) => {
                eprintln!("Error when reading {}:\n{}", refs_file, e);
                return 1
            }
        }
    } else {
        HashMap::new()
    };

    let cat = match cat::load_cat(&matches.opt_str("model").unwrap()) {
        Ok(mut cat) => {
            cat.unshadow(&mut cat::Shadows::new());
            let mut tcx = cat::initial_tcx(isa_config.barriers.values().map(String::clone));
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
                    return 1
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
                continue
            }

            let tests = &tests;
            let refs = &refs;
            let cat = &cat;
            let regs = &regs;
            let lets = &lets;
            let shared_state = &shared_state;
            let isa_config = &isa_config;
            let cache = &cache;

            scope.spawn(move |_| {
                for (i, litmus_file) in GroupIndex::new(tests, group_id, thread_groups).enumerate() {
                    let output = Command::new("isla-litmus")
                        .arg(litmus_file)
                        .output()
                        .expect("Failed to invoke isla-litmus");

                    let litmus = if output.status.success() {
                        match Litmus::parse(&String::from_utf8_lossy(&output.stdout), &shared_state.symtab, isa_config) {
                            Ok(litmus) => litmus,
                            Err(msg) => {
                                eprintln!("Failed to parse litmus file: {}\n{}", litmus_file.display(), msg);
                                continue
                            }
                        }
                    } else {
                        eprintln!("Failed to translate litmus file: {}\n{}", litmus_file.display(), String::from_utf8_lossy(&output.stderr));
                        continue;
                    };

                    let now = Instant::now();

                    let result_queue = SegQueue::new();

                    let run_info = run_litmus::smt_output_per_candidate::<B64, _, _, ()>(
                        &format!("g{}t{}", group_id, i),
                        threads_per_test,
                        timeout,
                        &litmus,
                        cat,
                        regs.clone(),
                        lets.clone(),
                        shared_state,
                        isa_config,
                        cache,
                        &|_exec, _footprints, z3_output| {
                            if z3_output.starts_with("sat") {
                                result_queue.push(Allowed);
                            } else if z3_output.starts_with("unsat") {
                                result_queue.push(Forbidden);
                            } else {
                                result_queue.push(Error);
                            }
                            Ok(())
                        },
                    );

                    let ref_result = refs.get(&litmus.name);

                    if let Err(_) = run_info {
                        print_result(&litmus.name, now, Error, ref_result);
                        continue;
                    }

                    let mut results: Vec<AxResult> = Vec::new();
                    loop {
                        match result_queue.pop() {
                            Ok(result) => results.push(result),
                            Err(_) => break,
                        }
                    }

                    if results.contains(&Error) {
                        print_result(&litmus.name, now, Error, ref_result);
                    } else if results.contains(&Allowed) {
                        print_result(&litmus.name, now, Allowed, ref_result);
                    } else {
                        print_result(&litmus.name, now, Forbidden, ref_result);
                    }
                }
            });
        }
    })
    .unwrap();

    0
}

fn print_result(name: &str, start_time: Instant, got: AxResult, expected: Option<&AxResult>) {
    let prefix = format!("{} {:?} {:?} {}ms ", name, got, expected, start_time.elapsed().as_millis());

    let result = if Some(&got) == expected {
        "\x1b[92m\x1b[1mok\x1b[0m"
    } else if got == AxResult::Error {
        "\x1b[95m\x1b[1merror\x1b[0m"
    } else if expected == None {
        "\x1b[93m\x1b[1m?\x1b[0m"
    } else {
        "\x1b[91m\x1b[1mfail\x1b[0m"
    };
    println!("{:.<80} {}", prefix, result)
}

#[derive(Debug)]
pub enum AtLineError {
    NoParse(usize, String)
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

fn process_at_line<P: AsRef<Path>>(root: P, line: &str, tests: &mut Vec<PathBuf>) -> Option<Result<(), Box<dyn Error>>> {
    let pathbuf = root.as_ref().join(&line);
    if pathbuf.file_name()?.to_string_lossy().starts_with("@") {
        Some(process_at_file(&pathbuf, tests))
    } else if pathbuf.extension()?.to_string_lossy() == "litmus" {
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
        if !line.starts_with("#") && !line.is_empty() {
            match process_at_line(&pathbuf, &line, tests) {
                Some(Ok(())) => (),
                Some(err) => return err,
                None => Err(AtLineError::NoParse(i, line.to_string()))?,
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
            Err(BadStatesLine(line.to_string()))?
        }
    } else {
        Err(UnexpectedEof)?
    }
}

fn negate_result(result: AxResult) -> AxResult {
    match result {
        AxResult::Allowed => AxResult::Forbidden,
        AxResult::Forbidden => AxResult::Allowed,
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
            Err(BadResultLine(line.to_string()))?
        }
    } else {
        Err(UnexpectedEof)?
    }
}

fn parse_expected(expected: &str) -> Result<AxResult, RefsError> {
    if expected == "Allowed" {
        Ok(AxResult::Allowed)
    } else if expected == "Forbidden" {
        Ok(AxResult::Forbidden)
    } else if expected == "Required" {
        // TODO: Check what this actually is
        Ok(AxResult::Allowed)
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

    loop {
        if let Some(line) = lines.next() {
            let line = line?;
            if line.starts_with("Test") {
                let test = line.split_whitespace().nth(1).ok_or_else(|| BadTestLine(line.to_string()))?;
                let expected = line
                    .split_whitespace()
                    .nth(2)
                    .ok_or_else(|| BadTestLine(line.to_string()))
                    .and_then(parse_expected)?;
                let num_states = parse_states_line(&mut lines)?;
                for _ in 0..num_states {
                    lines.next();
                }
                let result = parse_result_line(&mut lines, expected)?;
                refs.insert(test.to_string(), result);
            }
        } else {
            break
        }
    };

    Ok(refs)
}
