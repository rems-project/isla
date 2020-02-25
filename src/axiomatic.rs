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
use std::fmt;
use std::fs::{self, File};
use std::io::{prelude::*, BufReader};
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
    opts.optopt("", "threads-per-test", "number of threads to user per test", "<n>");
    opts.reqopt("m", "model", "Memory model in cat format", "<path>");
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

    let mut tests = Vec::new();
    if let Some(at_file) = matches.opt_str("tests") {
        if let Err(e) = process_at_file(&at_file, &mut tests) {
            eprintln!("Error when reading {}:\n{}", at_file, e);
            return 1
        }
    }

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
        match matches.opt_get_default("threads-per-test", 1) {
            Ok(n) => {
                if num_threads % n == 0 {
                    (n, num_threads / n)
                } else {
                    eprintln!("The number of threads must be divisible by the value of --threads-per-test");
                    return 1
                }
            }
            Err(e) => {
                eprintln!("Could not parse --threads-per-test option: {}", e);
                opts::print_usage(&opts, 1)
            }
        }
    };

    thread::scope(|scope| {
        for group_id in 0..thread_groups {
            let tests = &tests;
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

                    let _run_info = run_litmus::smt_output_per_candidate::<B64, _, _, ()>(
                        &format!("g{}t{}", group_id, i),
                        threads_per_test,
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
                                eprintln!("Allowed")
                            } else if z3_output.starts_with("unsat") {
                                result_queue.push(Forbidden);
                                eprintln!("Forbidden")
                            } else {
                                result_queue.push(Error);
                                eprintln!("Error")
                            }
                            Ok(())
                        },
                    )
                    .unwrap();

                    let mut results: Vec<AxResult> = Vec::new();
                    loop {
                        match result_queue.pop() {
                            Ok(result) => results.push(result),
                            Err(_) => break,
                        }
                    }

                    if results.contains(&Error) {
                        println!("{} error {}ms", litmus.name, now.elapsed().as_millis());
                    } else if results.contains(&Allowed) {
                        println!("{} allowed {}ms", litmus.name, now.elapsed().as_millis());
                    } else {
                        println!("{} forbidden {}ms", litmus.name, now.elapsed().as_millis());
                    }
                }
            });
        }
    })
    .unwrap();

    0
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
