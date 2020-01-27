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

use std::sync::atomic::{AtomicUsize, Ordering::*};

static LOG_LEVEL: AtomicUsize = AtomicUsize::new(0);

fn color(tid: usize) -> &'static str {
    match tid % 14 {
        0 => "\x1b[91m",
        1 => "\x1b[92m",
        2 => "\x1b[93m",
        3 => "\x1b[94m",
        4 => "\x1b[95m",
        5 => "\x1b[96m",
        6 => "\x1b[97m",
        7 => "\x1b[91m\x1b[4m",
        8 => "\x1b[92m\x1b[4m",
        9 => "\x1b[93m\x1b[4m",
        10 => "\x1b[94m\x1b[4m",
        11 => "\x1b[95m\x1b[4m",
        12 => "\x1b[96m\x1b[4m",
        13 => "\x1b[97m\x1b[4m",
        _ => unreachable!(),
    }
}

static CLEAR: &str = "\x1b[0m";

pub fn set_verbosity(level: usize) {
    LOG_LEVEL.store(level, SeqCst);
}

pub fn log(level: usize, msg: &str) {
    if LOG_LEVEL.load(Relaxed) > level {
        eprintln!("[log]: {}", msg)
    }
}

pub fn log_from(tid: usize, level: usize, msg: &str) {
    if LOG_LEVEL.load(Relaxed) > level {
        eprintln!("[{}{:<3}{}]: {}", color(tid), tid, CLEAR, msg)
    }
}
