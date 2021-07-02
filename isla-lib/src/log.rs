// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
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

use std::sync::atomic::{AtomicU32, Ordering::*};

pub static FLAGS: AtomicU32 = AtomicU32::new(0);

pub fn color(tid: usize) -> &'static str {
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

pub const VERBOSE: u32 = 1u32;
pub const MEMORY: u32 = 2u32;
pub const FORK: u32 = 4u32;
pub const LITMUS: u32 = 8u32;
pub const PROBE: u32 = 16u32;
pub const CACHE: u32 = 32u32;
pub const GRAPH: u32 = 64u32;

pub fn set_flags(flags: u32) {
    FLAGS.store(flags, SeqCst);
}

#[macro_export]
macro_rules! log {
    ($flags: expr, $msg: expr) => {
        if log::FLAGS.load(std::sync::atomic::Ordering::Relaxed) & $flags > 0u32 {
            eprintln!("[log]: {}", $msg)
        }
    };
}

#[macro_export]
macro_rules! log_from {
    ($tid: expr, $flags: expr, $msg: expr) => {
        if log::FLAGS.load(std::sync::atomic::Ordering::Relaxed) & $flags > 0u32 {
            eprintln!("[{}{:<3}\x1b[0m]: {}", log::color($tid), $tid, $msg)
        }
    };
}

#[macro_export]
macro_rules! if_logging {
    ($flags: expr, $body:block) => {
        if log::FLAGS.load(std::sync::atomic::Ordering::Relaxed) & $flags > 0u32 $body
    };
}
