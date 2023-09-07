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

use regex::Regex;
use std::fmt;

#[derive(Clone, Debug)]
pub struct LexError {
    pub pos: usize,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Lexical error at position: {}", self.pos)
    }
}

pub struct Lexer<'input> {
    pub buf: &'input str,
    pub pos: usize,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer { buf: input, pos: 0 }
    }
}

impl<'input> Lexer<'input> {
    pub fn consume_whitespace(&mut self) -> Option<()> {
        loop {
            if self.buf.chars().next()?.is_whitespace() {
                self.pos += 1;
                self.buf = &self.buf[1..]
            } else {
                break Some(());
            }
        }
    }

    pub fn consume_regex(&mut self, r: &Regex) -> Option<(usize, &'input str, usize)> {
        match r.find(self.buf) {
            None => None,
            Some(mat) => {
                let start_pos = self.pos;
                self.pos += mat.end();
                self.buf = &self.buf[mat.end()..];
                Some((start_pos, mat.as_str(), self.pos))
            }
        }
    }

    pub fn consume_to_newline(&mut self) -> Option<(usize, &'input str, usize)> {
        match self.buf.find('\n') {
            None => None,
            Some(n) => {
                let start_pos = self.pos;
                let contents = &self.buf[0..n];
                self.pos += n + 1;
                self.buf = &self.buf[(n + 1)..];
                Some((start_pos, contents, self.pos - 1))
            }
        }
    }

    pub fn consume_string_literal(&mut self) -> Option<(usize, &'input str, usize)> {
        // Note: this doesn't unescape the string
        if self.buf.chars().next()? == '\"' {
            let mut string_end = 1;
            loop {
                match self.buf.chars().nth(string_end)? {
                    '\"' => {
                        let contents = &self.buf[1..string_end];
                        let start_pos = self.pos;
                        self.pos += string_end + 1;
                        self.buf = &self.buf[(string_end + 1)..];
                        break Some((start_pos, contents, self.pos));
                    }
                    '\\' => string_end += 2,
                    _ => string_end += 1,
                }
            }
        } else {
            None
        }
    }
}

lazy_static! {
    pub static ref ID_REGEX: Regex = Regex::new(r"^[a-zA-Z_][0-9a-zA-Z_]*").unwrap();
    pub static ref HEX_REGEX: Regex = Regex::new(r"^[#0]x[0-9a-fA-F]+").unwrap();
    pub static ref BIN_REGEX: Regex = Regex::new(r"^[#0]b[0-1]+").unwrap();
    pub static ref CAP_REGEX: Regex = Regex::new(r"^[#0]c[0-1][0-9a-fA-F]*").unwrap();
    pub static ref NAT_REGEX: Regex = Regex::new(r"^[0-9]+").unwrap();
}
