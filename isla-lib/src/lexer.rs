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

use regex::Regex;
use std::fmt;

pub struct LexError {
    pub pos: usize,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Lex error at position: {}", self.pos)
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
        match r.find(&self.buf) {
            None => None,
            Some(mat) => {
                let start_pos = self.pos;
                self.pos += mat.end();
                self.buf = &self.buf[mat.end()..];
                Some((start_pos, mat.as_str(), self.pos))
            }
        }
    }

    pub fn consume_string_literal(&mut self) -> Option<(usize, &'input str, usize)> {
        if self.buf.chars().next()? == '\"' {
            let mut string_end = 1;
            loop {
                if let '\"' = self.buf.chars().nth(string_end)? {
                    let contents = &self.buf[1..string_end];
                    let start_pos = self.pos;
                    self.pos += string_end + 1;
                    self.buf = &self.buf[(string_end + 1)..];
                    break Some((start_pos, &contents, self.pos));
                }
                string_end += 1
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
    pub static ref NAT_REGEX: Regex = Regex::new(r"^[0-9]+").unwrap();
}
