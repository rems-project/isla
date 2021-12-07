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

use isla_lib::lexer::*;

pub struct SexpLexer<'input> {
    lexer: Lexer<'input>,
}

impl<'input> SexpLexer<'input> {
    pub fn new(input: &'input str) -> Self {
        SexpLexer { lexer: Lexer::new(input) }
    }
}

#[derive(Clone, Debug)]
pub enum Tok<'input> {
    Hex(&'input str),
    Bin(&'input str),
    Nat(&'input str),
    Atom(&'input str),
    Lparen,
    Rparen,
}

impl<'input> fmt::Display for Tok<'input> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub struct Keyword {
    word: &'static str,
    token: Tok<'static>,
    len: usize,
}

impl Keyword {
    pub fn new(kw: &'static str, tok: Tok<'static>) -> Self {
        Keyword { word: kw, token: tok, len: kw.len() }
    }
}

lazy_static! {
    static ref KEYWORDS: Vec<Keyword> = {
        use Tok::*;
        vec![Keyword::new("(", Lparen), Keyword::new(")", Rparen)]
    };
    pub static ref ATOM_REGEX: Regex = Regex::new(r"^[a-zA-Z_=><.!/-][0-9a-zA-Z_=><.!/-]*").unwrap();
    pub static ref BAR_ATOM_REGEX: Regex = Regex::new(r"^\|[^|]+\|").unwrap();
}

pub type Span<'input> = Result<(usize, Tok<'input>, usize), LexError>;

impl<'input> Iterator for SexpLexer<'input> {
    type Item = Span<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        use Tok::*;
        self.lexer.consume_whitespace()?;
        let start_pos = self.lexer.pos;

        for k in KEYWORDS.iter() {
            if self.lexer.buf.starts_with(k.word) {
                self.lexer.pos += k.len;
                self.lexer.buf = &self.lexer.buf[k.len..];
                return Some(Ok((start_pos, k.token.clone(), self.lexer.pos)));
            }
        }

        match self.lexer.consume_regex(&ATOM_REGEX) {
            None => (),
            Some((from, id, to)) => return Some(Ok((from, Atom(id), to))),
        }

        match self.lexer.consume_regex(&BAR_ATOM_REGEX) {
            None => (),
            Some((from, id, to)) => return Some(Ok((from, Atom(&id[1..(id.len() - 1)]), to))),
        }

        match self.lexer.consume_regex(&HEX_REGEX) {
            None => (),
            Some((from, bits, to)) => return Some(Ok((from, Hex(bits), to))),
        }

        match self.lexer.consume_regex(&BIN_REGEX) {
            None => (),
            Some((from, bits, to)) => return Some(Ok((from, Bin(bits), to))),
        }

        match self.lexer.consume_regex(&NAT_REGEX) {
            None => (),
            Some((from, n, to)) => return Some(Ok((from, Nat(n), to))),
        }

        Some(Err(LexError { pos: self.lexer.pos }))
    }
}
