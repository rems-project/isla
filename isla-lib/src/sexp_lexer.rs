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

use crate::lexer::*;

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
        let mut table = Vec::new();
        table.push(Keyword::new("(", Lparen));
        table.push(Keyword::new(")", Rparen));
        table
    };
    pub static ref ATOM_REGEX: Regex = Regex::new(r"^[a-zA-Z_=><.!-][0-9a-zA-Z_=><.!-]*").unwrap();
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
            Some((from, bits, to)) => return Some(Ok((from, Hex(&bits[2..]), to))),
        }

        match self.lexer.consume_regex(&BIN_REGEX) {
            None => (),
            Some((from, bits, to)) => return Some(Ok((from, Bin(&bits[2..]), to))),
        }

        match self.lexer.consume_regex(&NAT_REGEX) {
            None => (),
            Some((from, n, to)) => return Some(Ok((from, Nat(n), to))),
        }

        Some(Err(LexError { pos: self.lexer.pos }))
    }
}
