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

#[derive(Clone, Debug)]
pub enum Tok<'input> {
    Hex(&'input str),
    Bin(&'input str),
    Nat(&'input str),
    Id(&'input str),
    String(&'input str),
    Unit,
    Lbrace,
    Rbrace,
    Minus,
    Comma,
    True,
    False,
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
        table.push(Keyword::new("()", Unit));
        table.push(Keyword::new("{", Lbrace));
        table.push(Keyword::new("}", Rbrace));
        table.push(Keyword::new("-", Minus));
        table.push(Keyword::new("=", Eq));
        table.push(Keyword::new(",", Comma));
        table.push(Keyword::new("true", True));
        table.push(Keyword::new("false", False));
        table
    };
}

pub type Span<'input> = Result<(usize, Tok<'input>, usize), LexError>;

impl<'input> Iterator for Lexer<'input> {
    type Item = Span<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        use Tok::*;
        self.consume_whitespace()?;
        let start_pos = self.pos;

        for k in KEYWORDS.iter() {
            if self.buf.starts_with(k.word) {
                self.pos += k.len;
                self.buf = &self.buf[k.len..];
                return Some(Ok((start_pos, k.token.clone(), self.pos)));
            }
        }

        match self.consume_regex(&ID_REGEX) {
            None => (),
            Some((from, id, to)) => return Some(Ok((from, Id(id), to))),
        }

        match self.consume_regex(&HEX_REGEX) {
            None => (),
            Some((from, bits, to)) => return Some(Ok((from, Hex(&bits[2..]), to))),
        }

        match self.consume_regex(&BIN_REGEX) {
            None => (),
            Some((from, bits, to)) => return Some(Ok((from, Bin(&bits[2..]), to))),
        }

        match self.consume_regex(&NAT_REGEX) {
            None => (),
            Some((from, n, to)) => return Some(Ok((from, Nat(n), to))),
        }

        match self.consume_string_literal() {
            None => (),
            Some((from, s, to)) => return Some(Ok((from, String(s), to))),
        }

        Some(Err(LexError { pos: self.pos }))
    }
}
