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

use std::fmt;

use crate::page_table::setup::SetupParseError;
use isla_lib::lexer::*;

pub struct SetupLexer<'input> {
    lexer: Lexer<'input>,
}

impl<'input> SetupLexer<'input> {
    pub fn new(input: &'input str) -> Self {
        SetupLexer { lexer: Lexer::new(input) }
    }
}

#[derive(Clone, Debug)]
pub enum Tok<'input> {
    Nat(&'input str),
    Id(&'input str),
    Hex(&'input str),
    Bin(&'input str),
    Assert,
    As,
    At,
    And,
    Level,
    MapsTo,
    MaybeMapsTo,
    Identity,
    Aligned,
    Virtual,
    Intermediate,
    Physical,
    With,
    Code,
    Default,
    Implies,
    S1Table,
    S2Table,
    Option,
    Let,
    Not,
    BooleanAnd,
    BitAnd,
    BooleanOr,
    BitOr,
    Lparen,
    Rparen,
    Lsquare,
    Rsquare,
    Lbrace,
    Rbrace,
    Colon,
    Semi,
    NotEq,
    EqEq,
    Eq,
    Star,
    Comma,
    Caret,
    DotDot,
    Dot,
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
    is_symbol: bool,
}

impl Keyword {
    pub fn new(kw: &'static str, tok: Tok<'static>) -> Self {
        let c = kw.chars().next().expect("lexer contains empty keyword");
        Keyword { word: kw, token: tok, len: kw.len(), is_symbol: !c.is_ascii_alphabetic() }
    }
}

lazy_static! {
    static ref KEYWORDS: Vec<Keyword> = {
        use Tok::*;
        vec![
            Keyword::new("|->", MapsTo),
            Keyword::new("?->", MaybeMapsTo),
            Keyword::new("~", Not),
            Keyword::new("&&", BooleanAnd),
            Keyword::new("&", BitAnd),
            Keyword::new("||", BooleanOr),
            Keyword::new("|", BitOr),
            Keyword::new("(", Lparen),
            Keyword::new(")", Rparen),
            Keyword::new("[", Lsquare),
            Keyword::new("]", Rsquare),
            Keyword::new("{", Lbrace),
            Keyword::new("}", Rbrace),
            Keyword::new(":", Colon),
            Keyword::new(";", Semi),
            Keyword::new("!=", NotEq),
            Keyword::new("==", EqEq),
            Keyword::new("=", Eq),
            Keyword::new("*", Star),
            Keyword::new("^", Caret),
            Keyword::new(",", Comma),
            Keyword::new("..", DotDot),
            Keyword::new(".", Dot),
            Keyword::new("assert", Assert),
            Keyword::new("as", As),
            Keyword::new("at", At),
            Keyword::new("and", And),
            Keyword::new("aligned", Aligned),
            Keyword::new("level", Level),
            Keyword::new("virtual", Virtual),
            Keyword::new("intermediate", Intermediate),
            Keyword::new("identity", Identity),
            Keyword::new("physical", Physical),
            Keyword::new("with", With),
            Keyword::new("code", Code),
            Keyword::new("default", Default),
            Keyword::new("true", True),
            Keyword::new("false", False),
            Keyword::new("let", Let),
            Keyword::new("s1table", S1Table),
            Keyword::new("s2table", S2Table),
            Keyword::new("option", Option),
        ]
    };
}

pub type Span<'input> = Result<(usize, Tok<'input>, usize), SetupParseError>;

impl<'input> Iterator for SetupLexer<'input> {
    type Item = Span<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        use Tok::*;
        self.lexer.consume_whitespace()?;
        let start_pos = self.lexer.pos;

        for k in KEYWORDS.iter() {
            if self.lexer.buf.starts_with(k.word) {
                match self.lexer.buf.chars().nth(k.len) {
                    // A keyword cannot be immediately followed by any valid identifier characters
                    Some(c) if !k.is_symbol && (c.is_ascii_alphanumeric() || c == '_') => (),
                    _ => {
                        self.lexer.pos += k.len;
                        self.lexer.buf = &self.lexer.buf[k.len..];
                        return Some(Ok((start_pos, k.token.clone(), self.lexer.pos)));
                    }
                }
            }
        }

        match self.lexer.consume_regex(&ID_REGEX) {
            None => (),
            Some((from, id, to)) => return Some(Ok((from, Id(id), to))),
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

        Some(Err(SetupParseError::Lex { pos: self.lexer.pos }))
    }
}
