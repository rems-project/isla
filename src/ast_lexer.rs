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

#[derive(Clone, Debug)]
pub enum Tok<'input> {
    Nat(&'input str),
    Id(&'input str),
    String(&'input str),
    Hex(&'input str),
    Bin(&'input str),
    OpNot,
    OpOr,
    OpAnd,
    OpEq,
    OpNeq,
    OpSlice,
    OpConcat,
    OpSigned,
    OpUnsigned,
    OpBvnot,
    OpBvor,
    OpBvxor,
    OpBvand,
    OpBvadd,
    OpBvsub,
    OpBvaccess,
    OpBitToBool,
    OpLteq,
    OpLt,
    TyI,
    TyLb,
    TySb,
    TyFb,
    TyUnit,
    TyBool,
    TyBit,
    TyString,
    TyReal,
    TyEnum,
    TyStruct,
    TyUnion,
    TyVec,
    TyList,
    TurboFish,
    Gt,
    Amp,
    Lparen,
    Rparen,
    Lbrace,
    Rbrace,
    Dot,
    Star,
    Colon,
    Eq,
    Comma,
    Semi,
    Dollar,
    Bitzero,
    Bitone,
    Unit,
    Arrow,
    Minus,
    Struct,
    Is,
    As,
    Jump,
    Goto,
    Mono,
    Failure,
    Arbitrary,
    End,
    Register,
    Fn,
    Let,
    Enum,
    Union,
    Val,
    True,
    False,
}

impl<'input> fmt::Display for Tok<'input> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub struct LexError {
    pos: usize,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Lex error at position: {}", self.pos)
    }
}

pub struct Lexer<'input> {
    buf: &'input str,
    pos: usize,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer { buf: input, pos: 0 }
    }
}

struct Keyword {
    word: &'static str,
    token: Tok<'static>,
    len: usize,
}

impl Keyword {
    fn new(kw: &'static str, tok: Tok<'static>) -> Self {
        Keyword { word: kw, token: tok, len: kw.len() }
    }
}

lazy_static! {
    static ref KEYWORDS: Vec<Keyword> = {
        use Tok::*;
        let mut table = Vec::new();
        table.push(Keyword::new("::<", TurboFish));
        table.push(Keyword::new(">", Gt));
        table.push(Keyword::new("()", Unit));
        table.push(Keyword::new("->", Arrow));
        table.push(Keyword::new("&", Amp));
        table.push(Keyword::new("(", Lparen));
        table.push(Keyword::new(")", Rparen));
        table.push(Keyword::new("{", Lbrace));
        table.push(Keyword::new("}", Rbrace));
        table.push(Keyword::new(".", Dot));
        table.push(Keyword::new("*", Star));
        table.push(Keyword::new(":", Colon));
        table.push(Keyword::new("=", Eq));
        table.push(Keyword::new(",", Comma));
        table.push(Keyword::new(";", Semi));
        table.push(Keyword::new("$", Dollar));
        table.push(Keyword::new("bitzero", Bitzero));
        table.push(Keyword::new("bitone", Bitone));
        table.push(Keyword::new("-", Minus));
        table.push(Keyword::new("struct", Struct));
        table.push(Keyword::new("is", Is));
        table.push(Keyword::new("as", As));
        table.push(Keyword::new("jump", Jump));
        table.push(Keyword::new("goto", Goto));
        table.push(Keyword::new("mono", Mono));
        table.push(Keyword::new("failure", Failure));
        table.push(Keyword::new("arbitrary", Arbitrary));
        table.push(Keyword::new("end", End));
        table.push(Keyword::new("register", Register));
        table.push(Keyword::new("fn", Fn));
        table.push(Keyword::new("let", Let));
        table.push(Keyword::new("enum", Enum));
        table.push(Keyword::new("union", Union));
        table.push(Keyword::new("val", Val));
        table.push(Keyword::new("%i", TyI));
        table.push(Keyword::new("%lb", TyLb));
        table.push(Keyword::new("%sb", TySb));
        table.push(Keyword::new("%fb", TyFb));
        table.push(Keyword::new("%unit", TyUnit));
        table.push(Keyword::new("%bool", TyBool));
        table.push(Keyword::new("%bit", TyBit));
        table.push(Keyword::new("%string", TyString));
        table.push(Keyword::new("%real", TyReal));
        table.push(Keyword::new("%enum", TyEnum));
        table.push(Keyword::new("%struct", TyStruct));
        table.push(Keyword::new("%union", TyUnion));
        table.push(Keyword::new("%vec", TyVec));
        table.push(Keyword::new("%list", TyList));
        table.push(Keyword::new("@slice", OpSlice));
        table.push(Keyword::new("@concat", OpConcat));
        table.push(Keyword::new("@unsigned", OpUnsigned));
        table.push(Keyword::new("@signed", OpSigned));
        table.push(Keyword::new("@not", OpNot));
        table.push(Keyword::new("@or", OpOr));
        table.push(Keyword::new("@and", OpAnd));
        table.push(Keyword::new("@eq", OpEq));
        table.push(Keyword::new("@neq", OpNeq));
        table.push(Keyword::new("@bvnot", OpBvnot));
        table.push(Keyword::new("@bvor", OpBvor));
        table.push(Keyword::new("@bvxor", OpBvor));
        table.push(Keyword::new("@bvand", OpBvand));
        table.push(Keyword::new("@bvadd", OpBvadd));
        table.push(Keyword::new("@bvsub", OpBvsub));
        table.push(Keyword::new("@bvaccess", OpBvaccess));
        table.push(Keyword::new("@bit_to_bool", OpBitToBool));
        table.push(Keyword::new("@lteq", OpLteq));
        table.push(Keyword::new("@lt", OpLt));
        table.push(Keyword::new("bitzero", Bitzero));
        table.push(Keyword::new("bitone", Bitone));
        table.push(Keyword::new("true", True));
        table.push(Keyword::new("false", False));
        table
    };
    static ref ID_REGEX: Regex = Regex::new(r"^[a-zA-Z_][0-9a-zA-Z_]*").unwrap();
    static ref HEX_REGEX: Regex = Regex::new(r"^0x[0-9a-fA-F]+").unwrap();
    static ref BIN_REGEX: Regex = Regex::new(r"^0b[0-1]+").unwrap();
    static ref NAT_REGEX: Regex = Regex::new(r"^[0-9]+").unwrap();
}

pub type Span<'input> = Result<(usize, Tok<'input>, usize), LexError>;

impl<'input> Lexer<'input> {
    fn consume_whitespace(&mut self) -> Option<()> {
        loop {
            if self.buf.chars().next()?.is_whitespace() {
                self.pos += 1;
                self.buf = &self.buf[1..]
            } else {
                break Some(());
            }
        }
    }

    fn consume_regex(&mut self, r: &Regex) -> Option<(usize, &'input str, usize)> {
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

    fn consume_string_literal(&mut self) -> Option<(usize, &'input str, usize)> {
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

impl<'input> Iterator for Lexer<'input> {
    type Item = Span<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        use Tok::*;
        self.consume_whitespace()?;
        let start_pos = self.pos;

        // First try to tokenize as a keyword
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
