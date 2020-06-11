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

use crate::lexer::*;

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
    OpSetSlice,
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
    OpAdd,
    OpSub,
    OpLteq,
    OpLt,
    OpGteq,
    OpGt,
    OpHead,
    OpTail,
    TyI,
    TyBv,
    TyUnit,
    TyBool,
    TyBit,
    TyString,
    TyReal,
    TyEnum,
    TyStruct,
    TyUnion,
    TyVec,
    TyFVec,
    TyList,
    TurboFish,
    Backtick,
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
    Undefined,
    End,
    Register,
    Fn,
    Let,
    Enum,
    Union,
    Val,
    True,
    False,
    EmptyBitvec,
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
        table.push(Keyword::new("::<", TurboFish));
        table.push(Keyword::new("`", Backtick));
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
        table.push(Keyword::new("undefined", Undefined));
        table.push(Keyword::new("end", End));
        table.push(Keyword::new("register", Register));
        table.push(Keyword::new("fn", Fn));
        table.push(Keyword::new("let", Let));
        table.push(Keyword::new("enum", Enum));
        table.push(Keyword::new("union", Union));
        table.push(Keyword::new("val", Val));
        table.push(Keyword::new("%i", TyI));
        table.push(Keyword::new("%unit", TyUnit));
        table.push(Keyword::new("%bool", TyBool));
        table.push(Keyword::new("%bit", TyBit));
        table.push(Keyword::new("%string", TyString));
        table.push(Keyword::new("%real", TyReal));
        table.push(Keyword::new("%enum", TyEnum));
        table.push(Keyword::new("%struct", TyStruct));
        table.push(Keyword::new("%union", TyUnion));
        table.push(Keyword::new("%vec", TyVec));
        table.push(Keyword::new("%fvec", TyFVec));
        table.push(Keyword::new("%list", TyList));
        table.push(Keyword::new("%bv", TyBv));
        table.push(Keyword::new("@slice", OpSlice));
        table.push(Keyword::new("@set_slice", OpSetSlice));
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
        table.push(Keyword::new("@lteq", OpLteq));
        table.push(Keyword::new("@lt", OpLt));
        table.push(Keyword::new("@gteq", OpGteq));
        table.push(Keyword::new("@gt", OpGt));
        table.push(Keyword::new("@hd", OpHead));
        table.push(Keyword::new("@tl", OpTail));
        table.push(Keyword::new("@iadd", OpAdd));
        table.push(Keyword::new("@isub", OpSub));
        table.push(Keyword::new("bitzero", Bitzero));
        table.push(Keyword::new("bitone", Bitone));
        table.push(Keyword::new("true", True));
        table.push(Keyword::new("false", False));
        table.push(Keyword::new("UINT64_C(0)", EmptyBitvec));
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
