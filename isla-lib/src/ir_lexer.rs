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

use regex::Regex;
use std::fmt;

use crate::lexer::*;

lazy_static! {
    pub static ref PRAGMA_REGEX: Regex = Regex::new(r"^#[a-zA-Z_][0-9a-zA-Z_]*").unwrap();
}

#[derive(Clone, Debug)]
pub enum Tok<'input> {
    Nat(&'input str),
    Id(&'input str),
    String(&'input str),
    Hex(&'input str),
    Bin(&'input str),
    Pragma(&'input str, &'input str),
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
    OpZeroExtend,
    TyI,
    TyF,
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
    TyRoundingMode,
    TurboFish,
    Backtick,
    Gt,
    Amp,
    Lparen,
    Rparen,
    Lbrace,
    Rbrace,
    Lsquare,
    Rsquare,
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
    Abstract,
    As,
    Jump,
    Goto,
    Mono,
    Exit,
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
    Files,
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
        vec![
            Keyword::new("::<", TurboFish),
            Keyword::new("`", Backtick),
            Keyword::new(">", Gt),
            Keyword::new("()", Unit),
            Keyword::new("->", Arrow),
            Keyword::new("&", Amp),
            Keyword::new("(", Lparen),
            Keyword::new(")", Rparen),
            Keyword::new("{", Lbrace),
            Keyword::new("}", Rbrace),
            Keyword::new("[", Lsquare),
            Keyword::new("]", Rsquare),
            Keyword::new(".", Dot),
            Keyword::new("*", Star),
            Keyword::new(":", Colon),
            Keyword::new("=", Eq),
            Keyword::new(",", Comma),
            Keyword::new(";", Semi),
            Keyword::new("$", Dollar),
            Keyword::new("bitzero", Bitzero),
            Keyword::new("bitone", Bitone),
            Keyword::new("-", Minus),
            Keyword::new("struct", Struct),
            Keyword::new("is", Is),
            Keyword::new("as", As),
            Keyword::new("jump", Jump),
            Keyword::new("goto", Goto),
            Keyword::new("mono", Mono),
            Keyword::new("exit", Exit),
            Keyword::new("abstract", Abstract),
            Keyword::new("arbitrary", Arbitrary),
            Keyword::new("undefined", Undefined),
            Keyword::new("end", End),
            Keyword::new("register", Register),
            Keyword::new("fn", Fn),
            Keyword::new("let", Let),
            Keyword::new("enum", Enum),
            Keyword::new("union", Union),
            Keyword::new("val", Val),
            Keyword::new("%unit", TyUnit),
            Keyword::new("%bool", TyBool),
            Keyword::new("%bit", TyBit),
            Keyword::new("%string", TyString),
            Keyword::new("%real", TyReal),
            Keyword::new("%enum", TyEnum),
            Keyword::new("%struct", TyStruct),
            Keyword::new("%union", TyUnion),
            Keyword::new("%vec", TyVec),
            Keyword::new("%fvec", TyFVec),
            Keyword::new("%list", TyList),
            Keyword::new("%bv", TyBv),
            Keyword::new("%i", TyI),
            Keyword::new("%f", TyF),
            Keyword::new("%rounding_mode", TyRoundingMode),
            Keyword::new("@slice", OpSlice),
            Keyword::new("@set_slice", OpSetSlice),
            Keyword::new("@concat", OpConcat),
            Keyword::new("@unsigned", OpUnsigned),
            Keyword::new("@signed", OpSigned),
            Keyword::new("@not", OpNot),
            Keyword::new("@or", OpOr),
            Keyword::new("@and", OpAnd),
            Keyword::new("@eq", OpEq),
            Keyword::new("@neq", OpNeq),
            Keyword::new("@bvnot", OpBvnot),
            Keyword::new("@bvor", OpBvor),
            Keyword::new("@bvxor", OpBvor),
            Keyword::new("@bvand", OpBvand),
            Keyword::new("@bvadd", OpBvadd),
            Keyword::new("@bvsub", OpBvsub),
            Keyword::new("@bvaccess", OpBvaccess),
            Keyword::new("@lteq", OpLteq),
            Keyword::new("@lt", OpLt),
            Keyword::new("@gteq", OpGteq),
            Keyword::new("@gt", OpGt),
            Keyword::new("@hd", OpHead),
            Keyword::new("@tl", OpTail),
            Keyword::new("@iadd", OpAdd),
            Keyword::new("@isub", OpSub),
            Keyword::new("@zero_extend", OpZeroExtend),
            Keyword::new("bitzero", Bitzero),
            Keyword::new("bitone", Bitone),
            Keyword::new("true", True),
            Keyword::new("false", False),
            Keyword::new("UINT64_C(0)", EmptyBitvec),
            Keyword::new("files", Files),
        ]
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
            Some((from, bits, to)) => return Some(Ok((from, Hex(bits), to))),
        }

        match self.consume_regex(&BIN_REGEX) {
            None => (),
            Some((from, bits, to)) => return Some(Ok((from, Bin(bits), to))),
        }

        match self.consume_regex(&NAT_REGEX) {
            None => (),
            Some((from, n, to)) => return Some(Ok((from, Nat(n), to))),
        }

        match self.consume_string_literal() {
            None => (),
            Some((from, s, to)) => return Some(Ok((from, String(s), to))),
        }

        match self.consume_regex(&PRAGMA_REGEX) {
            None => (),
            Some((from, name, _)) => match self.consume_to_newline() {
                None => return Some(Err(LexError { pos: self.pos })),
                Some((_, args, to)) => return Some(Ok((from, Pragma(&name[1..], args.trim()), to))),
            },
        }

        Some(Err(LexError { pos: self.pos }))
    }
}
