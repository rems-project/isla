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

use lexgen::lexer;
use lexgen_util::LexerError;
use std::fmt;

use crate::lexer::*;

#[derive(Clone, Debug)]
pub enum Tok<'input> {
    Nat(&'input str),
    Id(&'input str),
    Cap(&'input str),
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
    OpIsEmpty,
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

lexer! {
    pub Lexer -> Tok<'input>;

    let id_start = ['a'-'z' 'A'-'Z' '_'];
    let id_continue = $id_start | ['0'-'9'];
    let bitvector_start = ['0' '#'];
    let hex_char = ['0'-'9' 'a'-'f' 'A'-'F'];
    let bin_char = ['0' '1'];
    let hex_literal = $bitvector_start 'x' $hex_char*;
    let bin_literal = $bitvector_start 'b' $bin_char*;
    let cap_literal = $bitvector_start 'c' $bin_char $hex_char*;

    rule Init {
        $$whitespace,

        "::<" = Tok::TurboFish,
        "`" = Tok::Backtick,
        ">" = Tok::Gt,
        "()" = Tok::Unit,
        "->" = Tok::Arrow,
        "&" = Tok::Amp,
        "(" = Tok::Lparen,
        ")" = Tok::Rparen,
        "{" = Tok::Lbrace,
        "}" = Tok::Rbrace,
        "[" = Tok::Lsquare,
        "]" = Tok::Rsquare,
        "." = Tok::Dot,
        "*" = Tok::Star,
        ":" = Tok::Colon,
        "=" = Tok::Eq,
        "," = Tok::Comma,
        ";" = Tok::Semi,
        "$" = Tok::Dollar,
        "bitzero" = Tok::Bitzero,
        "bitone" = Tok::Bitone,
        "-" = Tok::Minus,
        "struct" = Tok::Struct,
        "is" = Tok::Is,
        "as" = Tok::As,
        "jump" = Tok::Jump,
        "goto" = Tok::Goto,
        "mono" = Tok::Mono,
        "exit" = Tok::Exit,
        "abstract" = Tok::Abstract,
        "arbitrary" = Tok::Arbitrary,
        "undefined" = Tok::Undefined,
        "end" = Tok::End,
        "register" = Tok::Register,
        "fn" = Tok::Fn,
        "let" = Tok::Let,
        "enum" = Tok::Enum,
        "union" = Tok::Union,
        "val" = Tok::Val,
        "%unit" = Tok::TyUnit,
        "%bool" = Tok::TyBool,
        "%bit" = Tok::TyBit,
        "%string" = Tok::TyString,
        "%real" = Tok::TyReal,
        "%enum" = Tok::TyEnum,
        "%struct" = Tok::TyStruct,
        "%union" = Tok::TyUnion,
        "%vec" = Tok::TyVec,
        "%fvec" = Tok::TyFVec,
        "%list" = Tok::TyList,
        "%bv" = Tok::TyBv,
        "%i" = Tok::TyI,
        "%f" = Tok::TyF,
        "%rounding_mode" = Tok::TyRoundingMode,
        "@slice" = Tok::OpSlice,
        "@set_slice" = Tok::OpSetSlice,
        "@concat" = Tok::OpConcat,
        "@unsigned" = Tok::OpUnsigned,
        "@signed" = Tok::OpSigned,
        "@not" = Tok::OpNot,
        "@or" = Tok::OpOr,
        "@and" = Tok::OpAnd,
        "@eq" = Tok::OpEq,
        "@neq" = Tok::OpNeq,
        "@bvnot" = Tok::OpBvnot,
        "@bvor" = Tok::OpBvor,
        "@bvxor" = Tok::OpBvor,
        "@bvand" = Tok::OpBvand,
        "@bvadd" = Tok::OpBvadd,
        "@bvsub" = Tok::OpBvsub,
        "@bvaccess" = Tok::OpBvaccess,
        "@lteq" = Tok::OpLteq,
        "@lt" = Tok::OpLt,
        "@gteq" = Tok::OpGteq,
        "@gt" = Tok::OpGt,
        "@hd" = Tok::OpHead,
        "@tl" = Tok::OpTail,
        "@is_empty" = Tok::OpIsEmpty,
        "@iadd" = Tok::OpAdd,
        "@isub" = Tok::OpSub,
        "@zero_extend" = Tok::OpZeroExtend,
        "bitzero" = Tok::Bitzero,
        "bitone" = Tok::Bitone,
        "true" = Tok::True,
        "false" = Tok::False,
        "UINT64_C(0)" = Tok::EmptyBitvec,
        "files" = Tok::Files,

        $id_start $id_continue* => |lexer| {
            let id = lexer.match_();
            lexer.return_(Tok::Id(id))
        },

        $hex_literal => |lexer| {
            let hex = lexer.match_();
            lexer.return_(Tok::Hex(hex))
        },

        $bin_literal => |lexer| {
            let bin = lexer.match_();
            lexer.return_(Tok::Bin(bin))
        },

        $cap_literal => |lexer| {
            let cap = lexer.match_();
            lexer.return_(Tok::Cap(cap))
        },

        ['0'-'9']+ => |lexer| {
            let nat = lexer.match_();
            lexer.return_(Tok::Nat(nat))
        },

        '#' $id_start $id_continue* $$whitespace (_ # '\n')* '\n' => |lexer| {
            let pragma_line = &lexer.match_()[1..];
            let (pragma, args) = pragma_line.split_once(char::is_whitespace).unwrap();
            lexer.return_(Tok::Pragma(pragma, args.trim()))
        },

        '"' => |lexer| lexer.switch(LexerRule::String),
    }

    rule String {
        "\\\"" => |lexer| lexer.continue_(),

        '"' => |lexer| {
            let s = lexer.match_();
            let s = s.strip_prefix('"').unwrap().strip_suffix('"').unwrap();
            lexer.switch_and_return(LexerRule::Init, Tok::String(s))
        },

        _ => |lexer| lexer.continue_(),
    }
}

pub type Span<'input> = Result<(usize, Tok<'input>, usize), LexError>;

pub fn new_ir_lexer(input: &str) -> impl Iterator<Item = Span<'_>> {
    let lexer = Lexer::new(input);
    lexer.into_iter().map(|act| match act {
        Ok((s, tok, e)) => Ok((s.byte_idx, tok, e.byte_idx)),
        Err(LexerError { location, .. }) => Err(LexError { pos: location.byte_idx }),
    })
}
