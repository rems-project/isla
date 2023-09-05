// BSD 2-Clause License
//
// Copyright (c) 2022 Alasdair Armstrong
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

use isla_lib::lexer::{BIN_REGEX, HEX_REGEX, NAT_REGEX};

use crate::memory_model::ModelParseError;

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

    pub fn consume_string_literal(&mut self) -> Option<(usize, &'input str, usize)> {
        if self.buf.chars().next()? == '\"' {
            let mut string_end = 1;
            loop {
                if let '\"' = self.buf.chars().nth(string_end)? {
                    let contents = &self.buf[1..string_end];
                    let start_pos = self.pos;
                    self.pos += string_end + 1;
                    self.buf = &self.buf[(string_end + 1)..];
                    break Some((start_pos, contents, self.pos));
                }
                string_end += 1
            }
        } else {
            None
        }
    }

    pub fn consume_comment(&mut self) -> bool {
        loop {
            if self.buf.is_empty() {
                break false;
            } else if self.buf.starts_with("*)") {
                self.pos += 2;
                self.buf = &self.buf[2..];
                break true;
            } else {
                self.pos += 1;
                self.buf = &self.buf[1..];
            }
        }
    }

    pub fn consume_line_comment(&mut self) {
        loop {
            match self.buf.chars().next() {
                Some(c) if c == '\n' => {
                    self.pos += 1;
                    self.buf = &self.buf[1..];
                    break;
                }
                Some(c) => {
                    let len = c.len_utf8();
                    self.pos += len;
                    self.buf = &self.buf[len..];
                }
                None => (),
            }
        }
    }
}

macro_rules! lex_regex {
    ($lexer: ident, $token: path, $regex: expr) => {
        match $lexer.consume_regex(&$regex) {
            None => (),
            Some((from, id, to)) => return Some(Ok((from, $token(id), to))),
        }
    };
}

macro_rules! lex_keyword {
    ($lexer: ident, $keyword: expr) => {
        if $lexer.buf.starts_with($keyword.word) {
            match $lexer.buf.chars().nth($keyword.len) {
                // A keyword cannot be immediately followed by any valid identifier characters
                Some(c) if c.is_ascii_alphanumeric() || c == '.' || c == '_' || c == '-' => (),
                _ => {
                    let start_pos = $lexer.pos;
                    $lexer.pos += $keyword.len;
                    $lexer.buf = &$lexer.buf[$keyword.len..];
                    return Some(Ok((start_pos, $keyword.token.clone(), $lexer.pos)));
                }
            }
        }
    };
}

macro_rules! lex_char {
    ($lexer: ident, $next: ident, $token: path, $char: expr) => {
        if $next == $char {
            let start_pos = $lexer.pos;
            $lexer.pos += 1;
            $lexer.buf = &$lexer.buf[1..];
            return Some(Ok((start_pos, $token.clone(), $lexer.pos)));
        }
    };
}

#[derive(Clone, Debug)]
pub enum Tok<'input> {
    Nat(&'input str),
    FixedNat(&'input str),
    Id(&'input str),
    String(&'input str),
    Bin(&'input str),
    Hex(&'input str),
    // Keywords
    Accessor,
    Acyclic,
    Address,
    Amp,
    And,
    As,
    Assert,
    Backslash,
    Bar,
    Colon,
    Comma,
    Data,
    Declare,
    Define,
    Dot,
    DotDot,
    Else,
    Empty,
    Eq,
    EqEq,
    EqGt,
    Equals,
    Exists,
    Exts,
    Extz,
    Flag,
    Forall,
    HatPlus,
    HatStar,
    If,
    Implies,
    In,
    Include,
    Index,
    Inverse,
    Irreflexive,
    Is,
    Length,
    Let,
    Match,
    Neq,
    Opcode,
    Plus,
    PlusPlus,
    Question,
    Relation,
    Return,
    SemiColon,
    Set,
    Show,
    Star,
    Then,
    Tilde,
    Underscore,
    Unshow,
    Variant,
    Where,
    Zero,
    // Brackets
    Lparen,
    Rparen,
    Lbrace,
    Rbrace,
    Lsquare,
    Rsquare,
}

impl<'input> fmt::Display for Tok<'input> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Tok::*;
        match self {
            Nat(n) => write!(f, "{}", n),
            FixedNat(n) => write!(f, "{}", n),
            Id(id) => write!(f, "identifier {}", id),
            String(s) => write!(f, "\"{}\"", s),
            Bin(b) => write!(f, "{}", b),
            Hex(h) => write!(f, "{}", h),
            Accessor => write!(f, "accessor"),
            Acyclic => write!(f, "acyclic"),
            Address => write!(f, "address"),
            Amp => write!(f, "&"),
            And => write!(f, "and"),
            As => write!(f, "as"),
            Assert => write!(f, "assert"),
            Backslash => write!(f, "\\"),
            Bar => write!(f, "|"),
            Colon => write!(f, ":"),
            Comma => write!(f, ","),
            Data => write!(f, "data"),
            Declare => write!(f, "declare"),
            Define => write!(f, "define"),
            Dot => write!(f, "."),
            DotDot => write!(f, ".."),
            Else => write!(f, "else"),
            Empty => write!(f, "empty"),
            Eq => write!(f, "="),
            EqEq => write!(f, "=="),
            EqGt => write!(f, "=>"),
            Equals => write!(f, "equals"),
            Exists => write!(f, "exists"),
            Exts => write!(f, "exts"),
            Extz => write!(f, "extz"),
            Flag => write!(f, "flag"),
            Forall => write!(f, "forall"),
            HatPlus => write!(f, "^+"),
            HatStar => write!(f, "^*"),
            Implies => write!(f, "-->"),
            If => write!(f, "if"),
            In => write!(f, "in"),
            Include => write!(f, "include"),
            Index => write!(f, "index"),
            Inverse => write!(f, "^-1"),
            Irreflexive => write!(f, "irreflexive"),
            Is => write!(f, "is"),
            Length => write!(f, "length"),
            Let => write!(f, "let"),
            Match => write!(f, "match"),
            Neq => write!(f, "!="),
            Opcode => write!(f, "opcode"),
            Plus => write!(f, "+"),
            PlusPlus => write!(f, "++"),
            Question => write!(f, "?"),
            Relation => write!(f, "relation"),
            Return => write!(f, "return"),
            SemiColon => write!(f, ";"),
            Set => write!(f, "set"),
            Show => write!(f, "show"),
            Star => write!(f, "*"),
            Then => write!(f, "then"),
            Tilde => write!(f, "~"),
            Underscore => write!(f, "_"),
            Unshow => write!(f, "unshow"),
            Variant => write!(f, "variant"),
            Where => write!(f, "where"),
            Zero => write!(f, "zero"),
            Lparen => write!(f, "("),
            Rparen => write!(f, ")"),
            Lbrace => write!(f, "{{"),
            Rbrace => write!(f, "}}"),
            Lsquare => write!(f, "["),
            Rsquare => write!(f, "]"),
        }
    }
}

lazy_static! {
    pub static ref ID_REGEX: Regex = Regex::new(r"^[a-zA-Z_][0-9a-zA-Z_-]*").unwrap();
    pub static ref FIXED_NAT_REGEX: Regex = Regex::new(r"^[1-9][0-9]*i[1-9][0-9]*").unwrap();
    pub static ref KW_ACCESSOR: Keyword = Keyword::new("accessor", Tok::Accessor);
    pub static ref KW_ACYCLIC: Keyword = Keyword::new("acyclic", Tok::Acyclic);
    pub static ref KW_ADDRESS: Keyword = Keyword::new("address", Tok::Address);
    pub static ref KW_AND: Keyword = Keyword::new("and", Tok::And);
    pub static ref KW_AS: Keyword = Keyword::new("as", Tok::As);
    pub static ref KW_ASSERT: Keyword = Keyword::new("assert", Tok::Assert);
    pub static ref KW_DATA: Keyword = Keyword::new("data", Tok::Data);
    pub static ref KW_DECLARE: Keyword = Keyword::new("declare", Tok::Declare);
    pub static ref KW_DEFINE: Keyword = Keyword::new("define", Tok::Define);
    pub static ref KW_DOT_DOT: Keyword = Keyword::new("..", Tok::DotDot);
    pub static ref KW_ELSE: Keyword = Keyword::new("else", Tok::Else);
    pub static ref KW_EMPTY: Keyword = Keyword::new("empty", Tok::Empty);
    pub static ref KW_EQ_EQ: Keyword = Keyword::new("==", Tok::EqEq);
    pub static ref KW_EQ_GT: Keyword = Keyword::new("=>", Tok::EqGt);
    pub static ref KW_EQUALS: Keyword = Keyword::new("equals", Tok::Equals);
    pub static ref KW_EXISTS: Keyword = Keyword::new("exists", Tok::Exists);
    pub static ref KW_EXTS: Keyword = Keyword::new("exts", Tok::Exts);
    pub static ref KW_EXTZ: Keyword = Keyword::new("extz", Tok::Extz);
    pub static ref KW_FLAG: Keyword = Keyword::new("flag", Tok::Flag);
    pub static ref KW_FORALL: Keyword = Keyword::new("forall", Tok::Forall);
    pub static ref KW_HATPLUS: Keyword = Keyword::new("^+", Tok::HatPlus);
    pub static ref KW_HATSTAR: Keyword = Keyword::new("^*", Tok::HatStar);
    pub static ref KW_IMPLIES: Keyword = Keyword::new("-->", Tok::Implies);
    pub static ref KW_IN: Keyword = Keyword::new("in", Tok::In);
    pub static ref KW_INCLUDE: Keyword = Keyword::new("include", Tok::Include);
    pub static ref KW_INDEX: Keyword = Keyword::new("index", Tok::Index);
    pub static ref KW_INVERSE: Keyword = Keyword::new("^-1", Tok::Inverse);
    pub static ref KW_IRREFLEXIVE: Keyword = Keyword::new("irreflexive", Tok::Irreflexive);
    pub static ref KW_IF: Keyword = Keyword::new("if", Tok::If);
    pub static ref KW_IS: Keyword = Keyword::new("is", Tok::Is);
    pub static ref KW_LENGTH: Keyword = Keyword::new("length", Tok::Length);
    pub static ref KW_LET: Keyword = Keyword::new("let", Tok::Let);
    pub static ref KW_MATCH: Keyword = Keyword::new("match", Tok::Match);
    pub static ref KW_NEQ: Keyword = Keyword::new("!=", Tok::Neq);
    pub static ref KW_OPCODE: Keyword = Keyword::new("opcode", Tok::Opcode);
    pub static ref KW_PLUS_PLUS: Keyword = Keyword::new("++", Tok::PlusPlus);
    pub static ref KW_RELATION: Keyword = Keyword::new("relation", Tok::Relation);
    pub static ref KW_RETURN: Keyword = Keyword::new("return", Tok::Return);
    pub static ref KW_SET: Keyword = Keyword::new("set", Tok::Set);
    pub static ref KW_SHOW: Keyword = Keyword::new("show", Tok::Show);
    pub static ref KW_THEN: Keyword = Keyword::new("then", Tok::Then);
    pub static ref KW_UNSHOW: Keyword = Keyword::new("unshow", Tok::Unshow);
    pub static ref KW_VARIANT: Keyword = Keyword::new("variant", Tok::Variant);
    pub static ref KW_WHERE: Keyword = Keyword::new("where", Tok::Where);
}

pub type Span<'input> = Result<(usize, Tok<'input>, usize), ModelParseError>;

impl<'input> Iterator for Lexer<'input> {
    type Item = Span<'input>;

    #[allow(clippy::cognitive_complexity)]
    fn next(&mut self) -> Option<Self::Item> {
        use Tok::*;
        self.consume_whitespace()?;

        let next = self.buf.chars().next()?;

        if next == 'a' {
            lex_keyword!(self, KW_ACCESSOR);
            lex_keyword!(self, KW_ACYCLIC);
            lex_keyword!(self, KW_ASSERT);
            lex_keyword!(self, KW_AS);
            lex_keyword!(self, KW_AND);
            lex_keyword!(self, KW_ADDRESS);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'd' {
            lex_keyword!(self, KW_DATA);
            lex_keyword!(self, KW_DECLARE);
            lex_keyword!(self, KW_DEFINE);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'e' {
            lex_keyword!(self, KW_ELSE);
            lex_keyword!(self, KW_EMPTY);
            lex_keyword!(self, KW_EQUALS);
            lex_keyword!(self, KW_EXISTS);
            lex_keyword!(self, KW_EXTZ);
            lex_keyword!(self, KW_EXTS);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'f' {
            lex_keyword!(self, KW_FLAG);
            lex_keyword!(self, KW_FORALL);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'i' {
            lex_keyword!(self, KW_IF);
            lex_keyword!(self, KW_INCLUDE);
            lex_keyword!(self, KW_INDEX);
            lex_keyword!(self, KW_IN);
            lex_keyword!(self, KW_IRREFLEXIVE);
            lex_keyword!(self, KW_IS);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'l' {
            lex_keyword!(self, KW_LET);
            lex_keyword!(self, KW_LENGTH);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'o' {
            lex_keyword!(self, KW_OPCODE);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'm' {
            lex_keyword!(self, KW_MATCH);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'r' {
            lex_keyword!(self, KW_RELATION);
            lex_keyword!(self, KW_RETURN);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 's' {
            lex_keyword!(self, KW_SHOW);
            lex_keyword!(self, KW_SET);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 't' {
            lex_keyword!(self, KW_THEN);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'u' {
            lex_keyword!(self, KW_UNSHOW);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'v' {
            lex_keyword!(self, KW_VARIANT);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == 'w' {
            lex_keyword!(self, KW_WHERE);
            lex_regex!(self, Id, ID_REGEX)
        } else if next == '-' {
            lex_keyword!(self, KW_IMPLIES)
        } else if next == '+' {
            lex_keyword!(self, KW_PLUS_PLUS);
            lex_char!(self, next, Tok::Plus, '+')
        } else if next == '^' {
            lex_keyword!(self, KW_INVERSE);
            lex_keyword!(self, KW_HATPLUS);
            lex_keyword!(self, KW_HATSTAR);
        } else if next == '"' {
            match self.consume_string_literal() {
                None => (),
                Some((from, s, to)) => {
                    return Some(Ok((from, String(s), to)));
                }
            }
        } else if next == '#' {
            self.consume_line_comment();
            return self.next();
        } else if next == '0' {
            lex_regex!(self, Hex, HEX_REGEX);
            lex_regex!(self, Bin, BIN_REGEX);
            lex_regex!(self, Nat, NAT_REGEX)
        } else if next.is_ascii_digit() {
            lex_regex!(self, FixedNat, FIXED_NAT_REGEX);
            lex_regex!(self, Nat, NAT_REGEX)
        } else if next == '(' {
            if let Some('*') = self.buf.chars().nth(1) {
                if self.consume_comment() {
                    return self.next();
                }
            } else {
                lex_char!(self, next, Tok::Lparen, '(');
            }
        } else if next == '!' {
            lex_keyword!(self, KW_NEQ);
        } else if next == '=' {
            lex_keyword!(self, KW_EQ_EQ);
            lex_keyword!(self, KW_EQ_GT);
            lex_char!(self, next, Tok::Eq, '=');
        } else if next == '.' {
            lex_keyword!(self, KW_DOT_DOT);
            lex_char!(self, next, Tok::Dot, '.')
        } else {
            lex_char!(self, next, Tok::Eq, '=');
            lex_char!(self, next, Tok::Rparen, ')');
            lex_char!(self, next, Tok::Lbrace, '{');
            lex_char!(self, next, Tok::Rbrace, '}');
            lex_char!(self, next, Tok::Lbrace, '{');
            lex_char!(self, next, Tok::Rbrace, '}');
            lex_char!(self, next, Tok::Lsquare, '[');
            lex_char!(self, next, Tok::Rsquare, ']');
            lex_char!(self, next, Tok::Tilde, '~');
            lex_char!(self, next, Tok::Bar, '|');
            lex_char!(self, next, Tok::Bar, '∪');
            lex_char!(self, next, Tok::Amp, '&');
            lex_char!(self, next, Tok::Amp, '∩');
            lex_char!(self, next, Tok::Star, '*');
            lex_char!(self, next, Tok::Star, '×');
            lex_char!(self, next, Tok::SemiColon, ';');
            lex_char!(self, next, Tok::Comma, ',');
            lex_char!(self, next, Tok::Backslash, '\\');
            lex_char!(self, next, Tok::Zero, '0');
            lex_char!(self, next, Tok::Question, '?');
            lex_char!(self, next, Tok::Colon, ':');
            lex_char!(self, next, Tok::Underscore, '_');
            lex_regex!(self, Id, ID_REGEX)
        }

        Some(Err(ModelParseError::Lex { pos: self.pos }))
    }
}
