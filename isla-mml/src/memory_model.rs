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

use id_arena::{Arena, Id};
use lalrpop_util::ParseError;
use std::borrow::Cow;
use std::collections::HashMap;
use std::io::Write;
use std::num::ParseIntError;
use std::ops::Index;

use isla_lib::simplify::write_bits_prefix;
use isla_lib::zencode;
use isla_lib::source_loc::SourceLoc;

use crate::lexer;
use crate::parser;

/// This type is fundamentally the same as its namesake in the isla
/// IR, but we keep it separate to A) maintain the distinction between
/// memory model identifiers and IR identifiers, and B) allow a
/// different set of constants for this Name type (see the constants
/// module).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name {
    id: u32,
}

impl Name {
    pub fn from_u32(id: u32) -> Self {
        Name { id }
    }
}

pub mod constants {
    //! This module declares various constant symbols used in
    //! SMTLIB S-expressions and memory model language.

    use super::Name;

    #[derive(Copy, Clone, Debug)]
    pub struct Constant {
        id: u32,
        symbol: &'static str,
    }

    impl Constant {
        pub fn name(self) -> Name {
            Name { id: self.id }
        }

        pub fn to_str(self) -> &'static str {
            self.symbol
        }
    }

    pub const DECLARE_CONST: Constant = Constant { id: 0, symbol: "declare-const" };
    pub const DECLARE_FUN: Constant = Constant { id: 1, symbol: "declare-fun" };
    pub const DEFINE_FUN: Constant = Constant { id: 2, symbol: "define-fun" };
    pub const ASSERT: Constant = Constant { id: 3, symbol: "assert" };
    pub const TRUE: Constant = Constant { id: 4, symbol: "true" };
    pub const FALSE: Constant = Constant { id: 5, symbol: "false" };
    pub const AND: Constant = Constant { id: 6, symbol: "and" };
    pub const OR: Constant = Constant { id: 7, symbol: "or" };
    pub const NOT: Constant = Constant { id: 8, symbol: "not" };
    pub const FORALL: Constant = Constant { id: 9, symbol: "forall" };
    pub const EXISTS: Constant = Constant { id: 10, symbol: "exists" };
    pub const EVENT: Constant = Constant { id: 11, symbol: "Event" };
    pub const EQ: Constant = Constant { id: 12, symbol: "=" };
    pub const LET: Constant = Constant { id: 13, symbol: "let" };
    pub const BOOL: Constant = Constant { id: 14, symbol: "bool" };
    pub const IMPLIES: Constant = Constant { id: 15, symbol: "=>" };
    pub const ADDRESS: Constant = Constant { id: 16, symbol: "address" };
    pub const DATA: Constant = Constant { id: 17, symbol: "data" };
    pub const ITE: Constant = Constant { id: 18, symbol: "ite" };
    pub const AS: Constant = Constant { id: 19, symbol: "as" };
    pub const CONST: Constant = Constant { id: 20, symbol: "const" };
    pub const ARRAY: Constant = Constant { id: 21, symbol: "Array" };
    pub const EXCLAMATION: Constant = Constant { id: 22, symbol: "!" };
    pub const NAMED: Constant = Constant { id: 23, symbol: ":named" };
}

#[derive(Clone)]
pub struct Symtab<'input> {
    symbols: Vec<Cow<'input, str>>,
    table: HashMap<Cow<'input, str>, u32>,
    next: u32,
}

impl<'input> Index<Name> for Symtab<'input> {
    type Output = Cow<'input, str>;

    fn index(&self, n: Name) -> &Self::Output {
        &self.symbols[n.id as usize]
    }
}

impl<'input> Symtab<'input> {
    pub fn new() -> Self {
        use constants::*;

        let mut symtab = Symtab { symbols: Vec::new(), table: HashMap::new(), next: 0 };
        symtab.intern_constant(DECLARE_CONST);
        symtab.intern_constant(DECLARE_FUN);
        symtab.intern_constant(DEFINE_FUN);
        symtab.intern_constant(ASSERT);
        symtab.intern_constant(TRUE);
        symtab.intern_constant(FALSE);
        symtab.intern_constant(AND);
        symtab.intern_constant(OR);
        symtab.intern_constant(NOT);
        symtab.intern_constant(FORALL);
        symtab.intern_constant(EXISTS);
        symtab.intern_constant(EVENT);
        symtab.intern_constant(EQ);
        symtab.intern_constant(LET);
        symtab.intern_constant(BOOL);
        symtab.intern_constant(IMPLIES);
        symtab.intern_constant(ADDRESS);
        symtab.intern_constant(DATA);
        symtab.intern_constant(ITE);
        symtab.intern_constant(AS);
        symtab.intern_constant(CONST);
        symtab.intern_constant(ARRAY);
        symtab.intern_constant(EXCLAMATION);
        symtab.intern_constant(NAMED);
        symtab
    }

    pub fn get(&self, n: Name) -> Option<&Cow<'input, str>> {
        self.symbols.get(n.id as usize)
    }

    pub fn intern(&mut self, sym: &'input str) -> Name {
        match self.table.get(sym) {
            None => {
                let n = self.next;
                self.symbols.push(Cow::Borrowed(sym));
                self.table.insert(Cow::Borrowed(sym), n);
                self.next += 1;
                Name::from_u32(n)
            }
            Some(n) => Name::from_u32(*n),
        }
    }

    pub fn lookup(&self, sym: &str) -> Option<Name> {
        match self.table.get(sym) {
            Some(n) => Some(Name::from_u32(*n)),
            None => None,
        }
    }

    // This will throw an error at runtime if we attempt to intern a
    // constant in the wrong place in the symbol table
    fn intern_constant(&mut self, constant: constants::Constant) -> Name {
        let name = self.intern(constant.to_str());
        assert!(name == constant.name());
        name
    }

    pub fn intern_owned(&mut self, sym: String) -> Name {
        match self.table.get(sym.as_str()) {
            None => {
                let n = self.next;
                self.symbols.push(Cow::Owned(sym.clone()));
                self.table.insert(Cow::Owned(sym), n);
                self.next += 1;
                Name::from_u32(n)
            }
            Some(n) => Name::from_u32(*n),
        }
    }

    pub fn encode_accessors(&mut self, accessors: &[Accessor]) -> Name {
        let mut encoding = b"acc".to_vec();
        let mut need_sep = false;
        for a in accessors {
            if need_sep {
                write!(&mut encoding, "-").unwrap();
                need_sep = false
            }
            match a {
                Accessor::Extz(n) => write!(&mut encoding, "z{}", n).unwrap(),
                Accessor::Exts(n) => write!(&mut encoding, "s{}", n).unwrap(),
                Accessor::Subvec(hi, lo) => write!(&mut encoding, "h{}l{}", hi, lo).unwrap(),
                Accessor::Bits(bv) => {
                    write_bits_prefix(&mut encoding, "", true, bv).unwrap();
                    need_sep = true
                }
                Accessor::Field(id) => {
                    write!(&mut encoding, "f{}", zencode::encode(&self[*id])).unwrap();
                    need_sep = true
                }
                Accessor::Ctor(id) => {
                    write!(&mut encoding, "c{}", zencode::encode(&self[*id])).unwrap();
                    need_sep = true
                }
                Accessor::Wildcard => write!(&mut encoding, "w").unwrap(),
                Accessor::Match(n) => write!(&mut encoding, "m{}", n).unwrap(),
                Accessor::Tuple(n) => write!(&mut encoding, "t{}", n).unwrap(),
                Accessor::Length(n) => write!(&mut encoding, "n{}", n).unwrap(),
                Accessor::Address => write!(&mut encoding, "a").unwrap(),
                Accessor::Data => write!(&mut encoding, "d").unwrap(),
            }
        }
        self.intern_owned(String::from_utf8(encoding).unwrap())
    }
}

pub struct Spanned<T> {
    pub node: T,
    pub span: (usize, usize),
}

pub struct Error {
    pub message: String,
    pub span: (usize, usize),
}

/// Convert a span (which is a character offset pair) into a Isla source location
pub fn span_to_source_loc(span: (usize, usize), file_id: i16, contents: &str) -> SourceLoc {
    let mut seen: usize = 0;
    let mut lines: u32 = 1;

    let mut first = true;

    let mut line1: u32 = 0;
    let mut char1: u16 = 0;
    let mut line2: u32 = 0;
    let mut char2: u16 = 0;

    for line in contents.lines() {
        let len = line.len() + 1;
        if (if first { span.0 } else { span.1 }) <= seen + len {
            if first {
                line1 = lines;
                char1 = (span.0 - seen) as u16;
                first = false;
                if span.1 <= seen + len {
                    line2 = lines;
                    char2 = (span.1 - seen) as u16;
                    break;
                }
            } else {
                line2 = lines;
                char2 = (span.1 - seen) as u16;
                break;
            }
        }
        lines += 1;
        seen += len
    }

    SourceLoc::new(file_id, line1, char1, line2, char2)
}

pub type ExpId = Id<Spanned<Exp>>;

pub struct ExpArena {
    arena: Arena<Spanned<Exp>>,
}

impl Index<ExpId> for ExpArena {
    type Output = Spanned<Exp>;

    fn index(&self, i: ExpId) -> &Self::Output {
        &self.arena[i]
    }
}

impl ExpArena {
    pub fn new() -> Self {
        ExpArena { arena: Arena::new() }
    }

    pub fn alloc(&mut self, exp: Spanned<Exp>) -> ExpId {
        self.arena.alloc(exp)
    }
}

pub enum Unary {
    Compl,
    IdentityUnion,
    Identity,
    Inverse,
    TClosure,
    RTClosure,
}

pub enum Binary {
    Diff,
    Inter,
    Seq,
    Union,
    In,
    Eq,
    Neq,
}

pub(crate) fn bits_from_u64(bits: u64, size: usize) -> Vec<bool> {
    let mut bitvec = vec![false; size];
    for n in 0..size {
        if n < 64 && (bits >> n & 1) == 1 {
            bitvec[n] = true
        }
    }
    bitvec
}

pub(crate) fn bits_from_str(s: &str) -> Option<Vec<bool>> {
    if let Some(hex) = s.strip_prefix("0x") {
        let size = 4 * hex.len();
        let mut value = vec![false; size];
        let mut i = size - 4;
        for c in hex.chars() {
            let mut digit = c.to_digit(16)?;
            for j in 0..4 {
                value[i + j] = digit & 1 == 1;
                digit >>= 1;
            }
            i -= 4;
        }
        Some(value)
    } else if let Some(bin) = s.strip_prefix("0b") {
        let size = bin.len();
        let mut value = vec![false; size];
        for (i, c) in bin.char_indices() {
            match c {
                '0' => (),
                '1' => value[size - i - 1] = true,
                _ => return None,
            }
        }
        Some(value)
    } else {
        None
    }
}

/// The expression type, `Exp`, represents memory model expressions
/// that will be compiled directly into the SMTLIB definitions
/// representing the memory model.
pub enum Exp {
    Empty,
    Bits(Vec<bool>),
    Tuple(Vec<ExpId>),
    Id(Name),
    App(Name, Vec<Option<ExpId>>),
    Accessor(ExpId, Vec<Accessor>),
    Unary(Unary, ExpId),
    Binary(Binary, ExpId, ExpId),
    Cartesian(Option<ExpId>, Option<ExpId>),
    Set(Name, TyAnnot, ExpId),
    Relation(Name, TyAnnot, Name, TyAnnot, ExpId),
    Forall(Vec<(Name, TyAnnot)>, ExpId),
    Exists(Vec<(Name, TyAnnot)>, ExpId),
}

impl Exp {
    fn add_accessors<'a>(
        &'a self,
        collection: &mut HashMap<Name, &'a [Accessor]>,
        exps: &'a ExpArena,
        symtab: &mut Symtab,
    ) {
        use Exp::*;
        match self {
            Accessor(exp, accs) => {
                exps[*exp].node.add_accessors(collection, exps, symtab);
                let name = symtab.encode_accessors(accs);
                collection.insert(name, accs);
            }
            Tuple(xs) => {
                for x in xs {
                    exps[*x].node.add_accessors(collection, exps, symtab)
                }
            }
            App(_, args) => {
                for arg in args.iter().flatten() {
                    exps[*arg].node.add_accessors(collection, exps, symtab)
                }
            }
            Unary(_, exp) => exps[*exp].node.add_accessors(collection, exps, symtab),
            Binary(_, lhs, rhs) => {
                exps[*lhs].node.add_accessors(collection, exps, symtab);
                exps[*rhs].node.add_accessors(collection, exps, symtab)
            }
            Set(_, _, exp) => {
                exps[*exp].node.add_accessors(collection, exps, symtab);
            }
            Relation(_, _, _, _, exp) => exps[*exp].node.add_accessors(collection, exps, symtab),
            _ => (),
        }
    }
}

/// Accessors represent paths into potentially complex nested Sail
/// datatypes that are used in the concurrency interface. These Sail
/// subexpressions may not be fully representable in SMT, so when we
/// compile the model we generate event to SMT functions corresponding
/// to only the set of accessors found in the memory model.
#[derive(Debug)]
pub enum Accessor {
    Extz(u32),
    Exts(u32),
    Subvec(u32, u32),
    Tuple(usize),
    Bits(Vec<bool>),
    Field(Name),
    Ctor(Name),
    Wildcard,
    Match(usize),
    Length(u32),
    Address,
    Data,
}

#[derive(Debug)]
pub enum Check {
    Acyclic,
    Irreflexive,
    Empty,
    NonAcyclic,
    NonIrreflexive,
    NonEmpty,
}

pub type TyAnnot = Option<ExpId>;

pub enum Def {
    Let(Name, Vec<(Name, TyAnnot)>, TyAnnot, ExpId),
    Check(Check, ExpId, Name),
    Assert(ExpId),
    Include(String),
    Relation(u32, Name),
}

pub struct MemoryModel {
    pub(crate) name: Option<String>,
    pub(crate) defs: Vec<Spanned<Def>>,
}

pub enum ModelParseError {
    ParseInt { error: ParseIntError, span: (usize, usize) },
    Lex { pos: usize },
    NullaryRelation { span: (usize, usize) },
}

fn format_expected_tokens(expected: &[String]) -> String {
    if expected.is_empty() {
        "".to_string()
    } else {
        let mut output = ", expected:".to_string();
        for token in expected {
            output = format!("{} {}", output, token)
        }
        output
    }
}

fn format_parse_error(
    file_name: &str,
    contents: &str,
    parse_error: ParseError<usize, lexer::Tok<'_>, ModelParseError>,
) -> String {
    let (message, span) = match parse_error {
        ParseError::InvalidToken { location } => (format!("invalid token"), (location, location)),
        ParseError::UnrecognizedEOF { location, expected } => {
            (format!("unrecognized EOF{}", format_expected_tokens(&expected)), (location, location))
        }
        ParseError::UnrecognizedToken { token: (start, tok, end), expected } => {
            (format!("unrecognized token {}{}", tok, format_expected_tokens(&expected)), (start, end))
        }
        ParseError::ExtraToken { token: (start, tok, end) } => (format!("extra token {}", tok), (start, end)),
        ParseError::User { error } => match error {
            ModelParseError::ParseInt { error, span } => (format!("{}", error), span),
            ModelParseError::Lex { pos } => ("could not lex input".to_string(), (pos, pos)),
            ModelParseError::NullaryRelation { span } => (format!("found nullary relation declaration"), span),
        },
    };
    let source_loc = span_to_source_loc(span, 0, contents);
    source_loc.message_file_contents(&file_name, &contents, &message, true, true)
}

impl MemoryModel {
    fn new(defs: Vec<Spanned<Def>>) -> MemoryModel {
        MemoryModel { name: None, defs }
    }

    pub fn accessors<'a>(&self, exps: &'a ExpArena, symtab: &mut Symtab) -> HashMap<Name, &'a [Accessor]> {
        let mut collection = HashMap::new();
        for def in &self.defs {
            match &def.node {
                Def::Let(_, _, _, exp) => exps[*exp].node.add_accessors(&mut collection, exps, symtab),
                Def::Check(_, exp, _) | Def::Assert(exp) => {
                    exps[*exp].node.add_accessors(&mut collection, exps, symtab)
                }
                Def::Include(_) | Def::Relation(_, _) => (),
            }
        }
        collection
    }

    /// Parse a memory model from a string. The file_name argument is used for error reporting only.
    pub fn from_string<'input>(
        file_name: &str,
        contents: &'input str,
        arena: &mut ExpArena,
        symtab: &mut Symtab<'input>,
    ) -> Result<Self, String> {
        let lexer = lexer::Lexer::new(contents);
        match parser::MemoryModelParser::new().parse(arena, symtab, lexer) {
            Ok(cat) => Ok(cat),
            Err(e) => Err(format_parse_error(file_name, contents, e)),
        }
    }
}
