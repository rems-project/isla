use std::fmt;

use crate::litmus::exp::ExpParseError;
use isla_lib::lexer::*;

pub struct ExpLexer<'input> {
    lexer: Lexer<'input>,
}

impl<'input> ExpLexer<'input> {
    pub fn new(input: &'input str) -> Self {
        ExpLexer { lexer: Lexer::new(input) }
    }
}

#[derive(Clone, Debug)]
pub enum Tok<'input> {
    Nat(&'input str),
    Id(&'input str),
    Hex(&'input str),
    Bin(&'input str),
    Implies,
    Not,
    And,
    Or,
    Lparen,
    Rparen,
    Lsquare,
    Rsquare,
    Colon,
    Eq,
    Star,
    Comma,
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
            Keyword::new("->", Implies),
            Keyword::new("~", Not),
            Keyword::new("&", And),
            Keyword::new("|", Or),
            Keyword::new("(", Lparen),
            Keyword::new(")", Rparen),
            Keyword::new("[", Lsquare),
            Keyword::new("]", Rsquare),
            Keyword::new(":", Colon),
            Keyword::new("=", Eq),
            Keyword::new("*", Star),
            Keyword::new(",", Comma),
            Keyword::new(".", Dot),
            Keyword::new("true", True),
            Keyword::new("false", False),
        ]
    };
}

pub type Span<'input> = Result<(usize, Tok<'input>, usize), ExpParseError>;

impl<'input> Iterator for ExpLexer<'input> {
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

        Some(Err(ExpParseError::Lex { pos: self.lexer.pos }))
    }
}
