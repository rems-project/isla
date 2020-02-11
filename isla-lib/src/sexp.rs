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

use crate::concrete::Sbits;

#[derive(Debug)]
pub enum Sexp<'a> {
    Atom(&'a str),
    I128(i128),
    Bits(Sbits),
    List(Vec<Sexp<'a>>),
}

impl<'a> Sexp<'a> {
    pub fn is_fn(&self, name: &str, args: usize) -> bool {
        match self {
            Sexp::List(sexps) if sexps.len() > args => {
                if let Sexp::Atom(f) = sexps[0] {
                    f == name
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    pub fn as_str(&self) -> Option<&'a str> {
        match self {
            Sexp::Atom(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_usize(&self) -> Option<usize> {
        match self {
            Sexp::I128(n) => Some(*n as usize),
            _ => None,
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Sexp::I128(n) => Some(*n as u64),
            _ => None,
        }
    }
}
