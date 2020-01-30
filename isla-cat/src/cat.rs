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

#[derive(Debug)]
pub enum Exp {
    Empty,
    Id(String),
    Let(String, Box<Exp>, Box<Exp>),
    TryWith(String, Box<Exp>),
    Union(Box<Exp>, Box<Exp>),
    Inter(Box<Exp>, Box<Exp>),
    Add(Box<Exp>, Box<Exp>),
    Diff(Box<Exp>, Box<Exp>),
    Seq(Box<Exp>, Box<Exp>),
    Cartesian(Box<Exp>, Box<Exp>),
    Compl(Box<Exp>),
    Identity(Box<Exp>),
    IdentityInter(Box<Exp>),
    Inverse(Box<Exp>),
    TClosure(Box<Exp>),
    RTClosure(Box<Exp>),
    App(String, Box<Exp>),
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

#[derive(Debug)]
pub enum LetKind {
    Let,
    Rec,
    And,
}

#[derive(Debug)]
pub enum Def {
    Include(String),
    Let(LetKind, String, Exp),
    Flag(Check, Exp, String),
    Check(Check, Exp, Option<String>),
    Show(Vec<String>),
    Unshow(Vec<String>),
}

#[derive(Debug)]
pub struct Cat {
    pub tag: String,
    pub defs: Vec<Def>,
}
