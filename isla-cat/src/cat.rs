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

use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::path::{Path, PathBuf};

use crate::cat_lexer;
use crate::cat_parser;

#[derive(Debug)]
pub enum Exp {
    Empty,
    Id(String),
    Let(String, Box<Exp>, Box<Exp>),
    TryWith(Box<Exp>, Box<Exp>),
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
    Let(LetKind, String, Exp),
    Flag(Check, Exp, String),
    Check(Check, Exp, Option<String>),
    Show(Vec<String>),
    ShowAs(Exp, String),
    Unshow(Vec<String>),
    SpecialCos,
}

#[derive(Debug)]
pub enum ParseDef {
    Def(Def),
    Include(String),
}

#[derive(Debug)]
pub struct ParseCat {
    pub tag: String,
    pub defs: Vec<ParseDef>,
}

pub struct Cat {
    pub tag: String,
    pub defs: Vec<Def>,
}

impl ParseCat {
    pub fn from_file<P>(path: P) -> Result<Self, String>
    where
        P: AsRef<Path>,
    {
        let file_name = path.as_ref().display();
        let mut contents = String::new();

        match File::open(&path) {
            Ok(mut handle) => match handle.read_to_string(&mut contents) {
                Ok(_) => (),
                Err(e) => return Err(format!("Error when reading cat file '{:?}': {}", file_name, e)),
            },
            Err(e) => return Err(format!("Error when opening cat file '{:?}': {}", file_name, e)),
        }

        let lexer = cat_lexer::Lexer::new(&contents);
        match cat_parser::CatParser::new().parse(lexer) {
            Ok(cat) => Ok(cat),
            Err(e) => Err(format!("Failed to parse cat file '{:?}': {}", file_name, e)),
        }
    }
}

fn resolve_imports(cat_dirs: &[PathBuf], mut parse_cat: ParseCat) -> Result<Cat, String> {
    Ok(Cat {
        tag: parse_cat.tag,
        defs: parse_cat
            .defs
            .drain(..)
            .map(|parse_def| match parse_def {
                ParseDef::Def(def) => Ok(vec![def]),
                ParseDef::Include(name) => find_cat(cat_dirs, &name).map(|cat| cat.defs),
            })
            .collect::<Result<Vec<_>, _>>()?
            .drain(..)
            .flatten()
            .collect(),
    })
}

fn find_cat(cat_dirs: &[PathBuf], name: &str) -> Result<Cat, String> {
    if name == "cos.cat" {
        return Ok(Cat { tag: "".to_string(), defs: vec![Def::SpecialCos] });
    }

    for dir in cat_dirs {
        let cat_file = dir.join(name);
        if cat_file.is_file() {
            let parse_cat = ParseCat::from_file(cat_file)?;
            return resolve_imports(cat_dirs, parse_cat);
        }
    }

    Err(format!("Could not find cat: {}", name))
}

pub fn load_cat(name: &str) -> Result<Cat, String> {
    let path = Path::new(name);

    let mut cat_dirs: Vec<PathBuf> = Vec::new();

    match env::var("HERDLIB") {
        Ok(directory) => cat_dirs.push(directory.into()),
        Err(_) => (),
    }

    let mut directory = path.to_path_buf();
    directory.pop();
    if directory.is_dir() {
        cat_dirs.push(directory)
    }

    if path.is_file() {
        let parse_cat = ParseCat::from_file(path)?;
        resolve_imports(&cat_dirs, parse_cat)
    } else {
        find_cat(&cat_dirs, name)
    }
}
