// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
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

//! This module provides serde-based serialization support for the
//! IR. Note that the various `Primop*` instruction constructors
//! cannot be serialized, as they are direct function pointers to the
//! primop implementations. As such this module is intended to
//! serialize and deserialize the AST _only before_ the primops have
//! been inserted.

use serde::{Deserialize, Serialize};

use super::*;
use crate::concrete::BV;

#[derive(Clone, Serialize, Deserialize)]
enum SInstr<A> {
    Decl(A, Ty<A>),
    Init(A, Ty<A>, Exp<A>),
    Jump(Exp<A>, usize, String),
    Goto(usize),
    Copy(Loc<A>, Exp<A>),
    Monomorphize(A),
    Call(Loc<A>, bool, A, Vec<Exp<A>>),
    Failure,
    Arbitrary,
    End,
}

impl<A> SInstr<A> {
    fn into_instr<B: BV>(self) -> Instr<A, B> {
        use SInstr::*;
        match self {
            Decl(id, ty) => Instr::Decl(id, ty),
            Init(id, ty, exp) => Instr::Init(id, ty, exp),
            Jump(exp, target, info) => Instr::Jump(exp, target, info),
            Goto(target) => Instr::Goto(target),
            Copy(loc, exp) => Instr::Copy(loc, exp),
            Monomorphize(id) => Instr::Monomorphize(id),
            Call(loc, ext, id, args) => Instr::Call(loc, ext, id, args),
            Failure => Instr::Failure,
            Arbitrary => Instr::Arbitrary,
            End => Instr::End,
        }
    }

    fn from_instr<B: BV>(instr: Instr<A, B>) -> Option<Self> {
        use Instr::*;
        Some(match instr {
            Decl(id, ty) => SInstr::Decl(id, ty),
            Init(id, ty, exp) => SInstr::Init(id, ty, exp),
            Jump(exp, target, info) => SInstr::Jump(exp, target, info),
            Goto(target) => SInstr::Goto(target),
            Copy(loc, exp) => SInstr::Copy(loc, exp),
            Monomorphize(id) => SInstr::Monomorphize(id),
            Call(loc, ext, id, args) => SInstr::Call(loc, ext, id, args),
            Failure => SInstr::Failure,
            Arbitrary => SInstr::Arbitrary,
            End => SInstr::End,
            _ => return None,
        })
    }
}

#[derive(Clone, Serialize, Deserialize)]
enum SDef<A> {
    Register(A, Ty<A>),
    Let(Vec<(A, Ty<A>)>, Vec<SInstr<A>>),
    Enum(A, Vec<A>),
    Struct(A, Vec<(A, Ty<A>)>),
    Union(A, Vec<(A, Ty<A>)>),
    Val(A, Vec<Ty<A>>, Ty<A>),
    Extern(A, String, Vec<Ty<A>>, Ty<A>),
    Fn(A, Vec<A>, Vec<SInstr<A>>),
}

impl<A> SDef<A> {
    fn into_def<B: BV>(self) -> Def<A, B> {
        unimplemented!() //TODO
        /*
        use SDef::*;
        match self {
            Register(id, ty) => Def::Register(id, ty),
            Let(bindings, mut setup) => Def::Let(bindings, setup.drain(..).map(SInstr::into_instr).collect()),
            Enum(id, elems) => Def::Enum(id, elems),
            Struct(id, members) => Def::Struct(id, members),
            Union(id, ctors) => Def::Union(id, ctors),
            Val(id, arg_tys, ret_ty) => Def::Val(id, arg_tys, ret_ty),
            Extern(id, ext, arg_tys, ret_ty) => Def::Extern(id, ext, arg_tys, ret_ty),
            Fn(id, args, mut instrs) => Def::Fn(id, args, instrs.drain(..).map(SInstr::into_instr).collect()),
        }
        */
    }

    fn from_def<B: BV>(def: Def<A, B>) -> Option<SDef<A>> {
        use Def::*;
        Some(match def {
            Register(id, ty) => SDef::Register(id, ty),
            Let(bindings, mut setup) => {
                SDef::Let(bindings, setup.drain(..).map(SInstr::from_instr).collect::<Option<_>>()?)
            }
            Enum(id, elems) => SDef::Enum(id, elems),
            Struct(id, members) => SDef::Struct(id, members),
            Union(id, ctors) => SDef::Union(id, ctors),
            Val(id, arg_tys, ret_ty) => SDef::Val(id, arg_tys, ret_ty),
            Extern(id, ext, arg_tys, ret_ty) => SDef::Extern(id, ext, arg_tys, ret_ty),
            Fn(id, args, mut instrs) => {
                SDef::Fn(id, args, instrs.drain(..).map(SInstr::from_instr).collect::<Option<_>>()?)
            }
        })
    }
}

pub fn serialize<B: BV>(mut defs: Vec<Def<Name, B>>) -> Option<Vec<u8>> {
    let sdefs: Vec<SDef<Name>> = defs.drain(..).map(SDef::from_def).collect::<Option<_>>()?;
    bincode::serialize(&sdefs).ok()
}

pub fn deserialize<B: BV>(bytes: &[u8]) -> Option<Vec<Def<Name, B>>> {
    let mut sdefs: Vec<SDef<Name>> = bincode::deserialize(bytes).ok()?;
    Some(sdefs.drain(..).map(SDef::into_def).collect())
}
