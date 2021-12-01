// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
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

//! This module implements utility functions used to construct
//! primitive operations, including converting IR values into SMT
//! equivalents.

use std::convert::TryInto;

use crate::bitvector::BV;
use crate::bitvector::b64::B64;
use crate::error::ExecError;
use crate::ir::{BitsSegment, Val, SharedState, Ty, Name, source_loc::SourceLoc};
use crate::smt::{Sym, Solver};
use crate::smt::smtlib::{self, bits64, Exp};
use crate::zencode;

#[allow(clippy::needless_range_loop)]
pub fn smt_i128<V>(i: i128) -> Exp<V> {
    let mut bitvec = [false; 128];
    for n in 0..128 {
        if (i >> n & 1) == 1 {
            bitvec[n] = true
        }
    }
    Exp::Bits(bitvec.to_vec())
}

pub fn smt_i64<V>(i: i64) -> Exp<V> {
    Exp::Bits64(B64::new(i as u64, 64))
}

pub fn smt_u8<V>(i: u8) -> Exp<V> {
    Exp::Bits64(B64::new(i as u64, 8))
}

pub fn smt_sbits<B: BV,V>(bv: B) -> Exp<V> {
    if let Ok(u) = bv.try_into() {
        bits64(u, bv.len())
    } else {
        let mut bitvec = Vec::with_capacity(bv.len().try_into().unwrap());
        for n in 0..bv.len() {
            bitvec.push((bv.shiftr(n as i128).lower_u64() & 1) == 1)
        }
        Exp::Bits(bitvec)
    }
}

/// Return the length of a concrete or symbolic bitvector, or return
/// [ExecError::Type] if the argument value is not a bitvector.
pub fn length_bits<B: BV>(bits: &Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<u32, ExecError> {
    match bits {
        Val::Bits(bits) => Ok(bits.len()),
        Val::Symbolic(bits) => match solver.length(*bits) {
            Some(len) => Ok(len),
            None => Err(ExecError::Type(format!("length_bits (solver cannot determine length) {:?}", &bits), info)),
        },
        Val::MixedBits(segments) => segments_length(segments, solver, info),
        _ => Err(ExecError::Type(format!("length_bits {:?}", &bits), info)),
    }
}

// If the argument is a mixed bitvector, concatenate neighbouring concrete
// sections, and if the result is a single concrete bitvector then return
// it as a normal bitvector.
fn flatten_mixed_bits<B: BV>(value: Val<B>) -> Val<B> {
    match value {
        Val::MixedBits(mut segments) => {
            let mut new_segments: Vec<BitsSegment<B>> = vec![];
            match segments.drain(..).fold(None, |acc: Option<B>, segment| match (acc, segment) {
                (Some(bv), BitsSegment::Concrete(bv2)) => bv.append(bv2).or_else(|| {
                    new_segments.push(BitsSegment::Concrete(bv));
                    Some(bv2)
                }),
                (None, BitsSegment::Concrete(bv)) => Some(bv),
                (Some(bv), segment) => {
                    new_segments.push(BitsSegment::Concrete(bv));
                    new_segments.push(segment);
                    None
                }
                (None, segment) => {
                    new_segments.push(segment);
                    None
                }
            }) {
                None => Val::MixedBits(new_segments),
                Some(bv) => {
                    if new_segments.is_empty() {
                        Val::Bits(bv)
                    } else {
                        new_segments.push(BitsSegment::Concrete(bv));
                        Val::MixedBits(new_segments)
                    }
                }
            }
        }
        value => value,
    }
}

/// If a value is a mixed symbolic/concrete bitvector, replace it with a
/// symbolic value and a suitable constraint.
pub fn replace_mixed_bits<B: BV>(value: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    let value = flatten_mixed_bits(value);
    match value {
        Val::MixedBits(segments) => {
            let smt_exp = segments
                .iter()
                .map(|segment| match segment {
                    BitsSegment::Symbolic(v) => Exp::Var(*v),
                    BitsSegment::Concrete(bs) => smt_sbits(*bs),
                })
                .fold(None, |acc, next_exp| match (next_exp, acc) {
                    (Exp::Bits64(bv2), Some(Exp::Bits64(bv1))) => Some(
                        bv1.append(bv2)
                            .map(Exp::Bits64)
                            .unwrap_or_else(|| Exp::Concat(Box::new(Exp::Bits64(bv1)), Box::new(Exp::Bits64(bv2)))),
                    ),
                    (next_exp, Some(exp)) => Some(Exp::Concat(Box::new(exp), Box::new(next_exp))),
                    (next_exp, None) => Some(next_exp),
                })
                .ok_or_else(|| ExecError::Type("empty MixedBits".to_string(), info))?;
            let sym = solver.define_const(smt_exp, info);
            Ok(Val::Symbolic(sym))
        }
        _ => Ok(value),
    }
}

pub fn mixed_bits_to_smt<B: BV>(value: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Exp<Sym>, ExecError> {
    match replace_mixed_bits(value, solver, info)? {
        Val::Symbolic(v) => Ok(Exp::Var(v)),
        Val::Bits(bv) => Ok(smt_sbits(bv)),
        _ => Err(ExecError::Type("mixed_bits_to_smt".to_string(), info)),
    }
}

pub fn segment_length<B: BV>(segment: &BitsSegment<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<u32, ExecError> {
    match segment {
        BitsSegment::Symbolic(v) => match solver.length(*v) {
            Some(len) => Ok(len),
            None => Err(ExecError::Type(format!("length (solver cannot determine length) {:?}", &v), info)),
        },
        BitsSegment::Concrete(bv) => Ok(bv.len()),
    }
}

pub fn segments_length<B: BV>(
    segments: &[BitsSegment<B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<u32, ExecError> {
    Ok(segments.iter().try_fold(0, |n, segment| Ok(n + segment_length(segment, solver, info)?))?)
}

/// Convert base values into SMT equivalents.
pub fn smt_value<B: BV>(v: &Val<B>) -> Result<Exp<Sym>, ExecError> {
    Ok(match v {
        Val::I128(n) => smt_i128(*n),
        Val::I64(n) => smt_i64(*n),
        Val::Bits(bv) => smt_sbits(*bv),
        Val::Bool(b) => Exp::Bool(*b),
        Val::Enum(e) => Exp::Enum(*e),
        Val::Symbolic(v) => Exp::Var(*v),
        _ => return Err(ExecError::Type(format!("smt_value {:?}", &v), SourceLoc::unknown())),
    })
}

fn build_ite<B: BV>(
    b: Sym,
    lhs: &Val<B>,
    rhs: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match (lhs, rhs) {
        (Val::Struct(l_fields), Val::Struct(r_fields)) => {
            let fields: Result<_, _> = l_fields
                .iter()
                .map(|(k, l_val)| match r_fields.get(k) {
                    None => Err(ExecError::Type(format!("build_ite {:?}", &k), info)),
                    Some(r_val) => Ok((*k, build_ite(b, l_val, r_val, solver, info)?)),
                })
                .collect();
            Ok(Val::Struct(fields?))
        }
        _ => solver
            .define_const(Exp::Ite(Box::new(Exp::Var(b)), Box::new(smt_value(lhs)?), Box::new(smt_value(rhs)?)), info)
            .into(),
    }
}

pub fn ite<B: BV>(
    boolean: &Val<B>,
    lhs: &Val<B>,
    rhs: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    match boolean {
        Val::Symbolic(b) => build_ite(*b, lhs, rhs, solver, info),
        Val::Bool(true) => Ok(lhs.clone()),
        Val::Bool(false) => Ok(rhs.clone()),
        _ => Err(ExecError::Type(format!("ite {:?} (expected boolean argument)", boolean), info)),
    }
}

pub fn ite_choice<B: BV>(
    v: &Val<B>,
    vs: &[Val<B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if vs.is_empty() {
        Ok(v.clone())
    } else {
        let vr = ite_choice(&vs[0], &vs[1..], solver, info)?;
        let b = solver.declare_const(smtlib::Ty::Bool, info);
        build_ite(b, v, &vr, solver, info)
    }
}

/// Create a Symbolic value of a specified type. Can return a concrete value if the type only
/// permits a single value, such as for the unit type or the zero-length bitvector type (which is
/// ideal because SMT solvers don't allow zero-length bitvectors). Compound types like structs will
/// be a concrete structure with symbolic values for each field. Returns the `NoSymbolicType` error
/// if the type cannot be represented in the SMT solver.
pub fn symbolic<B: BV>(
    ty: &Ty<Name>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let smt_ty = match ty {
        Ty::Unit => return Ok(Val::Unit),
        Ty::Bits(0) => return Ok(Val::Bits(B::zeros(0))),

        Ty::I64 => smtlib::Ty::BitVec(64),
        Ty::I128 => smtlib::Ty::BitVec(128),
        Ty::Bits(sz) => smtlib::Ty::BitVec(*sz),
        Ty::Bool => smtlib::Ty::Bool,
        Ty::Bit => smtlib::Ty::BitVec(1),

        Ty::Struct(name) => {
            if let Some(field_types) = shared_state.structs.get(name) {
                let field_values = field_types
                    .iter()
                    .map(|(f, ty)| match symbolic(ty, shared_state, solver, info) {
                        Ok(value) => Ok((*f, value)),
                        Err(error) => Err(error),
                    })
                    .collect::<Result<_, _>>()?;
                return Ok(Val::Struct(field_values));
            } else {
                let name = zencode::decode(shared_state.symtab.to_str(*name));
                return Err(ExecError::Unreachable(format!("Struct {} does not appear to exist!", name)));
            }
        }

        Ty::Enum(name) => {
            let enum_size = shared_state.enums.get(name).unwrap().len();
            let enum_id = solver.get_enum(enum_size);
            return solver.declare_const(smtlib::Ty::Enum(enum_id), info).into();
        }

        Ty::FixedVector(sz, ty) => {
            let values = (0..*sz).map(|_| symbolic(ty, shared_state, solver, info)).collect::<Result<_, _>>()?;
            return Ok(Val::Vector(values));
        }

        // Some things we just can't represent symbolically, but we can continue in the hope that
        // they never actually get used.
        _ => return Ok(Val::Poison),
    };

    solver.declare_const(smt_ty, info).into()
}
