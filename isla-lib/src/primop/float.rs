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

//! This module defines all the Sail primitives for working with
//! floating point numbers.  Internally Isla uses the same
//! representation for floating points that Z3/SMTLIB uses, which
//! allows floating point numbers with arbitrary exponent and
//! significand widths. However, in Sail we want to ensure we can use
//! SoftFloat for emulation, so we restrict the primitives here to 16,
//! 32, 64, and 128-bit variants, prefixed either `fp16`, `fp32`,
//! `fp64`, and `fp128` respectively, as these are supported by
//! SoftFloat. Functions just prefixed with `fp_` work with any input
//! width.
//!
//! Using floating point types requires that the Solver is
//! instantiated with the `ALL` theory rather than just
//! bitvectors+datatypes as per usual.

use std::collections::HashMap;

use crate::bitvector::BV;
use crate::error::ExecError;
use crate::executor::LocalFrame;
use crate::ir::{FPTy, Val};
use crate::smt::smtlib::*;
use crate::smt::*;
use crate::source_loc::SourceLoc;

use super::{Binary, Unary, Variadic};

macro_rules! rounding_mode_primop {
    ($f:ident, $mode:expr) => {
        pub fn $f<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            solver.define_const(Exp::FPRoundingMode($mode), info).into()
        }
    };
}

rounding_mode_primop!(round_nearest_ties_to_even, FPRoundingMode::RoundNearestTiesToEven);
rounding_mode_primop!(round_nearest_ties_to_away, FPRoundingMode::RoundNearestTiesToAway);
rounding_mode_primop!(round_toward_positive, FPRoundingMode::RoundTowardPositive);
rounding_mode_primop!(round_toward_negative, FPRoundingMode::RoundTowardNegative);
rounding_mode_primop!(round_toward_zero, FPRoundingMode::RoundTowardZero);

pub fn fp16_undefined<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(FPTy::fp16().to_smt(), info).into()
}

pub fn fp32_undefined<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(FPTy::fp32().to_smt(), info).into()
}

pub fn fp64_undefined<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(FPTy::fp64().to_smt(), info).into()
}

pub fn fp128_undefined<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
    solver.declare_const(FPTy::fp128().to_smt(), info).into()
}

macro_rules! fp_constant_primop {
    ($f:ident, $constant:expr) => {
        pub mod $f {
            use super::*;
            pub fn constant16<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
                let ty = FPTy::fp16();
                solver
                    .define_const(Exp::FPConstant($constant, ty.exponent_width(), ty.significand_width()), info)
                    .into()
            }
            pub fn constant32<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
                let ty = FPTy::fp32();
                solver
                    .define_const(Exp::FPConstant($constant, ty.exponent_width(), ty.significand_width()), info)
                    .into()
            }
            pub fn constant64<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
                let ty = FPTy::fp64();
                solver
                    .define_const(Exp::FPConstant($constant, ty.exponent_width(), ty.significand_width()), info)
                    .into()
            }
            pub fn constant128<B: BV>(_: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
                let ty = FPTy::fp128();
                solver
                    .define_const(Exp::FPConstant($constant, ty.exponent_width(), ty.significand_width()), info)
                    .into()
            }
        }
    };
}

fp_constant_primop!(fp_nan, FPConstant::NaN);
fp_constant_primop!(fp_inf, FPConstant::Inf { negative: false });
fp_constant_primop!(fp_negative_inf, FPConstant::Inf { negative: true });
fp_constant_primop!(fp_zero, FPConstant::Zero { negative: false });
fp_constant_primop!(fp_negative_zero, FPConstant::Zero { negative: true });

macro_rules! fp_unary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(v: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            match v {
                Val::Symbolic(v) => solver.define_const(Exp::FPUnary($op, Box::new(Exp::Var(v))), info).into(),
                _ => Err(ExecError::Type(stringify!($f).to_string(), info)),
            }
        }
    };
}

fp_unary_primop!(fp_abs, FPUnary::Abs);
fp_unary_primop!(fp_neg, FPUnary::Neg);
fp_unary_primop!(fp_is_normal, FPUnary::IsNormal);
fp_unary_primop!(fp_is_subnormal, FPUnary::IsSubnormal);
fp_unary_primop!(fp_is_zero, FPUnary::IsZero);
fp_unary_primop!(fp_is_infinite, FPUnary::IsInfinite);
fp_unary_primop!(fp_is_nan, FPUnary::IsNaN);
fp_unary_primop!(fp_is_negative, FPUnary::IsNegative);
fp_unary_primop!(fp_is_positive, FPUnary::IsPositive);

fp_unary_primop!(fp16_from_ieee, {
    let ty = FPTy::fp16();
    FPUnary::FromIEEE(ty.exponent_width(), ty.significand_width())
});
fp_unary_primop!(fp32_from_ieee, {
    let ty = FPTy::fp32();
    FPUnary::FromIEEE(ty.exponent_width(), ty.significand_width())
});
fp_unary_primop!(fp64_from_ieee, {
    let ty = FPTy::fp64();
    FPUnary::FromIEEE(ty.exponent_width(), ty.significand_width())
});
fp_unary_primop!(fp128_from_ieee, {
    let ty = FPTy::fp128();
    FPUnary::FromIEEE(ty.exponent_width(), ty.significand_width())
});

macro_rules! fp_rounding_unary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(rm: Val<B>, v: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Result<Val<B>, ExecError> {
            match (rm, v) {
                (Val::Symbolic(rm), Val::Symbolic(v)) => solver
                    .define_const(Exp::FPRoundingUnary($op, Box::new(Exp::Var(rm)), Box::new(Exp::Var(v))), info)
                    .into(),
                _ => Err(ExecError::Type(stringify!($f).to_string(), info)),
            }
        }
    };
}

fp_rounding_unary_primop!(fp_sqrt, FPRoundingUnary::Sqrt);
fp_rounding_unary_primop!(fp_round_to_integral, FPRoundingUnary::RoundToIntegral);

fp_rounding_unary_primop!(fp16_convert, {
    let ty = FPTy::fp16();
    FPRoundingUnary::Convert(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp32_convert, {
    let ty = FPTy::fp32();
    FPRoundingUnary::Convert(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp64_convert, {
    let ty = FPTy::fp64();
    FPRoundingUnary::Convert(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp128_convert, {
    let ty = FPTy::fp128();
    FPRoundingUnary::Convert(ty.exponent_width(), ty.significand_width())
});

fp_rounding_unary_primop!(fp16_from_signed, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromSigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp32_from_signed, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromSigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp64_from_signed, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromSigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp128_from_signed, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromSigned(ty.exponent_width(), ty.significand_width())
});

fp_rounding_unary_primop!(fp16_from_unsigned, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromUnsigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp32_from_unsigned, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromUnsigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp64_from_unsigned, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromUnsigned(ty.exponent_width(), ty.significand_width())
});
fp_rounding_unary_primop!(fp128_from_unsigned, {
    let ty = FPTy::fp16();
    FPRoundingUnary::FromUnsigned(ty.exponent_width(), ty.significand_width())
});

fp_rounding_unary_primop!(fp_to_signed16, FPRoundingUnary::ToSigned(16));
fp_rounding_unary_primop!(fp_to_signed32, FPRoundingUnary::ToSigned(32));
fp_rounding_unary_primop!(fp_to_signed64, FPRoundingUnary::ToSigned(64));
fp_rounding_unary_primop!(fp_to_signed128, FPRoundingUnary::ToSigned(128));

macro_rules! fp_binary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(
            lhs: Val<B>,
            rhs: Val<B>,
            solver: &mut Solver<B>,
            info: SourceLoc,
        ) -> Result<Val<B>, ExecError> {
            match (lhs, rhs) {
                (Val::Symbolic(lhs), Val::Symbolic(rhs)) => solver
                    .define_const(Exp::FPBinary($op, Box::new(Exp::Var(lhs)), Box::new(Exp::Var(rhs))), info)
                    .into(),
                _ => Err(ExecError::Type(stringify!($f).to_string(), info)),
            }
        }
    };
}

fp_binary_primop!(fp_rem, FPBinary::Rem);
fp_binary_primop!(fp_min, FPBinary::Min);
fp_binary_primop!(fp_max, FPBinary::Max);
fp_binary_primop!(fp_lteq, FPBinary::Leq);
fp_binary_primop!(fp_lt, FPBinary::Lt);
fp_binary_primop!(fp_gteq, FPBinary::Geq);
fp_binary_primop!(fp_gt, FPBinary::Gt);
fp_binary_primop!(fp_eq, FPBinary::Eq);

macro_rules! fp_rounding_binary_primop {
    ($f:ident, $op:expr) => {
        pub fn $f<B: BV>(
            mut args: Vec<Val<B>>,
            solver: &mut Solver<B>,
            _: &mut LocalFrame<B>,
            info: SourceLoc,
        ) -> Result<Val<B>, ExecError> {
            if args.len() != 3 {
                return Err(ExecError::Type(format!("Incorrect number of arguments for {}", stringify!($f)), info));
            }
            let rhs = args.pop().unwrap();
            let lhs = args.pop().unwrap();
            let rm = args.pop().unwrap();
            match (rm, lhs, rhs) {
                (Val::Symbolic(rm), Val::Symbolic(lhs), Val::Symbolic(rhs)) => solver
                    .define_const(
                        Exp::FPRoundingBinary(
                            $op,
                            Box::new(Exp::Var(rm)),
                            Box::new(Exp::Var(lhs)),
                            Box::new(Exp::Var(rhs)),
                        ),
                        info,
                    )
                    .into(),
                _ => Err(ExecError::Type(stringify!($f).to_string(), info)),
            }
        }
    };
}

fp_rounding_binary_primop!(fp_add, FPRoundingBinary::Add);
fp_rounding_binary_primop!(fp_sub, FPRoundingBinary::Sub);
fp_rounding_binary_primop!(fp_mul, FPRoundingBinary::Mul);
fp_rounding_binary_primop!(fp_div, FPRoundingBinary::Div);

pub fn fp_fma<B: BV>(
    mut args: Vec<Val<B>>,
    solver: &mut Solver<B>,
    _: &mut LocalFrame<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if args.len() != 4 {
        return Err(ExecError::Type("Incorrect number of arguments for fp_fma".to_string(), info));
    }
    let z = args.pop().unwrap();
    let y = args.pop().unwrap();
    let x = args.pop().unwrap();
    let rm = args.pop().unwrap();
    match (rm, x, y, z) {
        (Val::Symbolic(rm), Val::Symbolic(x), Val::Symbolic(y), Val::Symbolic(z)) => solver
            .define_const(
                Exp::FPfma(Box::new(Exp::Var(rm)), Box::new(Exp::Var(x)), Box::new(Exp::Var(y)), Box::new(Exp::Var(z))),
                info,
            )
            .into(),
        _ => Err(ExecError::Type("fp_fma".to_string(), info)),
    }
}

pub fn unary_primops<B: BV>() -> HashMap<String, Unary<B>> {
    let mut primops = HashMap::new();
    primops.insert("round_nearest_ties_to_even".to_string(), round_nearest_ties_to_even as Unary<B>);
    primops.insert("round_nearest_ties_to_away".to_string(), round_nearest_ties_to_away as Unary<B>);
    primops.insert("round_toward_positive".to_string(), round_toward_positive as Unary<B>);
    primops.insert("round_toward_negative".to_string(), round_toward_negative as Unary<B>);
    primops.insert("round_toward_zero".to_string(), round_toward_zero as Unary<B>);

    primops.insert("fp16_nan".to_string(), fp_nan::constant16 as Unary<B>);
    primops.insert("fp32_nan".to_string(), fp_nan::constant32 as Unary<B>);
    primops.insert("fp64_nan".to_string(), fp_nan::constant64 as Unary<B>);
    primops.insert("fp128_nan".to_string(), fp_nan::constant128 as Unary<B>);

    primops.insert("fp16_inf".to_string(), fp_inf::constant16 as Unary<B>);
    primops.insert("fp32_inf".to_string(), fp_inf::constant32 as Unary<B>);
    primops.insert("fp64_inf".to_string(), fp_inf::constant64 as Unary<B>);
    primops.insert("fp128_inf".to_string(), fp_inf::constant128 as Unary<B>);

    primops.insert("fp16_negative_inf".to_string(), fp_negative_inf::constant16 as Unary<B>);
    primops.insert("fp32_negative_inf".to_string(), fp_negative_inf::constant32 as Unary<B>);
    primops.insert("fp64_negative_inf".to_string(), fp_negative_inf::constant64 as Unary<B>);
    primops.insert("fp128_negative_inf".to_string(), fp_negative_inf::constant128 as Unary<B>);

    primops.insert("fp16_zero".to_string(), fp_zero::constant16 as Unary<B>);
    primops.insert("fp32_zero".to_string(), fp_zero::constant32 as Unary<B>);
    primops.insert("fp64_zero".to_string(), fp_zero::constant64 as Unary<B>);
    primops.insert("fp128_zero".to_string(), fp_zero::constant128 as Unary<B>);

    primops.insert("fp16_negative_zero".to_string(), fp_negative_zero::constant16 as Unary<B>);
    primops.insert("fp32_negative_zero".to_string(), fp_negative_zero::constant32 as Unary<B>);
    primops.insert("fp64_negative_zero".to_string(), fp_negative_zero::constant64 as Unary<B>);
    primops.insert("fp128_negative_zero".to_string(), fp_negative_zero::constant128 as Unary<B>);

    primops.insert("fp16_undefined".to_string(), fp16_undefined as Unary<B>);
    primops.insert("fp32_undefined".to_string(), fp32_undefined as Unary<B>);
    primops.insert("fp64_undefined".to_string(), fp64_undefined as Unary<B>);
    primops.insert("fp128_undefined".to_string(), fp128_undefined as Unary<B>);

    primops.insert("fp_abs".to_string(), fp_abs as Unary<B>);
    primops.insert("fp_neg".to_string(), fp_neg as Unary<B>);
    primops.insert("fp_is_normal".to_string(), fp_is_normal as Unary<B>);
    primops.insert("fp_is_subnormal".to_string(), fp_is_subnormal as Unary<B>);
    primops.insert("fp_is_zero".to_string(), fp_is_zero as Unary<B>);
    primops.insert("fp_is_infinite".to_string(), fp_is_infinite as Unary<B>);
    primops.insert("fp_is_nan".to_string(), fp_is_nan as Unary<B>);
    primops.insert("fp_is_negative".to_string(), fp_is_negative as Unary<B>);
    primops.insert("fp_is_positive".to_string(), fp_is_positive as Unary<B>);

    primops.insert("fp16_from_ieee".to_string(), fp16_from_ieee as Unary<B>);
    primops.insert("fp32_from_ieee".to_string(), fp32_from_ieee as Unary<B>);
    primops.insert("fp64_from_ieee".to_string(), fp64_from_ieee as Unary<B>);
    primops.insert("fp128_from_ieee".to_string(), fp128_from_ieee as Unary<B>);

    primops
}

pub fn binary_primops<B: BV>() -> HashMap<String, Binary<B>> {
    let mut primops = HashMap::new();
    primops.insert("fp_sqrt".to_string(), fp_sqrt as Binary<B>);
    primops.insert("fp_round_to_integral".to_string(), fp_round_to_integral as Binary<B>);

    primops.insert("fp16_convert".to_string(), fp16_convert as Binary<B>);
    primops.insert("fp32_convert".to_string(), fp32_convert as Binary<B>);
    primops.insert("fp64_convert".to_string(), fp64_convert as Binary<B>);
    primops.insert("fp128_convert".to_string(), fp128_convert as Binary<B>);

    primops.insert("fp16_from_signed".to_string(), fp16_from_signed as Binary<B>);
    primops.insert("fp32_from_signed".to_string(), fp32_from_signed as Binary<B>);
    primops.insert("fp64_from_signed".to_string(), fp64_from_signed as Binary<B>);
    primops.insert("fp128_from_signed".to_string(), fp128_from_signed as Binary<B>);

    primops.insert("fp16_from_unsigned".to_string(), fp16_from_unsigned as Binary<B>);
    primops.insert("fp32_from_unsigned".to_string(), fp32_from_unsigned as Binary<B>);
    primops.insert("fp64_from_unsigned".to_string(), fp64_from_unsigned as Binary<B>);
    primops.insert("fp128_from_unsigned".to_string(), fp128_from_unsigned as Binary<B>);

    primops.insert("fp_to_signed16".to_string(), fp_to_signed16 as Binary<B>);
    primops.insert("fp_to_signed32".to_string(), fp_to_signed32 as Binary<B>);
    primops.insert("fp_to_signed64".to_string(), fp_to_signed64 as Binary<B>);
    primops.insert("fp_to_signed128".to_string(), fp_to_signed128 as Binary<B>);

    primops.insert("fp_rem".to_string(), fp_rem as Binary<B>);
    primops.insert("fp_min".to_string(), fp_min as Binary<B>);
    primops.insert("fp_max".to_string(), fp_max as Binary<B>);

    primops.insert("fp_lteq".to_string(), fp_lteq as Binary<B>);
    primops.insert("fp_lt".to_string(), fp_lt as Binary<B>);
    primops.insert("fp_gteq".to_string(), fp_gteq as Binary<B>);
    primops.insert("fp_gt".to_string(), fp_gt as Binary<B>);
    primops.insert("fp_eq".to_string(), fp_eq as Binary<B>);
    primops
}

pub fn variadic_primops<B: BV>() -> HashMap<String, Variadic<B>> {
    let mut primops = HashMap::new();
    primops.insert("fp_add".to_string(), fp_add as Variadic<B>);
    primops.insert("fp_sub".to_string(), fp_sub as Variadic<B>);
    primops.insert("fp_mul".to_string(), fp_mul as Variadic<B>);
    primops.insert("fp_div".to_string(), fp_div as Variadic<B>);
    primops.insert("fp_fma".to_string(), fp_fma as Variadic<B>);
    primops
}
