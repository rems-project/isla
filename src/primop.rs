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

use std::collections::HashMap;
use std::ops::{BitAnd, BitOr, BitXor, Not};

use crate::ast::Val;
use crate::concrete::Sbits;
use isla_smt::smtlib::*;
use isla_smt::*;

pub type Unary = for<'ast> fn(Val<'ast>, solver: &mut Solver) -> Val<'ast>;
pub type Binary = for<'ast> fn(Val<'ast>, Val<'ast>, solver: &mut Solver) -> Val<'ast>;
pub type Variadic = for<'ast> fn(&[Val<'ast>], solver: &mut Solver) -> Val<'ast>;
pub type Cast = Option<Unary>;

fn type_error(x: &'static str) -> ! {
    panic!("Primop type error: {}", x)
}

#[allow(clippy::needless_range_loop)]
fn smt_i128(i: i128) -> Exp {
    let mut bitvec = [false; 128];
    for n in 0..128 {
        if (i >> n & 1) == 1 {
            bitvec[n] = true
        }
    }
    Exp::Bits(bitvec.to_vec())
}

fn smt_sbits(bv: Sbits) -> Exp {
    Exp::Bits64(bv.bits, bv.length)
}

macro_rules! unary_primop_copy {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path) => {
        fn $f<'ast>(x: Val<'ast>, solver: &mut Solver) -> Val<'ast> {
            match x {
                Val::Symbolic(x) => {
                    let y = solver.fresh();
                    solver.add(Def::DefineConst(y, $smt_op(Box::new(Exp::Var(x)))));
                    Val::Symbolic(y)
                }
                $unwrap(x) => $wrap($concrete_op(x)),
                _ => type_error($name),
            }
        }
    };
}

macro_rules! unary_primop {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path) => {
        fn $f<'ast>(x: Val<'ast>, solver: &mut Solver) -> Val<'ast> {
            match x {
                Val::Symbolic(x) => {
                    let y = solver.fresh();
                    solver.add(Def::DefineConst(y, $smt_op(Box::new(Exp::Var(x)))));
                    Val::Symbolic(y)
                }
                $unwrap(x) => $wrap($concrete_op(&x)),
                (_, _) => type_error($name),
            }
        }
    };
}

macro_rules! binary_primop_copy {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path, $to_symbolic:path) => {
        fn $f<'ast>(x: Val<'ast>, y: Val<'ast>, solver: &mut Solver) -> Val<'ast> {
            match (x, y) {
                (Val::Symbolic(x), Val::Symbolic(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new(Exp::Var(x)), Box::new(Exp::Var(y)))));
                    Val::Symbolic(z)
                }
                (Val::Symbolic(x), $unwrap(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new(Exp::Var(x)), Box::new($to_symbolic(y)))));
                    Val::Symbolic(z)
                }
                ($unwrap(x), Val::Symbolic(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new($to_symbolic(x)), Box::new(Exp::Var(y)))));
                    Val::Symbolic(z)
                }
                ($unwrap(x), $unwrap(y)) => $wrap($concrete_op(x, y)),
                (_, _) => type_error($name),
            }
        }
    };
}

macro_rules! binary_primop {
    ($f:ident, $name:expr, $unwrap:path, $wrap:path, $concrete_op:path, $smt_op:path, $to_symbolic:path) => {
        fn $f<'ast>(x: Val<'ast>, y: Val<'ast>, solver: &mut Solver) -> Val<'ast> {
            match (x, y) {
                (Val::Symbolic(x), Val::Symbolic(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new(Exp::Var(x)), Box::new(Exp::Var(y)))));
                    Val::Symbolic(z)
                }
                (Val::Symbolic(x), $unwrap(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new(Exp::Var(x)), Box::new($to_symbolic(y)))));
                    Val::Symbolic(z)
                }
                ($unwrap(x), Val::Symbolic(y)) => {
                    let z = solver.fresh();
                    solver.add(Def::DefineConst(z, $smt_op(Box::new($to_symbolic(x)), Box::new(Exp::Var(y)))));
                    Val::Symbolic(z)
                }
                ($unwrap(x), $unwrap(y)) => $wrap($concrete_op(&x, &y)),
                (_, _) => type_error($name),
            }
        }
    };
}

fn assume<'ast>(x: Val<'ast>, solver: &mut Solver) -> Val<'ast> {
    match x {
        Val::Symbolic(x) => {
            solver.add(Def::Assert(Exp::Var(x)));
            Val::Unit
        }
        Val::Bool(b) => {
            if b {
                Val::Unit
            } else {
                solver.add(Def::Assert(Exp::Bool(false)));
                Val::Unit
            }
        }
        _ => type_error("assert"),
    }
}

// Basic comparisons

unary_primop_copy!(not_bool, "not", Val::Bool, Val::Bool, bool::not, Exp::Not);
binary_primop_copy!(and_bool, "and_bool", Val::Bool, Val::Bool, bool::bitand, Exp::And, Exp::Bool);
binary_primop_copy!(or_bool, "or_bool", Val::Bool, Val::Bool, bool::bitor, Exp::Or, Exp::Bool);
binary_primop!(eq_int, "eq_int", Val::I128, Val::Bool, i128::eq, Exp::Eq, smt_i128);
binary_primop!(eq_bool, "eq_bool", Val::Bool, Val::Bool, bool::eq, Exp::Eq, Exp::Bool);
binary_primop!(lteq_int, "lteq", Val::I128, Val::Bool, i128::le, Exp::Bvsle, smt_i128);
binary_primop!(gteq_int, "gteq", Val::I128, Val::Bool, i128::ge, Exp::Bvsge, smt_i128);
binary_primop!(lt_int, "lt", Val::I128, Val::Bool, i128::lt, Exp::Bvslt, smt_i128);
binary_primop!(gt_int, "gt", Val::I128, Val::Bool, i128::gt, Exp::Bvsgt, smt_i128);

// Arithmetic operations

binary_primop_copy!(add_int, "add_int", Val::I128, Val::I128, i128::wrapping_add, Exp::Bvadd, smt_i128);
binary_primop_copy!(sub_int, "sub_int", Val::I128, Val::I128, i128::wrapping_sub, Exp::Bvsub, smt_i128);
binary_primop_copy!(mult_int, "mult_int", Val::I128, Val::I128, i128::wrapping_mul, Exp::Bvmul, smt_i128);
unary_primop_copy!(neg_int, "neg_int", Val::I128, Val::I128, i128::wrapping_neg, Exp::Bvneg);
binary_primop_copy!(tdiv_int, "tdiv_int", Val::I128, Val::I128, i128::wrapping_div, Exp::Bvsdiv, smt_i128);
binary_primop_copy!(tmod_int, "tmod_int", Val::I128, Val::I128, i128::wrapping_rem, Exp::Bvsmod, smt_i128);

// Bitvector operations

binary_primop!(eq_bits, "eq_bits", Val::Bits, Val::Bool, Sbits::eq, Exp::Eq, smt_sbits);
binary_primop!(neq_bits, "neq_bits", Val::Bits, Val::Bool, Sbits::ne, Exp::Neq, smt_sbits);
unary_primop_copy!(not_bits, "not_bits", Val::Bits, Val::Bits, Sbits::not, Exp::Bvnot);
binary_primop_copy!(xor_bits, "xor_bits", Val::Bits, Val::Bits, Sbits::bitxor, Exp::Bvxor, smt_sbits);
binary_primop_copy!(or_bits, "or_bits", Val::Bits, Val::Bits, Sbits::bitor, Exp::Bvor, smt_sbits);
binary_primop_copy!(and_bits, "and_bits", Val::Bits, Val::Bits, Sbits::bitand, Exp::Bvand, smt_sbits);

lazy_static! {
    pub static ref UNARY_PRIMOPS: HashMap<String, Unary> = {
        let mut primops = HashMap::new();
        primops.insert("assume".to_string(), assume as Unary);
        primops.insert("not".to_string(), not_bool as Unary);
        primops.insert("neg_int".to_string(), neg_int as Unary);
        primops.insert("not_bits".to_string(), not_bits as Unary);
        primops
    };
    pub static ref BINARY_PRIMOPS: HashMap<String, Binary> = {
        let mut primops = HashMap::new();
        primops.insert("and_bool".to_string(), and_bool as Binary);
        primops.insert("or_bool".to_string(), or_bool as Binary);
        primops.insert("eq_int".to_string(), eq_int as Binary);
        primops.insert("eq_bool".to_string(), eq_bool as Binary);
        primops.insert("lteq".to_string(), lteq_int as Binary);
        primops.insert("gteq".to_string(), gteq_int as Binary);
        primops.insert("lt".to_string(), lt_int as Binary);
        primops.insert("gt".to_string(), gt_int as Binary);
        primops.insert("add_int".to_string(), add_int as Binary);
        primops.insert("sub_int".to_string(), sub_int as Binary);
        primops.insert("mult_int".to_string(), mult_int as Binary);
        primops.insert("tdiv_int".to_string(), tdiv_int as Binary);
        primops.insert("tmod_int".to_string(), tmod_int as Binary);
        primops.insert("eq_bits".to_string(), eq_bits as Binary);
        primops.insert("neq_bits".to_string(), neq_bits as Binary);
        primops.insert("xor_bits".to_string(), xor_bits as Binary);
        primops.insert("or_bits".to_string(), or_bits as Binary);
        primops.insert("and_bits".to_string(), and_bits as Binary);
        primops
    };
    pub static ref VARIADIC_PRIMOPS: HashMap<String, Variadic> = { HashMap::new() };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn div_rem_is_truncating() {
        assert!(i128::wrapping_div(3, 2) == 1);
        assert!(i128::wrapping_div(-3, 2) == -1)
    }
}
