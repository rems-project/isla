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
use std::ops::{BitAnd, BitOr, Not};

use crate::ast::Val;
use isla_smt::smtlib::*;
use isla_smt::*;

pub type Unary = for<'ast> fn(Val<'ast>, solver: &mut Solver) -> Val<'ast>;
pub type Binary = for<'ast> fn(Val<'ast>, Val<'ast>, solver: &mut Solver) -> Val<'ast>;

fn type_error(x: &'static str) -> ! {
    panic!("Primop type error: {}", x)
}

#[allow(clippy::needless_range_loop)]
fn bvint(i: i128) -> Exp {
    let mut bitvec = [false; 128];
    for n in 0..128 {
        if (i >> n & 1) == 1 {
            bitvec[n] = true
        }
    }
    Exp::Bits(bitvec.to_vec())
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

// lib/flow.sail

unary_primop_copy!(not_bool, "not_bool", Val::Bool, Val::Bool, bool::not, Exp::Not);
binary_primop_copy!(and_bool, "and_bool", Val::Bool, Val::Bool, bool::bitand, Exp::And, Exp::Bool);
binary_primop_copy!(or_bool, "or_bool", Val::Bool, Val::Bool, bool::bitor, Exp::Or, Exp::Bool);
binary_primop!(eq_int, "eq_int", Val::Int, Val::Bool, i128::eq, Exp::Eq, bvint);
binary_primop!(eq_bool, "eq_bool", Val::Bool, Val::Bool, bool::eq, Exp::Eq, Exp::Bool);
binary_primop!(lteq_int, "lteq_int", Val::Int, Val::Bool, i128::le, Exp::Bvsle, bvint);
binary_primop!(gteq_int, "gteq_int", Val::Int, Val::Bool, i128::ge, Exp::Bvsge, bvint);
binary_primop!(lt_int, "lt_int", Val::Int, Val::Bool, i128::lt, Exp::Bvslt, bvint);
binary_primop!(gt_int, "gt_int", Val::Int, Val::Bool, i128::gt, Exp::Bvsgt, bvint);

// lib/arith.sail

binary_primop_copy!(add_int, "add_int", Val::Int, Val::Int, i128::wrapping_add, Exp::Bvadd, bvint);
binary_primop_copy!(sub_int, "sub_int", Val::Int, Val::Int, i128::wrapping_sub, Exp::Bvsub, bvint);
binary_primop_copy!(mult_int, "mult_int", Val::Int, Val::Int, i128::wrapping_mul, Exp::Bvmul, bvint);
unary_primop_copy!(neg_int, "neg_int", Val::Int, Val::Int, i128::wrapping_neg, Exp::Bvneg);
binary_primop_copy!(tdiv_int, "tdiv_int", Val::Int, Val::Int, i128::wrapping_div, Exp::Bvsdiv, bvint);
binary_primop_copy!(tmod_int, "tmod_int", Val::Int, Val::Int, i128::wrapping_rem, Exp::Bvsmod, bvint);

lazy_static! {
    pub static ref UNARY_PRIMOPS: HashMap<String, Unary> = {
        let mut primops = HashMap::new();
        primops.insert("not_bool".to_string(), not_bool as Unary);
        primops.insert("neg_int".to_string(), neg_int as Unary);
        primops
    };
    pub static ref BINARY_PRIMOPS: HashMap<String, Binary> = {
        let mut primops = HashMap::new();
        primops.insert("and_bool".to_string(), and_bool as Binary);
        primops.insert("or_bool".to_string(), or_bool as Binary);
        primops.insert("eq_int".to_string(), eq_int as Binary);
        primops.insert("eq_bool".to_string(), eq_bool as Binary);
        primops.insert("lteq_int".to_string(), lteq_int as Binary);
        primops.insert("gteq_int".to_string(), gteq_int as Binary);
        primops.insert("lt_int".to_string(), lt_int as Binary);
        primops.insert("gt_int".to_string(), gt_int as Binary);
        primops.insert("add_int".to_string(), add_int as Binary);
        primops.insert("sub_int".to_string(), sub_int as Binary);
        primops.insert("mult_int".to_string(), mult_int as Binary);
        primops.insert("tdiv_int".to_string(), tdiv_int as Binary);
        primops.insert("tmod_int".to_string(), tmod_int as Binary);
        primops
    };
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
