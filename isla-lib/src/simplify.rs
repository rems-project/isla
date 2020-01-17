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

use crate::ast::{Symtab, HAVE_EXCEPTION};
use crate::smt::smtlib::*;
use crate::smt::Event;
use crate::smt::Event::*;
use crate::smt::Trace;
use crate::zencode;

/// `uses_in_exp` counts the number of occurences of each variable in an SMTLIB expression.
fn uses_in_exp(uses: &mut HashMap<u32, u32>, exp: &Exp) {
    use Exp::*;
    match exp {
        Var(v) => {
            uses.insert(*v, uses.get(&v).unwrap_or(&0) + 1);
        }
        Bits(_) | Bits64(_, _) | Bool(_) => (),
        Not(exp)
        | Bvnot(exp)
        | Bvredand(exp)
        | Bvredor(exp)
        | Bvneg(exp)
        | Extract(_, _, exp)
        | ZeroExtend(_, exp)
        | SignExtend(_, exp) => uses_in_exp(uses, exp),
        Eq(lhs, rhs)
        | Neq(lhs, rhs)
        | And(lhs, rhs)
        | Or(lhs, rhs)
        | Bvand(lhs, rhs)
        | Bvor(lhs, rhs)
        | Bvxor(lhs, rhs)
        | Bvnand(lhs, rhs)
        | Bvnor(lhs, rhs)
        | Bvxnor(lhs, rhs)
        | Bvadd(lhs, rhs)
        | Bvsub(lhs, rhs)
        | Bvmul(lhs, rhs)
        | Bvudiv(lhs, rhs)
        | Bvsdiv(lhs, rhs)
        | Bvurem(lhs, rhs)
        | Bvsrem(lhs, rhs)
        | Bvsmod(lhs, rhs)
        | Bvult(lhs, rhs)
        | Bvslt(lhs, rhs)
        | Bvule(lhs, rhs)
        | Bvsle(lhs, rhs)
        | Bvuge(lhs, rhs)
        | Bvsge(lhs, rhs)
        | Bvugt(lhs, rhs)
        | Bvsgt(lhs, rhs)
        | Bvshl(lhs, rhs)
        | Bvlshr(lhs, rhs)
        | Bvashr(lhs, rhs)
        | Concat(lhs, rhs) => {
            uses_in_exp(uses, lhs);
            uses_in_exp(uses, rhs)
        }
        Ite(cond, then_exp, else_exp) => {
            uses_in_exp(uses, cond);
            uses_in_exp(uses, then_exp);
            uses_in_exp(uses, else_exp)
        }
    }
}

pub fn simplify(trace: &Trace, symtab: &Symtab) {
    // First we collect all the definitions in the trace into a single vector
    let events: Vec<&Event> = trace.to_vec();

    let mut uses: HashMap<u32, u32> = HashMap::new();
    for event in events.iter().rev() {
        match event {
            Event::Smt(Def::DefineConst(_, exp)) => uses_in_exp(&mut uses, exp),
            Event::Smt(Def::Assert(exp)) => uses_in_exp(&mut uses, exp),
            _ => (),
        }
    }

    print!("(trace");
    for event in events.iter().rev() {
        match event {
            Branch(n, loc) => print!("\n  (branch {} \"{}\")", n, loc),
            Smt(def) => {
                print!("\n  {}", def);
            }
            WriteReg(n, v) => {
                print!("\n  (write-reg |{}| {})", zencode::decode(symtab.to_str(*n)), v.to_string(symtab))
            }
            ReadMem { value, read_kind, address, bytes } => print!(
                "\n  (read-mem v{} {} {} {})",
                value,
                read_kind.to_string(symtab),
                address.to_string(symtab),
                bytes
            ),
            WriteMem { value, write_kind, address, data, bytes } => print!(
                "\n  (write-mem v{} {} {} {} {})",
                value,
                write_kind.to_string(symtab),
                address.to_string(symtab),
                data.to_string(symtab),
                bytes
            ),
            ReadReg(n, acc, v) => {
                if *n == HAVE_EXCEPTION {
                } else {
                    let acc = acc
                        .iter()
                        .map(|elem| elem.to_string(symtab))
                        .fold(None, |acc, elem| {
                            if let Some(prefix) = acc {
                                Some(format!("{} {}", prefix, elem))
                            } else {
                                Some(elem)
                            }
                        })
                        .map_or("nil".to_string(), |acc| format!("({})", acc));
                    print!("\n  (read-reg |{}| {} {})", zencode::decode(symtab.to_str(*n)), acc, v.to_string(symtab))
                }
            }
        }
    }
    println!(")");
}
