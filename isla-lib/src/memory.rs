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

//! The memory is split up into various regions defined by a half-open
//! range between two addresses [base, top). This is done because we
//! want to give different semantics to various parts of memory,
//! e.g. program memory should be concrete, whereas the memory used
//! for loads and stores in litmus tests need to be totally symbolic
//! so the bevhaior can be imposed later as part of the concurrency
//! model.

use std::convert::TryFrom;
use std::ops::Range;

use crate::ast::Val;
use crate::error::Error;
use crate::smt::{Event, Solver};

/// For now, we assume that we only deal with 64-bit architectures.
pub type Address = u64;

pub enum Region {
    Symbolic(Range<Address>),
    Concrete(Range<Address>),
}

/// The simplest read is to symbolically read a memory location. In
/// that case we just return a fresh SMT bitvector of the appropriate
/// size, and add a ReadMem event to the trace. For this we need the
/// number of bytes to be non-symbolic, and this function will return
/// Error::SymbolicLength if it is not.
///
/// # Panics
///
/// Panics if the number of bytes to read is concrete but does not fit
/// in a u32, which should never be the case.
fn read_symbolic<'ast>(
    read_kind: Val<'ast>,
    address: Val<'ast>,
    bytes: Val<'ast>,
    solver: &mut Solver<'ast, '_>,
) -> Result<Val<'ast>, Error> {
    if let Val::I128(bytes) = bytes {
        use crate::smt::smtlib::*;
        let bytes = u32::try_from(bytes).expect("Bytes did not fit in u32 in read_symbolic");
        let value = solver.fresh();
        solver.add(Def::DeclareConst(value, Ty::BitVec(8 * bytes)));
        solver.add_event(Event::ReadMem { value, read_kind, address, bytes });
        Ok(Val::Symbolic(value))
    } else {
        Err(Error::SymbolicLength)
    }
}

/// `write_symbolic` just adds a WriteMem event to the trace,
/// returning a symbolic boolean (the semantics of which is controlled
/// by a memory model if required, but can be ignored in
/// others). Raises a type error if the data argument is not a
/// bitvector with a length that is a multiple of 8. This should be
/// guaranteed by the Sail type system.
fn write_symbolic<'ast>(
    write_kind: Val<'ast>,
    address: Val<'ast>,
    data: Val<'ast>,
    solver: &mut Solver<'ast, '_>,
) -> Result<Val<'ast>, Error> {
    let data_length = crate::primop::length_bits(&data, solver)?;
    if data_length % 8 != 0 {
	return Err(Error::Type("write_symbolic"))
    };
    let bytes = data_length / 8;
    use crate::smt::smtlib::*;
    let value = solver.fresh();
    solver.add(Def::DeclareConst(value, Ty::Bool));
    solver.add_event(Event::WriteMem { value, write_kind, address, data, bytes });
    Ok(Val::Symbolic(value))
}
