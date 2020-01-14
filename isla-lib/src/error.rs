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
pub enum Error {
    Type(&'static str),
    Unimplemented,
    AssertionFailed(String),
    Overflow,
    /// SMTLIB only supports fixed-length bitvectors. This error is
    /// raised if a bitvector width would become symbolic.
    SymbolicLength(&'static str),
    /// Returned when there is no symbolic representation for a
    /// specific type. Certain types like strings are always assumed
    /// to be concrete.
    NoSymbolicType,
    /// Used for cases that should be unreachable (i.e. are definite
    /// errors).
    Unreachable(String),
    /// Used when we try to access memory that does not have any
    /// defined semantics.
    Unmapped,
    BadRead,
    BadWrite,
    OutOfBounds(&'static str),
    Dead,
    Exit,
}
