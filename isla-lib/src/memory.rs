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

use std::collections::HashMap;
use std::convert::TryFrom;
use std::ops::Range;

use crate::concrete::Sbits;
use crate::error::Error;
use crate::ir::Val;
use crate::smt::{Event, Solver};
use crate::log::log;

/// For now, we assume that we only deal with 64-bit architectures.
pub type Address = u64;

#[derive(Clone)]
enum Region {
    Symbolic(Range<Address>),
    Concrete(Range<Address>, HashMap<Address, u8>),
}

#[derive(Clone)]
pub struct Memory {
    regions: Vec<Region>,
}

impl Memory {
    pub fn new() -> Self {
        Memory {
            regions: Vec::new()
        }
    }

    pub fn log_info(&self, level: usize) {
        for region in &self.regions {
            match region {
                Region::Symbolic(range) => {
                    log(level, &format!("Memory range: [0x{:x}, 0x{:x}) symbolic", range.start, range.end))
                }
                Region::Concrete(range, _) => {
                    log(level, &format!("Memory range: [0x{:x}, 0x{:x}) concrete", range.start, range.end))
                }
            }
        }
    }

    pub fn add_symbolic_region(&mut self, range: Range<Address>) {
        self.regions.push(Region::Symbolic(range))
    }

    pub fn add_concrete_region(&mut self, range: Range<Address>, contents: HashMap<Address, u8>) {
        self.regions.push(Region::Concrete(range, contents))
    }

    pub fn write_byte(&mut self, address: Address, byte: u8) {
        for region in &mut self.regions {
            match region {
                Region::Concrete(range, contents) if range.contains(&address) => {
                    contents.insert(address, byte);
                    return ()
                }
                _ => (),
            }
        }
        self.regions.push(Region::Concrete(address..address, vec![(address, byte)].into_iter().collect()))
    }

    /// Read from the memory region determined by the address. If the address is symbolic the read
    /// value is always also symbolic. The number of bytes must be concrete otherwise will return a
    /// SymbolicLength error.
    ///
    /// # Panics
    ///
    /// Panics if the number of bytes to read is concrete but does not fit
    /// in a u32, which should never be the case.
    pub fn read(&self, read_kind: Val, address: Val, bytes: Val, solver: &mut Solver) -> Result<Val, Error> {
        if let Val::I128(bytes) = bytes {
            let bytes = u32::try_from(bytes).expect("Bytes did not fit in u32 in memory read");

            if let Val::Bits(concrete_addr) = address {
                for region in &self.regions {
                    match region {
                        Region::Symbolic(range) if range.contains(&concrete_addr.bits) => {
                            return read_symbolic(read_kind, address, bytes, solver)
                        }

                        Region::Concrete(range, contents) if range.contains(&concrete_addr.bits) => {
                            return read_concrete(contents, concrete_addr.bits, bytes)
                        }

                        _ => continue,
                    }
                }

                read_symbolic(read_kind, address, bytes, solver)
            } else {
                read_symbolic(read_kind, address, bytes, solver)
            }
        } else {
            Err(Error::SymbolicLength("read_symbolic"))
        }
    }

    pub fn write(&mut self, write_kind: Val, address: Val, data: Val, solver: &mut Solver) -> Result<Val, Error> {
        if let Val::Bits(_) = address {
            write_symbolic(write_kind, address, data, solver)
        } else {
            write_symbolic(write_kind, address, data, solver)
        }
    }
}

fn read_concrete(region: &HashMap<Address, u8>, address: Address, bytes: u32) -> Result<Val, Error> {
    let mut byte_vec: Vec<u8> = Vec::new();
    for i in address..(address + u64::from(bytes)) {
       byte_vec.push(*region.get(&i).unwrap_or(&0))
    }

    if byte_vec.len() <= 8 {
        Ok(Val::Bits(Sbits::from_bytes(&byte_vec)))
    } else {
        // TODO: Handle reads > 64 bits
        Err(Error::BadRead)
    }
}

/// The simplest read is to symbolically read a memory location. In
/// that case we just return a fresh SMT bitvector of the appropriate
/// size, and add a ReadMem event to the trace. For this we need the
/// number of bytes to be non-symbolic.
fn read_symbolic(read_kind: Val, address: Val, bytes: u32, solver: &mut Solver) -> Result<Val, Error> {
    use crate::smt::smtlib::*;

    let value = solver.fresh();
    solver.add(Def::DeclareConst(value, Ty::BitVec(8 * bytes)));
    solver.add_event(Event::ReadMem { value, read_kind, address, bytes });

    Ok(Val::Symbolic(value))
}

/// `write_symbolic` just adds a WriteMem event to the trace,
/// returning a symbolic boolean (the semantics of which is controlled
/// by a memory model if required, but can be ignored in
/// others). Raises a type error if the data argument is not a
/// bitvector with a length that is a multiple of 8. This should be
/// guaranteed by the Sail type system.
fn write_symbolic(write_kind: Val, address: Val, data: Val, solver: &mut Solver) -> Result<Val, Error> {
    use crate::smt::smtlib::*;

    let data_length = crate::primop::length_bits(&data, solver)?;
    if data_length % 8 != 0 {
        return Err(Error::Type("write_symbolic"));
    };
    let bytes = data_length / 8;

    let value = solver.fresh();
    solver.add(Def::DeclareConst(value, Ty::Bool));
    solver.add_event(Event::WriteMem { value, write_kind, address, data, bytes });

    Ok(Val::Symbolic(value))
}
