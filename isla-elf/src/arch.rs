// BSD 2-Clause License
//
// Copyright (c) 2021 Alasdair Armstrong
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

use isla_lib::bitvector::BV;

use crate::relocation_types::*;

pub mod aarch64;

pub struct AArch64;

pub trait AsBits {
    fn as_bits<B: BV>(&self) -> B;
}

impl AsBits for u32 {
    fn as_bits<B: BV>(&self) -> B {
        B::from_u32(*self)
    }
}

pub trait Architecture {
    type RelocationCode: Copy + 'static;
    type Opcode: AsBits;

    fn static_string() -> &'static str;

    fn r_type(code: Self::RelocationCode) -> u32;

    fn instructions_from_buffer(buf: &[u8]) -> Option<Vec<(u64, Self::Opcode)>>;

    fn relocations() -> &'static [TableEntry<Self::RelocationCode>];
}

impl Architecture for AArch64 {
    type RelocationCode = aarch64::RelocationCode;
    type Opcode = u32;

    fn static_string() -> &'static str {
        "AArch64"
    }

    fn r_type(code: aarch64::RelocationCode) -> u32 {
        code as u32
    }

    fn relocations() -> &'static [TableEntry<aarch64::RelocationCode>] {
        &aarch64::RELOCATION_TABLE
    }

    fn instructions_from_buffer(buf: &[u8]) -> Option<Vec<(u64, u32)>> {
        aarch64::instructions_from_buffer(buf)
    }
}

pub(crate) fn get_table_entry<A: Architecture>(code: u32) -> &'static TableEntry<A::RelocationCode> {
    for entry in A::relocations() {
        if A::r_type(entry.code) == code {
            return entry;
        }
    }
    // If we get an unknown relocation code, it's probably better to just fail fast
    panic!("Unknown relocation code {} for architecture {}!", code, A::static_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aarch64_immediate_length() {
        for entry in AArch64::relocations() {
            if let Immediate::NoImm = entry.immediate {
                ()
            } else {
                assert_eq!(
                    entry.immediate.len(),
                    entry.slice.len(),
                    "Testing immediate and slice size equivalent for {:?}",
                    entry.code
                )
            }
        }
    }
}
