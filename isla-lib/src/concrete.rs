// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
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

use serde::de::DeserializeOwned;
use serde::Serialize;
use std::arch::x86_64::_bzhi_u64;
use std::convert::TryInto;
use std::fmt;
use std::hash::Hash;
use std::io::Write;
use std::ops::{Add, BitAnd, BitOr, BitXor, Neg, Not, Shl, Shr, Sub};

use crate::error::ExecError;

#[macro_export]
macro_rules! write_bits {
    ($f: expr, $bits: expr, $len: expr) => {{
        if $len == 4 {
            write!($f, "{:x}", $bits & 0xF)?
        } else if $len % 4 == 0 {
            for i in (0..($len / 4)).rev() {
                write!($f, "{:x}", ($bits >> (i * 4)) & 0xF)?;
            }
        } else {
            for i in (0..$len).rev() {
                write!($f, "{:b}", ($bits >> i) & 0b1)?;
            }
        }
        Ok(())
    }};
}

pub mod bitvector129;
pub mod bitvector64;

/// This trait allows us to be generic over the representation of
/// concrete bitvectors. Specific users of isla-lib may then choose
/// different representations depending on use case - B64 will likely
/// be the most efficient for ordinary use, but B129 can represent
/// [CHERI](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/)
/// compressed capabilities concretely.
pub trait BV
where
    Self: fmt::Debug + fmt::LowerHex + fmt::UpperHex + fmt::Display,
    Self: Copy + Clone + PartialEq + Eq + Hash + Send + Sync,
    Self: Serialize + DeserializeOwned,
    Self: Add<Output = Self>,
    Self: Sub<Output = Self>,
    Self: BitAnd<Output = Self>,
    Self: BitOr<Output = Self>,
    Self: BitXor<Output = Self>,
    Self: Not<Output = Self>,
    Self: Neg<Output = Self>,
    Self: Shl<Output = Self>,
    Self: Shr<Output = Self>,
    Self: TryInto<u64, Error = ExecError>,
{
    const BIT_ONE: Self;
    const BIT_ZERO: Self;

    /// In Isla concrete bitvectors are only represented up to a
    /// specific maximum width/length. Beyond this they will be
    /// promoted to symbolic variables which are equal to a concrete
    /// value represented in the SMT solver. This makes computation
    /// over concrete bitvectors below this max width very efficient,
    /// as they can be represented as simple Copy types like `u64`.
    const MAX_WIDTH: u32;

    fn new(value: u64, len: u32) -> Self;

    fn len(self) -> u32;

    fn lower_u64(self) -> u64;

    fn is_zero(self) -> bool;

    /// Make a small bitvector of all zeros.
    ///
    /// # Panics
    ///
    /// `len` must be less than or equal to `MAX_WIDTH`
    fn zeros(len: u32) -> Self;

    /// Make a small bitvector of all ones.
    ///
    /// # Panics
    ///
    /// `len` must be less than or equal to `MAX_WIDTH`
    fn ones(len: u32) -> Self;

    fn from_u8(value: u8) -> Self;

    fn from_u16(value: u16) -> Self;

    fn from_u32(value: u32) -> Self;

    fn from_u64(value: u64) -> Self;

    /// Byte order is: from_bytes(&[0xAB, 0xCD, 0xEF] == 0xABCDEF
    ///
    /// # Panics
    ///
    /// bytes.len() * 8 must be less than or equal to `MAX_WIDTH`
    fn from_bytes(bytes: &[u8]) -> Self;

    /// Parses a bitvector from a string slice. String must be
    /// prefixed by either #x/0x, or #b/0b (allowing both SMT style
    /// and Sail/C style prefixes) for hexadecimal or binary. Returns
    /// `None` if the string is not parseable for any reason
    fn from_str(bv: &str) -> Option<Self>;

    fn len_i128(self) -> i128 {
        i128::from(self.len())
    }

    fn is_empty(self) -> bool {
        self.len() == 0
    }

    fn add_i128(self, op: i128) -> Self;

    fn sub_i128(self, op: i128) -> Self {
        self.add_i128(-op)
    }

    /// zero_extend a bitvector to a specific new length.
    ///
    /// # Panics
    ///
    /// `new_len` must be greater than the current length, but less
    /// than `MAX_WIDTH`.
    fn zero_extend(self, new_len: u32) -> Self;

    /// sign_extend a bitvector to a specific new length. Sign
    /// extending a zero-length bitvector creates a `new_len` sized
    /// bitvector containing only zeros.
    ///
    /// # Panics
    ///
    /// `new_len` must be greater than the current length, but less
    /// than `MAX_WIDTH`.
    fn sign_extend(self, new_len: u32) -> Self;

    fn unsigned(self) -> i128;

    fn signed(self) -> i128;

    fn append(self, suffix: Self) -> Option<Self> {
        let new_len = self.len() + suffix.len();
        if new_len <= Self::MAX_WIDTH {
            let shift = Self::new(u64::from(suffix.len()), new_len);
            Some(self.zero_extend(new_len) << shift | suffix.zero_extend(new_len))
        } else {
            None
        }
    }

    fn slice(self, from: u32, len: u32) -> Option<Self>;

    fn set_slice(self, n: u32, update: Self) -> Self;

    fn extract(self, high: u32, low: u32) -> Option<Self> {
        let len = (high - low) + 1;
        if low <= high && high <= self.len() {
            self.slice(low, len)
        } else {
            None
        }
    }

    fn shiftr(self, shift: i128) -> Self {
        if shift < 0 {
            self.shiftl(shift.abs())
        } else if shift >= 64 {
            Self::zeros(self.len())
        } else {
            self >> Self::new(shift as u64, self.len())
        }
    }

    fn shiftl(self, shift: i128) -> Self {
        if shift < 0 {
            self.shiftr(shift.abs())
        } else if shift >= 64 {
            Self::zeros(self.len())
        } else {
            self << Self::new(shift as u64, self.len())
        }
    }

    fn truncate_lsb(self, len: i128) -> Option<Self> {
        if 0 < len && len <= Self::MAX_WIDTH as i128 {
            let len = len as u64;
            (self >> Self::new(64 - len, self.len())).slice(0, len as u32)
        } else if len == 0 {
            Some(Self::new(0, 0))
        } else {
            None
        }
    }

    fn replicate(self, times: i128) -> Option<Self> {
        if times == 0 {
            Some(Self::new(0, 0))
        } else if 0 <= times && self.len() as i128 * times <= Self::MAX_WIDTH as i128 {
            let mut bv = self;
            for _ in 1..times {
                bv = bv.append(self).unwrap()
            }
            Some(bv)
        } else {
            None
        }
    }

    fn set_slice_int(int: i128, n: u32, update: Self) -> i128;
}

pub fn write_bits64(buf: &mut dyn Write, bits: u64, len: u32) -> std::io::Result<()> {
    if len % 4 == 0 {
        write!(buf, "#x")?
    } else {
        write!(buf, "#b")?
    }
    write_bits!(buf, bits, len)
}

#[inline(always)]
pub fn bzhi_u64(bits: u64, len: u32) -> u64 {
    unsafe { _bzhi_u64(bits, len) }
}

pub fn bzhi_u128(bits: u128, len: u32) -> u128 {
    bits & (std::u128::MAX >> (128 - len))
}
