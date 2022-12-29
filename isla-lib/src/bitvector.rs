// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
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

//! This module defines the bitvector trait BV, and includes modules
//! for concrete bitvectors of up to 64-bits, or up to 129-bits.
//!
//! The 129-bit bitvectors are intended for CHERI architectures as it
//! allows capabilities to be represented without involving the SMT
//! solver. Most functions in isla-lib and dependent libraries will be
//! parametric over the BV trait.
//!
//! The reason for having an upper-bound on the size of concrete
//! bitvectors is so they can be fixed size, which allows them to be
//! Copy types in Rust. This does not affect expressivity, just that
//! longer concrete bitvectors will be represented in the SMT solver,
//! and appear as [crate::ir::Val::Symbolic] values (as defined the
//! [crate::ir] module).

use serde::de::DeserializeOwned;
use serde::Serialize;
#[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
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

pub mod b129;
pub mod b64;

/// If we are indexing a vector of length `n`, we require this many
/// bits to represent all possible indices.
pub fn required_index_bits(n: usize) -> u32 {
    ((std::mem::size_of::<usize>() * 8) as u32) - n.saturating_sub(1).leading_zeros()
}

/// Read a vector of bits from a string, which can be in either
/// hexadecimal (starting `0x` or `#x`) or binary (starting `0b` or
/// `#b`). The bitvector length is determined by the length of the
/// string, four times the number of digit characters for hexadecimal,
/// and the exact number of characters for binary (so leading zeros
/// are not ignored).
///
/// We also allow a prefix of `0c` or `#c` for exactly 129-bit CHERI
/// capabilities, where the first bit can either be a `0` or `1`
/// followed by 32 hexadecimal digits.
///
/// This method will parse `0x`, `#x`, `0b`, and `#b` as the empty
/// bitvector.
pub fn bit_vector_from_str(s: &str) -> Option<Vec<bool>> {
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("#x")) {
        let size = 4 * hex.len();
        let mut value = vec![false; size];
        let mut i = size;
        for c in hex.chars() {
            i -= 4;
            let mut digit = c.to_digit(16)?;
            for j in 0..4 {
                value[i + j] = digit & 1 == 1;
                digit >>= 1;
            }
        }
        Some(value)
    } else if let Some(bin) = s.strip_prefix("0b").or_else(|| s.strip_prefix("#b")) {
        let size = bin.len();
        let mut value = vec![false; size];
        for (i, c) in bin.char_indices() {
            match c {
                '0' => (),
                '1' => value[size - i - 1] = true,
                _ => return None,
            }
        }
        Some(value)
    } else if let Some(cap) = s.strip_prefix("0c").or_else(|| s.strip_prefix("#c")) {
        let mut value = vec![false; 129];
        let tag_bit = &cap[0..1];
        if tag_bit != "0" && tag_bit != "1" {
            return None;
        }
        let mut i = 128;
        value[i] = tag_bit == "1";
        for c in cap[1..].chars() {
            i -= 4;
            let mut digit = c.to_digit(16)?;
            for j in 0..4 {
                value[i + j] = digit & 1 == 1;
                digit >>= 1;
            }
        }
        Some(value)
    } else {
        None
    }
}

/// Each concrete bitvector type has a maximum length, so when we read
/// a bitvector from a string we may not be able to fit it inside our
/// type. This enumeration allows for a fallback using a vector of
/// bits via [bit_vector_from_str] when `B::from_str` fails.
pub enum ParsedBits<B> {
    Short(B),
    Long(Vec<bool>),
}

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
    Self: 'static,
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

    fn zero_width() -> Self {
        BV::new(0, 0)
    }

    fn len(self) -> u32;

    fn lower_u64(self) -> u64;

    fn lower_u8(self) -> u8;

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

    fn leading_zeros(self) -> u32;

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

    fn to_le_bytes(self) -> Vec<u8>;
    fn to_be_bytes(self) -> Vec<u8>;

    /// Parses a bitvector from a string slice. String must be
    /// prefixed by either #x/0x, or #b/0b (allowing both SMT style
    /// and Sail/C style prefixes) for hexadecimal or binary. Returns
    /// `None` if the string is not parseable for any reason
    fn from_str(s: &str) -> Option<Self>;

    fn from_str_long(s: &str) -> Option<ParsedBits<Self>> {
        if let Some(bv) = Self::from_str(s) {
            Some(ParsedBits::Short(bv))
        } else {
            bit_vector_from_str(s).map(ParsedBits::Long)
        }
    }

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
        } else if shift >= self.len() as i128 {
            Self::zeros(self.len())
        } else {
            self >> Self::new(shift as u64, self.len())
        }
    }

    fn arith_shiftr(self, shift: i128) -> Self {
        if shift < 0 {
            self.shiftl(shift.abs())
        } else if shift >= self.len() as i128 {
            if self.leading_zeros() > 0 {
                Self::zeros(self.len())
            } else {
                Self::ones(self.len())
            }
        } else if self.leading_zeros() > 0 {
            self.shiftr(shift)
        } else {
            self.shiftr(shift).slice(0, self.len() - shift as u32).unwrap().sign_extend(self.len())
        }
    }

    fn shiftl(self, shift: i128) -> Self {
        if shift < 0 {
            self.shiftr(shift.abs())
        } else if shift >= self.len() as i128 {
            Self::zeros(self.len())
        } else {
            self << Self::new(shift as u64, self.len())
        }
    }

    fn truncate_lsb(self, len: i128) -> Option<Self> {
        if 0 < len && len <= Self::MAX_WIDTH as i128 {
            let len = len as u32;
            self.slice(self.len() - len, len)
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

    fn get_slice_int(len: u32, int: i128, n: u32) -> Self;

    fn to_vec(self) -> Vec<bool> {
        let mut bitvec = Vec::with_capacity(self.len().try_into().unwrap());
        for n in 0..self.len() {
            bitvec.push((self.shiftr(n as i128).lower_u64() & 1) == 1)
        }
        bitvec
    }
}

pub fn write_bits64(buf: &mut dyn Write, bits: u64, len: u32) -> std::io::Result<()> {
    if len % 4 == 0 {
        write!(buf, "#x")?
    } else {
        write!(buf, "#b")?
    }
    write_bits!(buf, bits, len)
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "bmi2")))]
pub fn bzhi_u64(bits: u64, len: u32) -> u64 {
    let lt64_mask = ((len < 64) as u64).wrapping_neg();
    bits & (1u64.wrapping_shl(len) & lt64_mask).wrapping_sub(1)
}

pub fn bzhi_u128(bits: u128, len: u32) -> u128 {
    let lt128_mask = ((len < 128) as u128).wrapping_neg();
    bits & (1u128.wrapping_shl(len) & lt128_mask).wrapping_sub(1)
}

#[inline(always)]
#[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
pub fn bzhi_u64(bits: u64, len: u32) -> u64 {
    unsafe { _bzhi_u64(bits, len) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_required_index_bits() {
        assert_eq!(required_index_bits(0), 0);
        assert_eq!(required_index_bits(1), 0);
        assert_eq!(required_index_bits(2), 1);
        assert_eq!(required_index_bits(3), 2);
        assert_eq!(required_index_bits(4), 2);
        assert_eq!(required_index_bits(5), 3);
        assert_eq!(required_index_bits(32), 5);
        assert_eq!(required_index_bits(33), 6);
        assert_eq!(required_index_bits(usize::MAX), std::mem::size_of::<usize>() as u32 * 8);
    }

    #[test]
    fn test_bzhi_u64() {
        assert_eq!(bzhi_u64(u64::MAX, 32), 0xFFFF_FFFF);
        assert_eq!(bzhi_u64(u64::MAX, 16), 0xFFFF);
        assert_eq!(bzhi_u64(u64::MAX, 8), 0xFF);
        assert_eq!(bzhi_u64(u64::MAX, 4), 0xF);
        assert_eq!(bzhi_u64(u64::MAX, 0), 0);
        assert_eq!(bzhi_u64(u64::MAX, 1), 1);
        assert_eq!(bzhi_u64(u64::MAX, 63), u64::MAX >> 1);
        assert_eq!(bzhi_u64(u64::MAX, 64), u64::MAX);
        assert_eq!(bzhi_u64(u64::MAX, 65), u64::MAX);
    }

    #[test]
    fn test_bzhi_u128() {
        assert_eq!(bzhi_u128(u128::MAX, 32), 0xFFFF_FFFF);
        assert_eq!(bzhi_u128(u128::MAX, 16), 0xFFFF);
        assert_eq!(bzhi_u128(u128::MAX, 8), 0xFF);
        assert_eq!(bzhi_u128(u128::MAX, 4), 0xF);
        assert_eq!(bzhi_u128(u128::MAX, 0), 0);
        assert_eq!(bzhi_u128(u128::MAX, 1), 1);
        assert_eq!(bzhi_u128(u128::MAX, 127), u128::MAX >> 1);
        assert_eq!(bzhi_u128(u128::MAX, 128), u128::MAX);
        assert_eq!(bzhi_u128(u128::MAX, 129), u128::MAX);
    }

    #[test]
    fn test_bit_vector_from_str() {
        assert_eq!(bit_vector_from_str("#xE"), Some(vec![false, true, true, true]));
        assert_eq!(bit_vector_from_str("#xe"), Some(vec![false, true, true, true]));
        assert_eq!(bit_vector_from_str("0x2"), Some(vec![false, true, false, false]));
        assert_eq!(bit_vector_from_str("0x2E"), Some(vec![false, true, true, true, false, true, false, false]));
        assert_eq!(bit_vector_from_str("#b110"), Some(vec![false, true, true]));
        assert_eq!(bit_vector_from_str("0b1100"), Some(vec![false, false, true, true]));
        assert_eq!(bit_vector_from_str("not a bitvector"), None);
        assert_eq!(bit_vector_from_str("0x"), Some(Vec::new()));
        assert_eq!(bit_vector_from_str("#x"), Some(Vec::new()));
        assert_eq!(bit_vector_from_str("0b"), Some(Vec::new()));
        assert_eq!(bit_vector_from_str("#b"), Some(Vec::new()));
        assert_eq!(bit_vector_from_str("0b2"), None);
        assert_eq!(bit_vector_from_str("0xABG"), None);
        assert_eq!(bit_vector_from_str(""), None);
    }
}
