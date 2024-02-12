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

//! This module defines a concrete bitvector type [B64] that can
//! represent bitvectors up to length 64.

use serde::{Deserialize, Serialize};
use std::convert::TryInto;
use std::fmt;
use std::ops::{Add, BitAnd, BitOr, BitXor, Neg, Not, Shl, Shr, Sub};
use std::u128;

use super::{bzhi_u128, bzhi_u64, BV};
use crate::error::ExecError;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct B64 {
    len: u32,
    bits: u64,
}

impl fmt::LowerHex for B64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(&self.bits, f)
    }
}

impl fmt::UpperHex for B64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperHex::fmt(&self.bits, f)
    }
}

impl fmt::Display for B64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.len % 4 == 0 {
            write!(f, "#x")?
        } else {
            write!(f, "#b")?
        }
        write_bits!(f, self.bits, self.len)
    }
}

impl TryInto<u64> for B64 {
    type Error = ExecError;

    fn try_into(self) -> Result<u64, ExecError> {
        Ok(self.bits)
    }
}

impl Not for B64 {
    type Output = B64;

    fn not(self) -> Self::Output {
        B64 { len: self.len, bits: bzhi_u64(!self.bits, self.len) }
    }
}

impl BitXor for B64 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        B64 { len: self.len, bits: self.bits ^ rhs.bits }
    }
}

impl BitOr for B64 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        B64 { len: self.len, bits: self.bits | rhs.bits }
    }
}

impl BitAnd for B64 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        B64 { len: self.len, bits: self.bits & rhs.bits }
    }
}

impl Neg for B64 {
    type Output = B64;

    fn neg(self) -> Self::Output {
        B64 { len: self.len, bits: bzhi_u64((-(self.bits as i64)) as u64, self.len) }
    }
}

impl Add<B64> for B64 {
    type Output = B64;

    fn add(self, rhs: Self) -> Self::Output {
        B64 { len: self.len, bits: bzhi_u64(self.bits.wrapping_add(rhs.bits), self.len) }
    }
}

impl Sub<B64> for B64 {
    type Output = B64;

    fn sub(self, rhs: Self) -> Self::Output {
        B64 { len: self.len, bits: bzhi_u64(self.bits.wrapping_sub(rhs.bits), self.len) }
    }
}

impl Shl<B64> for B64 {
    type Output = B64;

    fn shl(self, rhs: Self) -> Self::Output {
        if rhs.bits >= 64 {
            B64 { len: self.len, bits: 0 }
        } else {
            B64 { len: self.len, bits: bzhi_u64(self.bits << rhs.bits, self.len) }
        }
    }
}

impl Shr<B64> for B64 {
    type Output = B64;

    fn shr(self, rhs: Self) -> Self::Output {
        if rhs.bits >= 64 {
            B64 { len: self.len, bits: 0 }
        } else {
            B64 { len: self.len, bits: bzhi_u64(self.bits >> rhs.bits, self.len) }
        }
    }
}

impl BV for B64 {
    const BIT_ONE: Self = B64 { len: 1, bits: 1 };
    const BIT_ZERO: Self = B64 { len: 1, bits: 0 };
    const MAX_WIDTH: u32 = 64;

    fn new(bits: u64, len: u32) -> Self {
        assert!(len <= 64 && bits == bzhi_u64(bits, len));
        B64 { len, bits }
    }

    fn lower_u64(self) -> u64 {
        self.bits
    }

    fn lower_u8(self) -> u8 {
        (self.bits & 0xFF) as u8
    }

    fn is_zero(self) -> bool {
        self.bits == 0
    }

    fn zeros(len: u32) -> Self {
        assert!(len <= 64);
        B64 { len, bits: 0 }
    }

    fn ones(len: u32) -> Self {
        assert!(len <= 64);
        B64 { len, bits: bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, len) }
    }

    fn leading_zeros(self) -> u32 {
        self.bits.leading_zeros() - (64 - self.len)
    }

    fn from_u8(value: u8) -> Self {
        B64 { len: 8, bits: value as u64 }
    }

    fn from_u16(value: u16) -> Self {
        B64 { len: 16, bits: value as u64 }
    }

    fn from_u32(value: u32) -> Self {
        B64 { len: 32, bits: value as u64 }
    }

    fn from_u64(value: u64) -> Self {
        B64 { len: 64, bits: value }
    }

    fn from_bytes(bytes: &[u8]) -> Self {
        assert!(bytes.len() <= 8);
        let mut bits: u64 = 0;
        for byte in bytes {
            bits = (bits << 8) | (*byte as u64)
        }
        B64 { len: bytes.len() as u32 * 8, bits }
    }

    fn to_le_bytes(self) -> Vec<u8> {
        assert!(self.len % 8 == 0);
        self.bits.to_le_bytes()[..self.len as usize / 8].to_vec()
    }

    fn to_be_bytes(self) -> Vec<u8> {
        assert!(self.len % 8 == 0);
        self.bits.to_be_bytes()[8 - self.len as usize / 8..].to_vec()
    }

    fn from_str(s: &str) -> Option<Self> {
        if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("#x")) {
            let len = hex.len();
            if len == 0 {
                Some(B64::zero_width())
            } else if len <= 16 {
                Some(B64 { len: len as u32 * 4, bits: u64::from_str_radix(hex, 16).ok()? })
            } else {
                None
            }
        } else if let Some(bin) = s.strip_prefix("0b").or_else(|| s.strip_prefix("#b")) {
            let len = bin.len();
            if len == 0 {
                Some(B64::zero_width())
            } else if len <= 64 {
                Some(B64 { len: len as u32, bits: u64::from_str_radix(bin, 2).ok()? })
            } else {
                None
            }
        } else {
            None
        }
    }

    fn len(self) -> u32 {
        self.len
    }

    fn add_i128(self, op: i128) -> Self {
        B64 { len: self.len, bits: bzhi_u64(self.bits.wrapping_add(op as u64), self.len) }
    }

    fn zero_extend(self, new_len: u32) -> Self {
        assert!(self.len <= new_len && new_len <= 64);
        B64 { len: new_len, bits: self.bits }
    }

    fn sign_extend(self, new_len: u32) -> Self {
        assert!(self.len <= new_len && new_len <= 64);
        if self.len > 0 {
            if (self.bits >> (self.len - 1)) & 0b1 == 0b1 {
                let top = bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, new_len) & !bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, self.len);
                B64 { len: new_len, bits: self.bits | top }
            } else {
                B64 { len: new_len, bits: self.bits }
            }
        } else {
            B64 { len: new_len, bits: 0 }
        }
    }

    fn unsigned(self) -> i128 {
        i128::from(self.bits)
    }

    fn signed(self) -> i128 {
        i128::from(self.sign_extend(64).bits as i64)
    }

    fn slice(self, from: u32, len: u32) -> Option<Self> {
        if from + len <= self.len {
            Some(B64 { len, bits: bzhi_u64(self.bits >> from, len) })
        } else {
            None
        }
    }

    fn set_slice(self, n: u32, update: Self) -> Self {
        let mask = !bzhi_u64(0xFFFF_FFFF_FFFF_FFFF << n, n + update.len);
        let update = update.bits << n;
        B64 { len: self.len, bits: (self.bits & mask) | update }
    }

    fn set_slice_int(int: i128, n: u32, update: Self) -> i128 {
        let mask = !bzhi_u128(u128::max_value() << n, n + update.len());
        let update = (update.bits as u128) << n;
        ((int as u128 & mask) | update) as i128
    }

    fn get_slice_int(len: u32, int: i128, n: u32) -> Self {
        let slice = bzhi_u64((int >> n) as u64, len);
        Self::new(slice, len)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_bits64() {
        assert_eq!(format!("{}", B64::zeros(4)), "#x0");
        assert_eq!(format!("{}", B64::zeros(8)), "#x00");
        assert_eq!(format!("{}", B64::zeros(12)), "#x000");
        assert_eq!(format!("{}", B64::zeros(16)), "#x0000");

        assert_eq!(format!("{}", B64::ones(4)), "#xf");
        assert_eq!(format!("{}", B64::ones(8)), "#xff");
        assert_eq!(format!("{}", B64::ones(12)), "#xfff");
        assert_eq!(format!("{}", B64::ones(16)), "#xffff");

        assert_eq!(format!("{}", B64::from_u32(0xDEAD_BEEFu32)), "#xdeadbeef");

        assert_eq!(format!("{}", B64::new(0b101, 3)), "#b101");
        assert_eq!(format!("{}", B64::new(0b100, 3)), "#b100");
        assert_eq!(format!("{}", B64::new(0b001, 3)), "#b001");

        assert_eq!(format!("{}", B64::new(0x0000_0000_0000_0000, 64)), "#x0000000000000000");
    }

    #[test]
    fn test_from_bytes() {
        assert_eq!(B64::from_bytes(&[0xABu8, 0xCDu8]), B64::from_u16(0xABCDu16));
        assert_eq!(B64::from_bytes(&[0xABu8, 0xCDu8, 0xEFu8]), B64::new(0xABCDEF, 24));
    }

    #[test]
    fn test_add() {
        assert_eq!(B64::new(0xFFFF_FFFF_FFFF_FFFF, 64) + B64::new(1, 64), B64::new(0, 64));
        assert_eq!(B64::new(0xFF, 8) + B64::new(2, 8), B64::new(1, 8));
    }

    #[test]
    fn test_neg() {
        assert_eq!(-B64::new(0b000, 3), B64::new(0b000, 3));
        assert_eq!(-B64::new(0b001, 3), B64::new(0b111, 3));
        assert_eq!(-B64::new(0b010, 3), B64::new(0b110, 3));
        assert_eq!(-B64::new(0xFF, 8), B64::new(0x1, 8));
        assert_eq!(-B64::new(0xFFFF_FFFF_FFFF_FFFF, 64), B64::new(0x1, 64));
        assert_eq!(-B64::zero_width(), B64::zero_width());
    }

    #[test]
    fn test_shl() {
        assert!(B64::new(0b001, 3) << B64::new(2, 3) == B64::new(0b100, 3));
        assert!(B64::new(0b001, 3) << B64::new(3, 3) == B64::new(0b000, 3));
        assert!(B64::new(0x0000_0000_0000_0001, 64) << B64::new(64, 64) == B64::new(0, 64));
        assert!(B64::new(0x0000_0000_0000_0001, 64) << B64::new(65, 64) == B64::new(0, 64));
        assert!(B64::new(0xFFFF_FFFF_FFFF_FFFF, 64) << B64::new(64, 64) == B64::new(0, 64));
        assert!(B64::new(0xFFFF_FFFF_FFFF_FFFF, 64) << B64::new(66, 64) == B64::new(0, 64));
    }

    #[test]
    fn test_shr() {
        assert!(B64::new(0b100, 3) >> B64::new(2, 3) == B64::new(0b001, 3));
        assert!(B64::new(0b100, 3) >> B64::new(3, 3) == B64::new(0b000, 3));
        assert!(B64::new(0xFFFF_FFFF_FFFF_FFFF, 64) >> B64::new(64, 64) == B64::new(0, 64));
        assert!(B64::new(0xFFFF_FFFF_FFFF_FFFF, 64) >> B64::new(66, 64) == B64::new(0, 64));
    }

    #[test]
    fn test_zero_extend() {
        assert!(B64::new(0b100, 3).zero_extend(3) == B64::new(0b100, 3));
        assert!(B64::new(0b100, 3).zero_extend(6) == B64::new(0b000100, 6));
    }

    #[test]
    fn test_sign_extend() {
        assert!(B64::new(0b100, 3).sign_extend(6) == B64::new(0b111100, 6));
        assert!(B64::new(0b010, 3).sign_extend(6) == B64::new(0b000010, 6));
        assert!(B64::new(0b110, 3).sign_extend(3) == B64::new(0b110, 3));
        assert!(B64::new(0b010, 3).sign_extend(3) == B64::new(0b010, 3));
        assert!(B64::new(0xF, 4).sign_extend(8) == B64::new(0xFF, 8));
    }

    #[test]
    fn test_append() {
        let sbits_max = B64::new(0xFFFF_FFFF_FFFF_FFFF, 64);
        assert!(B64::new(0, 0).append(sbits_max) == Some(sbits_max));
        assert!(sbits_max.append(B64::new(0, 0)) == Some(sbits_max));
        assert!(sbits_max.append(sbits_max) == None);
        assert!(B64::new(0xCAFECAFE, 32).append(B64::new(0x1234ABCD, 32)) == Some(B64::new(0xCAFECAFE1234ABCD, 64)));
    }

    #[test]
    fn test_slice() {
        let sbits = B64::new(0xCAFE_F00D_1234_ABCD, 64);
        assert!(sbits.slice(0, 32) == Some(B64::new(0x1234_ABCD, 32)));
        assert!(sbits.slice(32, 32) == Some(B64::new(0xCAFE_F00D, 32)));
        assert!(sbits.slice(16, 16) == Some(B64::new(0x1234, 16)));
    }

    #[test]
    fn test_extract() {
        let sbits = B64::new(0xCAFE_F00D_1234_ABCD, 64);
        assert!(sbits.extract(31, 0) == Some(B64::new(0x1234_ABCD, 32)));
        assert!(sbits.extract(63, 32) == Some(B64::new(0xCAFE_F00D, 32)));
        assert!(sbits.extract(7, 0) == Some(B64::new(0xCD, 8)));
    }

    #[test]
    fn test_truncate_lsb() {
        let sbits = B64::new(0xCAFE_F00D_1234_ABCD, 64);
        assert!(sbits.truncate_lsb(16) == Some(B64::new(0xCAFE, 16)));
        assert!(sbits.truncate_lsb(64) == Some(sbits));
        assert!(sbits.truncate_lsb(0) == Some(B64::new(0, 0)));
    }

    #[test]
    fn test_signed() {
        assert!(B64::new(0b100, 3).signed() == -4);
        assert!(B64::new(0b011, 3).signed() == 3);
        assert!(B64::new(0b111, 3).signed() == -1);
        assert!(B64::new(0b000, 3).signed() == 0);
        assert!(B64::new(0b1, 1).signed() == -1);
    }

    #[test]
    fn test_unsigned() {
        assert!(B64::new(0b100, 3).unsigned() == 4);
        assert!(B64::new(0b011, 3).unsigned() == 3);
        assert!(B64::new(0b111, 3).unsigned() == 7);
        assert!(B64::new(0b000, 3).unsigned() == 0);
        assert!(B64::new(0b1, 1).unsigned() == 1);
    }

    #[test]
    fn test_replicate() {
        assert!(B64::new(0b101, 3).replicate(0) == Some(B64::new(0, 0)));
        assert!(B64::new(0b10, 2).replicate(3) == Some(B64::new(0b101010, 6)));
        assert!(B64::new(0xCAFE, 16).replicate(4) == Some(B64::new(0xCAFECAFECAFECAFE, 64)));
        assert!(B64::new(0b1, 1).replicate(128) == None);
    }

    #[test]
    fn test_set_slice() {
        assert!(B64::new(0b000, 3).set_slice(1, B64::new(0b1, 1)) == B64::new(0b010, 3));
        assert!(B64::new(0b111, 3).set_slice(1, B64::new(0b0, 1)) == B64::new(0b101, 3));
        assert!(B64::new(0b111, 3).set_slice(1, B64::new(0b1, 1)) == B64::new(0b111, 3));
        assert!(B64::new(0b000, 3).set_slice(1, B64::new(0b0, 1)) == B64::new(0b000, 3));
        assert!(B64::new(0xCAFE, 16).set_slice(4, B64::new(0x0, 4)) == B64::new(0xCA0E, 16));
        assert!(B64::new(0xFFFF, 16).set_slice(12, B64::new(0x0, 4)) == B64::new(0x0FFF, 16));
        assert!(B64::new(0xFFFF, 16).set_slice(8, B64::new(0x0, 4)) == B64::new(0xF0FF, 16));
        assert!(B64::new(0xFFFF, 16).set_slice(4, B64::new(0x0, 4)) == B64::new(0xFF0F, 16));
        assert!(B64::new(0xFFFF, 16).set_slice(0, B64::new(0x0, 4)) == B64::new(0xFFF0, 16));
    }

    #[test]
    fn test_leading_zeros() {
        assert_eq!(B64::new(0b001, 3).leading_zeros(), 2);
        assert_eq!(B64::new(0b010, 3).leading_zeros(), 1);
        assert_eq!(B64::new(0b00001, 5).leading_zeros(), 4);
        assert_eq!(B64::new(0, 32).leading_zeros(), 32);
        assert_eq!(B64::new(0, 64).leading_zeros(), 64);
        assert_eq!(B64::new(0xFFFF_FFFF_FFFF_FFFF, 64).leading_zeros(), 0);
    }

    #[test]
    fn test_set_slice_int() {
        assert!(B64::set_slice_int(15, 1, B64::new(0, 2)) == 9)
    }

    #[test]
    fn test_arith_shiftr() {
        assert_eq!(B64::new(0b100, 3).arith_shiftr(0), B64::new(0b100, 3));
        assert_eq!(B64::new(0b100, 3).arith_shiftr(1), B64::new(0b110, 3));
        assert_eq!(B64::new(0b100, 3).arith_shiftr(2), B64::new(0b111, 3));
        assert_eq!(B64::new(0b100, 3).arith_shiftr(3), B64::new(0b111, 3));
        assert_eq!(B64::new(0b100, 3).arith_shiftr(4), B64::new(0b111, 3));

        assert_eq!(B64::new(0b0110, 4).arith_shiftr(2), B64::new(0b0001, 4));
    }

    #[test]
    fn test_to_bytes() {
        assert_eq!(B64::new(0x123456, 24).to_le_bytes(), [0x56, 0x34, 0x12]);
        assert_eq!(B64::new(0x123456, 24).to_be_bytes(), [0x12, 0x34, 0x56]);
    }

    #[test]
    fn test_format_empty_bv() {
        assert_eq!(&format!("{}", B64::zero_width()), "#x")
    }

    #[test]
    fn test_from_str() {
        assert_eq!(B64::from_str("0x"), Some(B64::zero_width()));
        assert_eq!(B64::from_str("#b"), Some(B64::zero_width()));
        assert_eq!(B64::from_str("#xFFFF_FFFF_FFFF_FFFF_FFFF"), None);

        let mut bitpat: u64 = 0x01234_5679_ABCD_EF00;

        for len in 0u32..64 {
            bitpat = bitpat.rotate_left(1);
            let bv = B64::new(bzhi_u64(bitpat, len), len);
            assert_eq!(B64::from_str(&format!("{}", bv)), Some(bv))
        }
    }
}
