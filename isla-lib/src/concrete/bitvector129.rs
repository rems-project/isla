// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
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

use serde::{Deserialize, Serialize};
use std::convert::TryFrom;
use std::convert::TryInto;
use std::fmt;
use std::ops::{Add, BitAnd, BitOr, BitXor, Neg, Not, Shl, Shr, Sub};
use std::u128;

use super::{bzhi_u128, BV};
use crate::error::ExecError;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct B129 {
    tag: bool,
    bits: u128,
    len: u32,
}

impl fmt::LowerHex for B129 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.len <= 128 || !self.tag {
            write!(f, "{:x}", self.bits)
        } else {
            write!(f, "1{:0>32x}", self.bits)
        }
    }
}

impl fmt::UpperHex for B129 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.len <= 128 || !self.tag {
            write!(f, "{:X}", self.bits)
        } else {
            write!(f, "1{:0>32X}", self.bits)
        }
    }
}

impl fmt::Display for B129 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.len % 4 == 0 {
            write!(f, "#x")?
        } else {
            write!(f, "#b")?
        }
        if self.len == 129 {
            if self.tag {
                write!(f, "1")?
            } else {
                write!(f, "0")?
            }
            write_bits!(f, self.bits, 128)
        } else {
            write_bits!(f, self.bits, self.len)
        }
    }
}

impl TryInto<u64> for B129 {
    type Error = ExecError;

    fn try_into(self) -> Result<u64, ExecError> {
        if self.len <= 64 {
            Ok(self.bits as u64)
        } else {
            Err(ExecError::Overflow)
        }
    }
}

fn bzhi(bv: B129, len: u32) -> B129 {
    if len > 128 {
        bv
    } else {
        B129 { len: bv.len, tag: false, bits: bzhi_u128(bv.bits, len) }
    }
}

impl Not for B129 {
    type Output = B129;

    fn not(self) -> Self::Output {
        bzhi(B129 { len: self.len, tag: !self.tag, bits: !self.bits }, self.len)
    }
}

impl BitXor for B129 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        B129 { len: self.len, tag: self.tag ^ rhs.tag, bits: self.bits ^ rhs.bits }
    }
}

impl BitOr for B129 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        B129 { len: self.len, tag: self.tag | rhs.tag, bits: self.bits | rhs.bits }
    }
}

impl BitAnd for B129 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        B129 { len: self.len, tag: self.tag & rhs.tag, bits: self.bits & rhs.bits }
    }
}

impl Add<B129> for B129 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let (sum, carry) = self.bits.overflowing_add(rhs.bits);
        bzhi(B129 { len: self.len, tag: self.tag ^ rhs.tag ^ carry, bits: sum }, self.len)
    }
}

impl Neg for B129 {
    type Output = B129;

    fn neg(self) -> Self::Output {
        !self + B129 { len: self.len, tag: false, bits: 1 }
    }
}

impl Sub<B129> for B129 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl Shl<B129> for B129 {
    type Output = B129;

    fn shl(self, rhs: Self) -> Self::Output {
        if rhs.bits >= 129 || rhs.tag {
            B129 { len: self.len, tag: false, bits: 0 }
        } else if rhs.bits == 128 {
            bzhi(B129 { len: self.len, tag: rhs.bits & 0b1 == 0b1, bits: 0 }, self.len)
        } else if rhs.bits == 0 {
            self
        } else {
            let tag = (self.bits >> (128 - rhs.bits)) & 0b1 == 0b1;
            bzhi(B129 { len: self.len, tag, bits: self.bits << rhs.bits }, self.len)
        }
    }
}

impl Shr<B129> for B129 {
    type Output = B129;

    fn shr(self, rhs: Self) -> Self::Output {
        if rhs.bits >= 129 || rhs.tag {
            B129 { len: self.len, tag: false, bits: 0 }
        } else if rhs.bits == 128 {
            bzhi(B129 { len: self.len, tag: false, bits: if self.tag { 1 } else { 0 } }, self.len)
        } else if rhs.bits == 0 {
            self
        } else {
            let mask = if self.tag { 0b1 << (128 - rhs.bits) } else { 0 };
            bzhi(B129 { len: self.len, tag: false, bits: (self.bits >> rhs.bits) | mask }, self.len)
        }
    }
}

fn shift_u32(bits: u32, len: u32) -> B129 {
    B129 { len, tag: false, bits: bits as u128 }
}

const ALL_ONES_129: B129 = B129 { tag: true, bits: u128::MAX, len: 129 };

impl BV for B129 {
    const BIT_ONE: Self = B129 { len: 1, tag: false, bits: 1 };
    const BIT_ZERO: Self = B129 { len: 1, tag: false, bits: 0 };
    const MAX_WIDTH: u32 = 129;

    fn new(bits: u64, len: u32) -> Self {
        assert!(len <= 129);
        B129 { len, tag: false, bits: bits as u128 }
    }

    fn len(self) -> u32 {
        self.len
    }

    fn lower_u64(self) -> u64 {
        self.bits as u64
    }

    fn is_zero(self) -> bool {
        !self.tag && self.bits == 0
    }

    fn zeros(len: u32) -> Self {
        B129 { len, tag: false, bits: 0 }
    }

    fn ones(len: u32) -> Self {
        bzhi(B129 { len, tag: true, bits: u128::MAX }, len)
    }

    fn leading_zeros(self) -> u32 {
        if self.tag {
            0
        } else {
            (self.bits.leading_zeros() + 1) - (129 - self.len)
        }
    }

    fn from_u8(value: u8) -> Self {
        B129 { len: 8, tag: false, bits: value as u128 }
    }

    fn from_u16(value: u16) -> Self {
        B129 { len: 16, tag: false, bits: value as u128 }
    }

    fn from_u32(value: u32) -> Self {
        B129 { len: 32, tag: false, bits: value as u128 }
    }

    fn from_u64(value: u64) -> Self {
        B129 { len: 64, tag: false, bits: value as u128 }
    }

    fn from_bytes(bytes: &[u8]) -> Self {
        assert!(bytes.len() <= 16);
        let mut bits: u128 = 0;
        for byte in bytes {
            bits = (bits << 8) | (*byte as u128)
        }
        B129 { len: bytes.len() as u32 * 8, tag: false, bits }
    }

    fn to_le_bytes(self) -> Vec<u8> {
        assert!(self.len % 8 == 0);
        self.bits.to_le_bytes()[..self.len as usize / 8].to_vec()
    }

    fn to_be_bytes(self) -> Vec<u8> {
        assert!(self.len % 8 == 0);
        self.bits.to_be_bytes()[16 - self.len as usize / 8..].to_vec()
    }

    fn zero_extend(self, new_len: u32) -> Self {
        assert!(self.len <= new_len && new_len <= 129);
        B129 { len: new_len, tag: self.tag, bits: self.bits }
    }

    fn sign_extend(self, new_len: u32) -> Self {
        assert!(self.len <= new_len && new_len <= 129);
        if self.len == 0 {
            B129 { len: new_len, tag: false, bits: 0 }
        } else if new_len < 129 {
            if (self.bits >> (self.len - 1)) & 1 == 1 {
                let top = bzhi_u128(u128::MAX, new_len) & !bzhi_u128(u128::MAX, self.len);
                B129 { len: new_len, tag: false, bits: self.bits | top }
            } else {
                B129 { len: new_len, tag: false, bits: self.bits }
            }
        } else if self.len == 129 {
            self
        } else {
            // new_len == 129 && self.len < 129
            if (self.bits >> (self.len - 1)) & 0b1 == 0b1 {
                B129 { len: new_len, tag: true, bits: self.bits | !bzhi_u128(u128::MAX, self.len) }
            } else {
                B129 { len: new_len, tag: false, bits: self.bits }
            }
        }
    }

    fn unsigned(self) -> i128 {
        assert!(!self.tag);
        i128::try_from(self.bits).unwrap()
    }

    fn signed(self) -> i128 {
        if self.tag {
            assert!(self.bits & 0x8000_0000_0000_0000_0000_0000_0000_0000 != 0);
            self.bits as i128
        } else {
            assert!(self.bits & 0x8000_0000_0000_0000_0000_0000_0000_0000 == 0);
            self.bits as i128
        }
    }

    fn slice(self, from: u32, len: u32) -> Option<Self> {
        if from + len <= self.len {
            Some(bzhi(B129 { len, ..self >> shift_u32(from, self.len) }, len))
        } else {
            None
        }
    }

    fn from_str(bv: &str) -> Option<Self> {
        if bv.len() <= 2 || !(bv.starts_with('#') || bv.starts_with('0')) {
            return None;
        }

        match bv.chars().nth(1) {
            Some('x') => {
                let hex = &bv[2..];
                let len = hex.len();
                if len <= 32 {
                    Some(B129 { len: len as u32 * 4, tag: false, bits: u128::from_str_radix(hex, 16).ok()? })
                } else {
                    None
                }
            }
            Some('b') => {
                let bin = &bv[2..];
                let len = bin.len();
                if len <= 128 {
                    Some(B129 { len: len as u32, tag: false, bits: u128::from_str_radix(bin, 2).ok()? })
                } else if len == 129 {
                    let tag_bit = &bin[0..1];
                    if tag_bit != "0" && tag_bit != "1" {
                        return None;
                    }
                    Some(B129 { len: len as u32, tag: tag_bit == "1", bits: u128::from_str_radix(&bin[1..], 2).ok()? })
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn add_i128(self, op: i128) -> Self {
        if op > 0 {
            self + bzhi(B129 { len: self.len, tag: false, bits: op as u128 }, self.len)
        } else {
            self + bzhi(B129 { len: self.len, tag: true, bits: op as u128 }, self.len)
        }
    }

    fn set_slice(self, n: u32, update: Self) -> Self {
        let mask = (ALL_ONES_129 << shift_u32(n, 129)).slice(0, n + update.len).unwrap().zero_extend(self.len);
        let update = update.zero_extend(self.len) << shift_u32(n, self.len);
        (self & !mask) | update
    }

    fn set_slice_int(int: i128, n: u32, update: Self) -> i128 {
        assert!(update.len <= 128);
        let mask = !bzhi_u128(u128::max_value() << n, n as u32 + update.len());
        let update = (update.bits as u128) << n;
        ((int as u128 & mask) | update) as i128
    }

    fn get_slice_int(len: u32, int: i128, n: u32) -> Self {
        assert!(len <= 128);
        B129 { len, tag: false, bits: bzhi_u128((int >> n) as u128, len) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::u128;

    const JUST_TAG: B129 = B129 { tag: true, bits: 0, len: 129 };

    const ONE_129: B129 = B129 { tag: false, bits: 1, len: 129 };

    const TWO_129: B129 = B129 { tag: false, bits: 2, len: 129 };

    const ALL_ONES_129: B129 = B129 { tag: true, bits: u128::MAX, len: 129 };

    const ALL_ZEROS_129: B129 = B129 { tag: false, bits: 0, len: 129 };

    #[test]
    fn test_lower_hex() {
        assert_eq!(format!("0x{:x}", ALL_ONES_129), "0x1ffffffffffffffffffffffffffffffff");
        assert_eq!(
            format!("0x{:x}", B129 { tag: false, bits: u128::MAX, len: 129 }),
            "0xffffffffffffffffffffffffffffffff"
        );
        assert_eq!(
            format!("0x{:x}", B129 { tag: false, bits: u128::MAX, len: 128 }),
            "0xffffffffffffffffffffffffffffffff"
        );
        assert_eq!(format!("0x{:x}", B129 { tag: false, bits: 0, len: 129 }), "0x0");
        assert_eq!(format!("0x{:x}", JUST_TAG), "0x100000000000000000000000000000000")
    }

    #[test]
    fn test_upper_hex() {
        assert_eq!(format!("0x{:X}", ALL_ONES_129), "0x1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
        assert_eq!(
            format!("0x{:X}", B129 { tag: false, bits: u128::MAX, len: 129 }),
            "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
        );
        assert_eq!(
            format!("0x{:X}", B129 { tag: false, bits: u128::MAX, len: 128 }),
            "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
        );
        assert_eq!(format!("0x{:X}", B129 { tag: false, bits: 0, len: 129 }), "0x0");
        assert_eq!(format!("0x{:X}", JUST_TAG), "0x100000000000000000000000000000000")
    }

    #[test]
    fn test_not() {
        assert_eq!(!ALL_ONES_129, ALL_ZEROS_129);
        assert_eq!(!JUST_TAG, B129 { tag: false, bits: u128::MAX, len: 129 });
        assert_eq!(!B129 { tag: false, bits: 0xFF, len: 8 }, B129 { tag: false, bits: 0, len: 8 });
    }

    #[test]
    fn test_bitxor() {
        assert_eq!(ALL_ONES_129 ^ ALL_ZEROS_129, ALL_ONES_129);
        assert_eq!(ALL_ONES_129 ^ ALL_ONES_129, ALL_ZEROS_129)
    }

    #[test]
    fn test_bitor() {
        assert_eq!(ALL_ONES_129 | ALL_ZEROS_129, ALL_ONES_129);
        assert_eq!(ALL_ONES_129 | ALL_ONES_129, ALL_ONES_129)
    }

    #[test]
    fn test_bitand() {
        assert_eq!(ALL_ONES_129 & ALL_ZEROS_129, ALL_ZEROS_129);
        assert_eq!(ALL_ONES_129 & ALL_ONES_129, ALL_ONES_129)
    }

    #[test]
    fn test_add() {
        assert_eq!(ALL_ONES_129 + ONE_129, ALL_ZEROS_129);
        assert_eq!(ALL_ONES_129 + TWO_129, ONE_129);
        assert_eq!(ONE_129 + ONE_129, TWO_129);
        assert_eq!(B129 { tag: false, ..ALL_ONES_129 } + ONE_129, JUST_TAG);
        assert_eq!(JUST_TAG + JUST_TAG, ALL_ZEROS_129);
    }

    #[test]
    fn test_sub() {
        assert_eq!(ALL_ONES_129 - JUST_TAG, B129 { tag: false, ..ALL_ONES_129 });
        assert_eq!(ALL_ONES_129 - ONE_129, ALL_ONES_129 & !ONE_129);
        assert_eq!(TWO_129 - TWO_129, ALL_ZEROS_129);
        assert_eq!(TWO_129 - ONE_129, ONE_129)
    }

    #[test]
    fn test_leading_zeros() {
        assert_eq!(ALL_ONES_129.leading_zeros(), 0);
        assert_eq!(ALL_ZEROS_129.leading_zeros(), 129);
        assert_eq!(JUST_TAG.leading_zeros(), 0);
        assert_eq!(ONE_129.leading_zeros(), 128);
        assert_eq!(B129::new(0b001, 3).leading_zeros(), 2);
        assert_eq!(B129::new(0b010, 3).leading_zeros(), 1);
        assert_eq!(B129::new(0b00001, 5).leading_zeros(), 4);
        assert_eq!(B129::new(0, 32).leading_zeros(), 32);
        assert_eq!(B129::new(0, 64).leading_zeros(), 64);
        assert_eq!(B129::new(0xFFFF_FFFF_FFFF_FFFF, 64).leading_zeros(), 0);
    }

    #[test]
    fn test_arith_shiftr() {
        assert_eq!(B129::new(0b100, 3).arith_shiftr(0), B129::new(0b100, 3));
        assert_eq!(B129::new(0b100, 3).arith_shiftr(1), B129::new(0b110, 3));
        assert_eq!(B129::new(0b100, 3).arith_shiftr(2), B129::new(0b111, 3));
        assert_eq!(B129::new(0b100, 3).arith_shiftr(3), B129::new(0b111, 3));
        assert_eq!(B129::new(0b100, 3).arith_shiftr(4), B129::new(0b111, 3));

        assert_eq!(B129::new(0b0110, 4).arith_shiftr(2), B129::new(0b0001, 4));

        for i in 0..131 {
            assert_eq!(ALL_ONES_129.arith_shiftr(i as i128), ALL_ONES_129);
            assert_eq!(ALL_ZEROS_129.arith_shiftr(i as i128), ALL_ZEROS_129);
        }
    }

    #[test]
    fn test_sign_extend() {
        assert_eq!(B129::new(0b1, 1).sign_extend(129), ALL_ONES_129);
        assert_eq!(B129::new(0b01, 2).sign_extend(129), ONE_129);

        assert_eq!(B129::new(0b1, 1).sign_extend(5), B129::new(0b11111, 5));
        assert_eq!(B129::new(0b01, 2).sign_extend(5), B129::new(0b00001, 5));
    }

    #[test]
    fn test_to_bytes() {
        assert_eq!(B129::new(0x123456,24).to_le_bytes(), [0x56, 0x34, 0x12]);
        assert_eq!(B129::new(0x123456,24).to_be_bytes(), [0x12, 0x34, 0x56]);
    }
}
