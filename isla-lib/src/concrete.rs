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

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use std::arch::x86_64::_bzhi_u64;
use std::convert::TryInto;
use std::fmt;
use std::hash::Hash;
use std::io::Write;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};

pub trait BV
where
    Self: Copy + Clone + fmt::Debug + fmt::Display + PartialEq + Eq + Hash + Send + Sync,
    Self: Serialize + DeserializeOwned,
    Self: Add<Output = Self>,
    Self: Sub<Output = Self>,
    Self: BitAnd<Output = Self>,
    Self: BitOr<Output = Self>,
    Self: BitXor<Output = Self>,
    Self: Not<Output = Self>,
    Self: Div<Output = Self>,
    Self: Mul<Output = Self>,
    Self: Neg<Output = Self>,
    Self: Rem<Output = Self>,
    Self: Shl<Output = Self>,
    Self: Shr<Output = Self>,
    Self: TryInto<u64, Error = ()>,
{
    const BIT_ONE: Self;
    const BIT_ZERO: Self;

    fn new(value: u64, len: u32) -> Self;
    fn bits(self) -> u64;

    fn zeros(len: u32) -> Self;

    fn ones(len: u32) -> Self;

    fn from_u8(value: u8) -> Self;

    fn from_u16(value: u16) -> Self;

    fn from_u32(value: u32) -> Self;

    fn from_u64(value: u64) -> Self;

    fn from_bytes(bytes: &[u8]) -> Self;

    fn len(self) -> u32;

    fn len_i128(self) -> i128 {
        i128::from(self.len())
    }

    fn is_empty(self) -> bool {
        self.len() == 0
    }

    fn zero_extend(self, new_length: u32) -> Self;

    fn sign_extend(self, new_length: u32) -> Self;

    fn unsigned(self) -> i128;

    fn signed(self) -> i128;

    fn append(self, suffix: Self) -> Option<Self>;

    fn slice(self, from: u32, length: u32) -> Option<Self>;

    fn set_slice(self, n: u32, update: Self) -> Self;

    fn extract(self, high: u32, low: u32) -> Option<Self>;

    fn shiftr(self, shift: i128) -> Self;

    fn shiftl(self, shift: i128) -> Self;

    fn truncate_lsb(self, length: i128) -> Option<Self>;

    fn replicate(self, times: i128) -> Option<Self>;

    fn set_slice_int(int: i128, n: u32, update: Self) -> i128;
}

#[inline(always)]
pub fn bzhi_u64(bits: u64, len: u32) -> u64 {
    unsafe { _bzhi_u64(bits, len) }
}

pub fn bzhi_u128(bits: u128, len: u32) -> u128 {
    bits & (std::u128::MAX >> (128 - len))
}

macro_rules! write_bits64 {
    ($f: expr, $bits: expr, $len: expr) => {{
        if $len == 4 {
            write!($f, "#x{:x}", $bits & 0xF)?
        } else if $len % 4 == 0 {
            write!($f, "#x")?;
            for i in (0..($len / 4)).rev() {
                write!($f, "{:x}", ($bits >> (i * 4)) & 0xF)?;
            }
        } else {
            write!($f, "#b")?;
            for i in (0..$len).rev() {
                write!($f, "{:b}", ($bits >> i) & 0b1)?;
            }
        }
        Ok(())
    }};
}

pub fn write_bits64(buf: &mut dyn Write, bits: u64, len: u32) -> std::io::Result<()> {
    write_bits64!(buf, bits, len)
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct B64 {
    pub length: u32,
    pub bits: u64,
}

impl fmt::Display for B64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_bits64!(f, self.bits, self.length)
    }
}

impl TryInto<u64> for B64 {
    type Error = ();

    fn try_into(self) -> Result<u64, ()> {
        Ok(self.bits)
    }
}

impl Not for B64 {
    type Output = B64;

    fn not(self) -> Self::Output {
        B64 { length: self.length, bits: bzhi_u64(!self.bits, self.length) }
    }
}

impl BitXor for B64 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        B64 { length: self.length, bits: self.bits ^ rhs.bits }
    }
}

impl BitOr for B64 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        B64 { length: self.length, bits: self.bits | rhs.bits }
    }
}

impl BitAnd for B64 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        B64 { length: self.length, bits: self.bits & rhs.bits }
    }
}

impl Neg for B64 {
    type Output = B64;

    fn neg(self) -> Self::Output {
        B64 { length: self.length, bits: bzhi_u64((-(self.bits as i64)) as u64, self.length) }
    }
}

impl Add<B64> for B64 {
    type Output = B64;

    fn add(self, rhs: Self) -> Self::Output {
        B64 { length: self.length, bits: bzhi_u64(self.bits + rhs.bits, self.length) }
    }
}

impl Sub<B64> for B64 {
    type Output = B64;

    fn sub(self, rhs: Self) -> Self::Output {
        B64 { length: self.length, bits: bzhi_u64(self.bits - rhs.bits, self.length) }
    }
}

impl Div<B64> for B64 {
    type Output = B64;

    fn div(self, rhs: Self) -> Self::Output {
        B64 { length: self.length, bits: bzhi_u64(self.bits / rhs.bits, self.length) }
    }
}

impl Rem<B64> for B64 {
    type Output = B64;

    fn rem(self, rhs: Self) -> Self::Output {
        B64 { length: self.length, bits: bzhi_u64(self.bits % rhs.bits, self.length) }
    }
}

impl Mul<B64> for B64 {
    type Output = B64;

    fn mul(self, rhs: Self) -> Self::Output {
        B64 { length: self.length, bits: bzhi_u64(self.bits * rhs.bits, self.length) }
    }
}

impl Shl<B64> for B64 {
    type Output = B64;

    fn shl(self, rhs: Self) -> Self::Output {
        if rhs.bits >= 64 {
            B64 { length: self.length, bits: 0 }
        } else {
            B64 { length: self.length, bits: bzhi_u64(self.bits << rhs.bits, self.length) }
        }
    }
}

impl Shr<B64> for B64 {
    type Output = B64;

    fn shr(self, rhs: Self) -> Self::Output {
        if rhs.bits >= 64 {
            B64 { length: self.length, bits: 0 }
        } else {
            B64 { length: self.length, bits: bzhi_u64(self.bits >> rhs.bits, self.length) }
        }
    }
}

impl BV for B64 {
    const BIT_ONE: Self = B64 { length: 1, bits: 1 };
    const BIT_ZERO: Self = B64 { length: 1, bits: 0 };

    fn new(bits: u64, length: u32) -> Self {
        assert!(length <= 64);
        B64 { length, bits }
    }

    fn bits(self) -> u64 {
        self.bits
    }

    fn zeros(length: u32) -> Self {
        assert!(length <= 64);
        B64 { length, bits: 0 }
    }

    fn ones(length: u32) -> Self {
        assert!(length <= 64);
        B64 { length, bits: bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, length) }
    }

    fn from_u8(value: u8) -> Self {
        B64 { length: 8, bits: value as u64 }
    }

    fn from_u16(value: u16) -> Self {
        B64 { length: 16, bits: value as u64 }
    }

    fn from_u32(value: u32) -> Self {
        B64 { length: 32, bits: value as u64 }
    }

    fn from_u64(value: u64) -> Self {
        B64 { length: 64, bits: value }
    }

    fn from_bytes(bytes: &[u8]) -> Self {
        assert!(bytes.len() <= 8);
        let mut bits: u64 = 0;
        for byte in bytes {
            bits = (bits << 8) | (*byte as u64)
        }
        B64 { length: bytes.len() as u32 * 8, bits }
    }

    fn len(self) -> u32 {
        self.length
    }

    fn zero_extend(self, new_length: u32) -> Self {
        assert!(self.length <= new_length && new_length <= 64);
        B64 { length: new_length, bits: self.bits }
    }

    fn sign_extend(self, new_length: u32) -> Self {
        assert!(self.length <= new_length && new_length <= 64);
        if self.length > 0 {
            if (self.bits >> (self.length - 1)) & 0b1 == 0b1 {
                let top = bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, new_length) & !bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, self.length);
                B64 { length: new_length, bits: self.bits | top }
            } else {
                B64 { length: new_length, bits: self.bits }
            }
        } else {
            B64 { length: 0, bits: 0 }
        }
    }

    fn unsigned(self) -> i128 {
        i128::from(self.bits)
    }

    fn signed(self) -> i128 {
        i128::from(self.sign_extend(64).bits as i64)
    }

    fn append(self, suffix: Self) -> Option<Self> {
        let new_length = self.length + suffix.length;
        if new_length <= 64 {
            if suffix.length == 64 {
                Some(suffix)
            } else {
                Some(B64 { length: new_length, bits: (self.bits << suffix.length | suffix.bits) })
            }
        } else {
            None
        }
    }

    fn slice(self, from: u32, length: u32) -> Option<Self> {
        if from + length <= self.length {
            Some(B64 { length, bits: bzhi_u64(self.bits >> from, length) })
        } else {
            None
        }
    }

    fn set_slice(self, n: u32, update: Self) -> Self {
        let mask = !bzhi_u64(0xFFFF_FFFF_FFFF_FFFF << n, n + update.length);
        let update = update.bits << n;
        B64 { length: self.length, bits: (self.bits & mask) | update }
    }

    fn extract(self, high: u32, low: u32) -> Option<Self> {
        let length = (high - low) + 1;
        if low <= high && high <= self.length {
            Some(B64 { length, bits: bzhi_u64(self.bits >> low, length) })
        } else {
            None
        }
    }

    fn shiftr(self, shift: i128) -> Self {
        if shift < 0 {
            self.shiftl(shift.abs())
        } else if shift >= 64 {
            B64 { length: self.length, bits: 0 }
        } else {
            B64 { length: self.length, bits: bzhi_u64(self.bits >> (shift as u64), self.length) }
        }
    }

    fn shiftl(self, shift: i128) -> Self {
        if shift < 0 {
            self.shiftr(shift.abs())
        } else if shift >= 64 {
            B64 { length: self.length, bits: 0 }
        } else {
            B64 { length: self.length, bits: bzhi_u64(self.bits << (shift as u64), self.length) }
        }
    }

    fn truncate_lsb(self, length: i128) -> Option<Self> {
        if 0 < length && length <= 64 {
            let length = length as u32;
            Some(B64 { length, bits: bzhi_u64(self.bits >> (64 - length), length) })
        } else if length == 0 {
            Some(B64::new(0, 0))
        } else {
            None
        }
    }

    fn replicate(self, times: i128) -> Option<Self> {
        if times == 0 {
            Some(B64::new(0, 0))
        } else if 0 <= times && self.length as i128 * times <= 64 {
            let mut bits = self.bits;
            for _ in 1..times {
                bits |= bits << self.length
            }
            Some(B64 { length: self.length * times as u32, bits })
        } else {
            None
        }
    }

    fn set_slice_int(int: i128, n: u32, update: Self) -> i128 {
        let mask = !bzhi_u128(u128::max_value() << n, n as u32 + update.len());
        let update = (update.bits as u128) << n;
        ((int as u128 & mask) | update) as i128
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
    }

    #[test]
    fn test_mul() {
        assert!(B64::new(0b111, 3) * B64::new(0b111, 3) == B64::new(0b001, 3));
        assert!(B64::new(0b0100, 4) * B64::new(0b0001, 4) == B64::new(0b0100, 4));
    }

    #[test]
    fn test_neg() {
        assert!(-B64::new(0b000, 3) == B64::new(0b000, 3));
        assert!(-B64::new(0b001, 3) == B64::new(0b111, 3));
        assert!(-B64::new(0b010, 3) == B64::new(0b110, 3));
    }

    #[test]
    fn test_shl() {
        assert!(B64::new(0b001, 3) << B64::new(2, 3) == B64::new(0b100, 3));
        assert!(B64::new(0b001, 3) << B64::new(3, 3) == B64::new(0b000, 3));
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
    fn test_set_slice_int() {
        assert!(B64::set_slice_int(15, 1, B64::new(0, 2)) == 9)
    }
}
