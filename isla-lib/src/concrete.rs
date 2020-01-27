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

use std::arch::x86_64::_bzhi_u64;
use std::fmt;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};

#[inline(always)]
pub fn bzhi_u64(bits: u64, len: u32) -> u64 {
    unsafe { _bzhi_u64(bits, len) }
}

pub fn bzhi_u128(bits: u128, len: u32) -> u128 {
    bits & ((1 << len) - 1)
}

#[allow(clippy::needless_range_loop)]
pub fn write_bits64(f: &mut fmt::Formatter<'_>, bits: u64, len: u32) -> fmt::Result {
    if len == 4 {
        write!(f, "#x{:x}", bits & 0xF)?
    } else if len % 4 == 0 {
        write!(f, "#x")?;
        let bytes = bits.to_be_bytes();
        for i in (8 - len as usize / 8)..8 {
            write!(f, "{:x}", bytes[i] >> 4)?;
            write!(f, "{:x}", bytes[i] & 0xF)?;
        }
    } else {
        write!(f, "#b")?;
        for i in (0..len).rev() {
            write!(f, "{:b}", (bits >> i) & 0b1)?;
        }
    }
    Ok(())
}

#[derive(Copy, Clone, Debug)]
pub struct Sbits {
    pub length: u32,
    pub bits: u64,
}

impl Sbits {
    pub fn new(bits: u64, length: u32) -> Self {
        assert!(length <= 64);
        Sbits { length, bits }
    }

    pub fn zeros(length: u32) -> Self {
        assert!(length <= 64);
        Sbits { length, bits: 0 }
    }

    pub fn ones(length: u32) -> Self {
        assert!(length <= 64);
        Sbits { length, bits: bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, length) }
    }

    pub const BIT_ONE: Self = Sbits { length: 1, bits: 1 };
    pub const BIT_ZERO: Self = Sbits { length: 1, bits: 0 };

    pub fn from_u8(value: u8) -> Self {
        Sbits { length: 8, bits: value as u64 }
    }

    pub fn from_u32(value: u32) -> Self {
        Sbits { length: 32, bits: value as u64 }
    }

    pub fn from_bytes(bytes: &[u8]) -> Self {
        assert!(bytes.len() <= 8);
        let mut bits: u64 = 0;
        for byte in bytes {
            bits = (bits << 8) | (*byte as u64)
        }
        Sbits { length: bytes.len() as u32 * 8, bits }
    }

    pub fn len_i128(self) -> i128 {
        i128::from(self.length)
    }

    pub fn zero_extend(self, new_length: u32) -> Self {
        assert!(self.length <= new_length && new_length <= 64);
        Sbits { length: new_length, bits: self.bits }
    }

    pub fn sign_extend(self, new_length: u32) -> Self {
        assert!(self.length <= new_length && new_length <= 64);
        if self.length > 0 {
            if (self.bits >> (self.length - 1)) & 0b1 == 0b1 {
                let top = bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, new_length) & !bzhi_u64(0xFFFF_FFFF_FFFF_FFFF, self.length);
                Sbits { length: new_length, bits: self.bits | top }
            } else {
                Sbits { length: new_length, bits: self.bits }
            }
        } else {
            Sbits { length: 0, bits: 0 }
        }
    }

    pub fn unsigned(self) -> i128 {
        i128::from(self.bits)
    }

    pub fn signed(self) -> i128 {
        i128::from(self.sign_extend(64).bits as i64)
    }

    pub fn append(self, suffix: Self) -> Option<Self> {
        let new_length = self.length + suffix.length;
        if new_length <= 64 {
            if suffix.length == 64 {
                Some(suffix)
            } else {
                Some(Sbits { length: new_length, bits: (self.bits << suffix.length | suffix.bits) })
            }
        } else {
            None
        }
    }

    pub fn slice(self, from: u32, length: u32) -> Option<Self> {
        if from + length <= self.length {
            Some(Sbits { length, bits: bzhi_u64(self.bits >> from, length) })
        } else {
            None
        }
    }

    pub fn set_slice(self, n: u32, update: Self) -> Self {
        let mask = !bzhi_u64(0xFFFF_FFFF_FFFF_FFFF << n, n + update.length);
        let update = update.bits << n;
        Sbits { length: self.length, bits: (self.bits & mask) | update }
    }

    pub fn extract(self, high: u32, low: u32) -> Option<Self> {
        let length = (high - low) + 1;
        if low <= high && high <= self.length {
            Some(Sbits { length, bits: bzhi_u64(self.bits >> low, length) })
        } else {
            None
        }
    }

    pub fn shiftr(self, shift: i128) -> Self {
        if shift < 0 {
            self.shiftl(shift.abs())
        } else if shift >= 64 {
            Sbits { length: self.length, bits: 0 }
        } else {
            Sbits { length: self.length, bits: bzhi_u64(self.bits >> (shift as u64), self.length) }
        }
    }

    pub fn shiftl(self, shift: i128) -> Self {
        if shift < 0 {
            self.shiftr(shift.abs())
        } else if shift >= 64 {
            Sbits { length: self.length, bits: 0 }
        } else {
            Sbits { length: self.length, bits: bzhi_u64(self.bits << (shift as u64), self.length) }
        }
    }

    pub fn truncate_lsb(self, length: i128) -> Option<Self> {
        if 0 < length && length <= 64 {
            let length = length as u32;
            Some(Sbits { length, bits: bzhi_u64(self.bits >> (64 - length), length) })
        } else if length == 0 {
            Some(Sbits::new(0, 0))
        } else {
            None
        }
    }

    pub fn replicate(self, times: i128) -> Option<Self> {
        if times == 0 {
            Some(Sbits::new(0, 0))
        } else if 0 <= times && self.length as i128 * times <= 64 {
            let mut bits = self.bits;
            for _ in 1..times {
                bits |= bits << self.length
            }
            Some(Sbits { length: self.length * times as u32, bits })
        } else {
            None
        }
    }
}

impl PartialEq for Sbits {
    fn eq(&self, rhs: &Self) -> bool {
        self.bits == rhs.bits
    }
}
impl Eq for Sbits {}

impl Not for Sbits {
    type Output = Sbits;

    fn not(self) -> Self::Output {
        Sbits { length: self.length, bits: bzhi_u64(!self.bits, self.length) }
    }
}

impl BitXor for Sbits {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Sbits { length: self.length, bits: self.bits ^ rhs.bits }
    }
}

impl BitOr for Sbits {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Sbits { length: self.length, bits: self.bits | rhs.bits }
    }
}

impl BitAnd for Sbits {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Sbits { length: self.length, bits: self.bits & rhs.bits }
    }
}

impl Neg for Sbits {
    type Output = Sbits;

    fn neg(self) -> Self::Output {
        Sbits { length: self.length, bits: bzhi_u64((-(self.bits as i64)) as u64, self.length) }
    }
}

impl Add<Sbits> for Sbits {
    type Output = Sbits;

    fn add(self, rhs: Self) -> Self::Output {
        Sbits { length: self.length, bits: bzhi_u64(self.bits + rhs.bits, self.length) }
    }
}

impl Sub<Sbits> for Sbits {
    type Output = Sbits;

    fn sub(self, rhs: Self) -> Self::Output {
        Sbits { length: self.length, bits: bzhi_u64(self.bits - rhs.bits, self.length) }
    }
}

impl Div<Sbits> for Sbits {
    type Output = Sbits;

    fn div(self, rhs: Self) -> Self::Output {
        Sbits { length: self.length, bits: bzhi_u64(self.bits / rhs.bits, self.length) }
    }
}

impl Rem<Sbits> for Sbits {
    type Output = Sbits;

    fn rem(self, rhs: Self) -> Self::Output {
        Sbits { length: self.length, bits: bzhi_u64(self.bits % rhs.bits, self.length) }
    }
}

impl Mul<Sbits> for Sbits {
    type Output = Sbits;

    fn mul(self, rhs: Self) -> Self::Output {
        Sbits { length: self.length, bits: bzhi_u64(self.bits * rhs.bits, self.length) }
    }
}

impl Shl<Sbits> for Sbits {
    type Output = Sbits;

    fn shl(self, rhs: Self) -> Self::Output {
        if rhs.bits >= 64 {
            Sbits { length: self.length, bits: 0 }
        } else {
            Sbits { length: self.length, bits: bzhi_u64(self.bits << rhs.bits, self.length) }
        }
    }
}

impl Shr<Sbits> for Sbits {
    type Output = Sbits;

    fn shr(self, rhs: Self) -> Self::Output {
        if rhs.bits >= 64 {
            Sbits { length: self.length, bits: 0 }
        } else {
            Sbits { length: self.length, bits: bzhi_u64(self.bits >> rhs.bits, self.length) }
        }
    }
}

impl fmt::Display for Sbits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_bits64(f, self.bits, self.length)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mul() {
        assert!(Sbits::new(0b111, 3) * Sbits::new(0b111, 3) == Sbits::new(0b001, 3));
        assert!(Sbits::new(0b0100, 4) * Sbits::new(0b0001, 4) == Sbits::new(0b0100, 4));
    }

    #[test]
    fn test_neg() {
        assert!(-Sbits::new(0b000, 3) == Sbits::new(0b000, 3));
        assert!(-Sbits::new(0b001, 3) == Sbits::new(0b111, 3));
        assert!(-Sbits::new(0b010, 3) == Sbits::new(0b110, 3));
    }

    #[test]
    fn test_shl() {
        assert!(Sbits::new(0b001, 3) << Sbits::new(2, 3) == Sbits::new(0b100, 3));
        assert!(Sbits::new(0b001, 3) << Sbits::new(3, 3) == Sbits::new(0b000, 3));
        assert!(Sbits::new(0xFFFF_FFFF_FFFF_FFFF, 64) << Sbits::new(64, 64) == Sbits::new(0, 64));
        assert!(Sbits::new(0xFFFF_FFFF_FFFF_FFFF, 64) << Sbits::new(66, 64) == Sbits::new(0, 64));
    }

    #[test]
    fn test_shr() {
        assert!(Sbits::new(0b100, 3) >> Sbits::new(2, 3) == Sbits::new(0b001, 3));
        assert!(Sbits::new(0b100, 3) >> Sbits::new(3, 3) == Sbits::new(0b000, 3));
        assert!(Sbits::new(0xFFFF_FFFF_FFFF_FFFF, 64) >> Sbits::new(64, 64) == Sbits::new(0, 64));
        assert!(Sbits::new(0xFFFF_FFFF_FFFF_FFFF, 64) >> Sbits::new(66, 64) == Sbits::new(0, 64));
    }

    #[test]
    fn test_zero_extend() {
        assert!(Sbits::new(0b100, 3).zero_extend(3) == Sbits::new(0b100, 3));
        assert!(Sbits::new(0b100, 3).zero_extend(6) == Sbits::new(0b000100, 6));
    }

    #[test]
    fn test_sign_extend() {
        assert!(Sbits::new(0b100, 3).sign_extend(6) == Sbits::new(0b111100, 6));
        assert!(Sbits::new(0b010, 3).sign_extend(6) == Sbits::new(0b000010, 6));
        assert!(Sbits::new(0b110, 3).sign_extend(3) == Sbits::new(0b110, 3));
        assert!(Sbits::new(0b010, 3).sign_extend(3) == Sbits::new(0b010, 3));
        assert!(Sbits::new(0xF, 4).sign_extend(8) == Sbits::new(0xFF, 8));
    }

    #[test]
    fn test_append() {
        let sbits_max = Sbits::new(0xFFFF_FFFF_FFFF_FFFF, 64);
        assert!(Sbits::new(0, 0).append(sbits_max) == Some(sbits_max));
        assert!(sbits_max.append(Sbits::new(0, 0)) == Some(sbits_max));
        assert!(sbits_max.append(sbits_max) == None);
        assert!(
            Sbits::new(0xCAFECAFE, 32).append(Sbits::new(0x1234ABCD, 32)) == Some(Sbits::new(0xCAFECAFE1234ABCD, 64))
        );
    }

    #[test]
    fn test_slice() {
        let sbits = Sbits::new(0xCAFE_F00D_1234_ABCD, 64);
        assert!(sbits.slice(0, 32) == Some(Sbits::new(0x1234_ABCD, 32)));
        assert!(sbits.slice(32, 32) == Some(Sbits::new(0xCAFE_F00D, 32)));
        assert!(sbits.slice(16, 16) == Some(Sbits::new(0x1234, 16)));
    }

    #[test]
    fn test_extract() {
        let sbits = Sbits::new(0xCAFE_F00D_1234_ABCD, 64);
        assert!(sbits.extract(31, 0) == Some(Sbits::new(0x1234_ABCD, 32)));
        assert!(sbits.extract(63, 32) == Some(Sbits::new(0xCAFE_F00D, 32)));
        assert!(sbits.extract(7, 0) == Some(Sbits::new(0xCD, 8)));
    }

    #[test]
    fn test_truncate_lsb() {
        let sbits = Sbits::new(0xCAFE_F00D_1234_ABCD, 64);
        assert!(sbits.truncate_lsb(16) == Some(Sbits::new(0xCAFE, 16)));
        assert!(sbits.truncate_lsb(64) == Some(sbits));
        assert!(sbits.truncate_lsb(0) == Some(Sbits::new(0, 0)));
    }

    #[test]
    fn test_signed() {
        assert!(Sbits::new(0b100, 3).signed() == -4);
        assert!(Sbits::new(0b011, 3).signed() == 3);
        assert!(Sbits::new(0b111, 3).signed() == -1);
        assert!(Sbits::new(0b000, 3).signed() == 0);
        assert!(Sbits::new(0b1, 1).signed() == -1);
    }

    #[test]
    fn test_unsigned() {
        assert!(Sbits::new(0b100, 3).unsigned() == 4);
        assert!(Sbits::new(0b011, 3).unsigned() == 3);
        assert!(Sbits::new(0b111, 3).unsigned() == 7);
        assert!(Sbits::new(0b000, 3).unsigned() == 0);
        assert!(Sbits::new(0b1, 1).unsigned() == 1);
    }

    #[test]
    fn test_replicate() {
        assert!(Sbits::new(0b101, 3).replicate(0) == Some(Sbits::new(0, 0)));
        assert!(Sbits::new(0b10, 2).replicate(3) == Some(Sbits::new(0b101010, 6)));
        assert!(Sbits::new(0xCAFE, 16).replicate(4) == Some(Sbits::new(0xCAFECAFECAFECAFE, 64)));
        assert!(Sbits::new(0b1, 1).replicate(128) == None);
    }

    #[test]
    fn test_set_slice() {
        assert!(Sbits::new(0b000, 3).set_slice(1, Sbits::new(0b1, 1)) == Sbits::new(0b010, 3));
        assert!(Sbits::new(0b111, 3).set_slice(1, Sbits::new(0b0, 1)) == Sbits::new(0b101, 3));
        assert!(Sbits::new(0b111, 3).set_slice(1, Sbits::new(0b1, 1)) == Sbits::new(0b111, 3));
        assert!(Sbits::new(0b000, 3).set_slice(1, Sbits::new(0b0, 1)) == Sbits::new(0b000, 3));
        assert!(Sbits::new(0xCAFE, 16).set_slice(4, Sbits::new(0x0, 4)) == Sbits::new(0xCA0E, 16));
        assert!(Sbits::new(0xFFFF, 16).set_slice(12, Sbits::new(0x0, 4)) == Sbits::new(0x0FFF, 16));
        assert!(Sbits::new(0xFFFF, 16).set_slice(8, Sbits::new(0x0, 4)) == Sbits::new(0xF0FF, 16));
        assert!(Sbits::new(0xFFFF, 16).set_slice(4, Sbits::new(0x0, 4)) == Sbits::new(0xFF0F, 16));
        assert!(Sbits::new(0xFFFF, 16).set_slice(0, Sbits::new(0x0, 4)) == Sbits::new(0xFFF0, 16));
    }
}
