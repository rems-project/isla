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
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Sub};

#[derive(Copy, Clone)]
pub struct Sbits {
    length: u32,
    bits: u64,
}

impl Sbits {
    pub fn bv(bits: u64, length: u32) -> Self {
        Sbits { length, bits }
    }

    fn from_u64(bits: u64) -> Self {
        Sbits { length: 64, bits }
    }

    fn from_u32(bits: u32) -> Self {
        Sbits { length: 32, bits: u64::from(bits) }
    }

    fn from_u16(bits: u16) -> Self {
        Sbits { length: 16, bits: u64::from(bits) }
    }

    fn from_u8(bits: u8) -> Self {
        Sbits { length: 8, bits: u64::from(bits) }
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
        unsafe { Sbits { length: self.length, bits: _bzhi_u64(!self.bits, self.length) } }
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
        unsafe { Sbits { length: self.length, bits: _bzhi_u64((-(self.bits as i64)) as u64, self.length) } }
    }
}

impl Add<Sbits> for Sbits {
    type Output = Sbits;

    fn add(self, rhs: Self) -> Self::Output {
        unsafe { Sbits { length: self.length, bits: _bzhi_u64(self.bits + rhs.bits, self.length) } }
    }
}

impl Sub<Sbits> for Sbits {
    type Output = Sbits;

    fn sub(self, rhs: Self) -> Self::Output {
        unsafe { Sbits { length: self.length, bits: _bzhi_u64(self.bits - rhs.bits, self.length) } }
    }
}

impl Div<Sbits> for Sbits {
    type Output = Sbits;

    fn div(self, rhs: Self) -> Self::Output {
        unsafe { Sbits { length: self.length, bits: _bzhi_u64(self.bits / rhs.bits, self.length) } }
    }
}

impl Rem<Sbits> for Sbits {
    type Output = Sbits;

    fn rem(self, rhs: Self) -> Self::Output {
        unsafe { Sbits { length: self.length, bits: _bzhi_u64(self.bits % rhs.bits, self.length) } }
    }
}

impl Mul<Sbits> for Sbits {
    type Output = Sbits;

    fn mul(self, rhs: Self) -> Self::Output {
        unsafe { Sbits { length: self.length, bits: _bzhi_u64(self.bits * rhs.bits, self.length) } }
    }
}

impl fmt::Display for Sbits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(_ bv{} {})", self.bits, self.length)
    }
}

#[derive(Clone)]
pub enum CVal {
    Sbits(Sbits),
    Int(i128),
    Bool(bool),
}

impl fmt::Display for CVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CVal::Sbits(bv) => Sbits::fmt(bv, f),
            CVal::Bool(b) => bool::fmt(b, f),
            CVal::Int(i) => write!(f, "(_ bv{} 128)", *i as u128),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mul() {
        assert!(Sbits::bv(0b111, 3) * Sbits::bv(0b111, 3) == Sbits::bv(0b001, 3));
        assert!(Sbits::bv(0b0100, 4) * Sbits::bv(0b0001, 4) == Sbits::bv(0b0100, 4));
    }

    #[test]
    fn test_neg() {
        assert!(-Sbits::bv(0b000, 3) == Sbits::bv(0b000, 3));
        assert!(-Sbits::bv(0b001, 3) == Sbits::bv(0b111, 3));
        assert!(-Sbits::bv(0b010, 3) == Sbits::bv(0b110, 3));
    }
}
