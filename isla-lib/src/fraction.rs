// BSD 2-Clause License
//
// Copyright (c) 2024 Alasdair Armstrong
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

use std::ops::Add;

#[derive(Copy, Clone, Debug)]
pub struct Fraction {
    num: u32,
    denom_pow: u32,
}

impl Fraction {
    pub fn one() -> Self {
        Fraction { num: 1, denom_pow: 0 }
    }

    pub fn halve(self) -> Self {
        Fraction { num: self.num, denom_pow: self.denom_pow + 1 }
    }

    pub fn is_one(self) -> bool {
        self.num == 1 << self.denom_pow
    }
}

impl Add for Fraction {
    type Output = Self;

    fn add(mut self, mut other: Self) -> Self {
        if self.denom_pow < other.denom_pow {
            self.num = self.num * (1 << (other.denom_pow - self.denom_pow));
            self.denom_pow = other.denom_pow;
        } else if self.denom_pow > other.denom_pow {
            other.num = other.num * (1 << (self.denom_pow - other.denom_pow));
            other.denom_pow = self.denom_pow
        };
        Fraction { num: self.num + other.num, denom_pow: self.denom_pow }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fractions() {
        let f = Fraction::one();
        assert!(Fraction::is_one(f));

        let x = f.halve();
        let y = x.halve();
        assert!(!Fraction::is_one(x));
        assert!(!Fraction::is_one(y));

        assert!(Fraction::is_one(x + x));
        assert!(Fraction::is_one(x + y + y));
        assert!(Fraction::is_one(y + y + y + y));
    }
}
