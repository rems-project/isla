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

use std::ops::AddAssign;

use num_bigint::BigUint;
use num_traits::identities::{One, Zero};

#[derive(Clone, Debug)]
pub struct Fraction {
    num: BigUint,
    denom_pow: u64,
}

impl Fraction {
    pub fn zero() -> Self {
        Fraction { num: BigUint::zero(), denom_pow: 0 }
    }

    pub fn one() -> Self {
        Fraction { num: BigUint::one(), denom_pow: 0 }
    }

    pub fn halve(&mut self) {
        self.denom_pow += 1
    }

    fn divide_pow(&mut self, pow: u64) {
        self.num *= BigUint::from(1u64 << pow);
        self.denom_pow += pow;
    }

    /// `frac.min_split(N)` splits a fraction into two parts with the
    /// argument being `1 / 2 ^ N` of the original, and the returned
    /// value containing the rest. For example:
    ///
    /// ```text
    /// let mut f = Fraction::one();
    /// let rest = f.min_split(6);
    /// // f == 1/64
    /// // rest == 63/64
    /// ```
    pub fn min_split(&mut self, pow: u64) -> Self {
        if self.num.is_one() {
            self.divide_pow(pow);
        }
        let split = Fraction { num: self.num.clone() - BigUint::one(), denom_pow: self.denom_pow };
        self.num.set_one();
        split
    }

    pub fn is_one(&self) -> bool {
        self.num == BigUint::one() << self.denom_pow
    }
}

impl AddAssign for Fraction {
    fn add_assign(&mut self, mut rhs: Self) {
        if self.denom_pow < rhs.denom_pow {
            self.num *= BigUint::one() << (rhs.denom_pow - self.denom_pow);
            self.denom_pow = rhs.denom_pow
        } else if self.denom_pow > rhs.denom_pow {
            rhs.num *= BigUint::one() << (self.denom_pow - rhs.denom_pow);
            rhs.denom_pow = self.denom_pow;
        }
        self.num += rhs.num
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fraction_halve() {
        let mut fracs = Vec::new();
        let mut f = Fraction::one();
        for _ in 0..1024 {
            f.halve();
            fracs.push(f.clone());
        }
        let mut total = Fraction::zero();
        for part in fracs {
            total += part
        }
        total += f;
        assert!(total.is_one())
    }
}
