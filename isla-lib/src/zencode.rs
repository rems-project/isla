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

//! This module implements the name mangling scheme used by Sail
//!
//! It allows all ASCII strings to be represented using just the
//! characters allowed in C identifers. The way it works is all
//! characters that are not allowed in C identifiers are encoded as
//! `zX` where `X` is some C allowed character. The letter `z` is
//! encoded as `zz`. Additionally a 'z' prefix is placed at the start
//! of the string. This prefix allows us to undo multiple rounds of
//! encoding, which can happen when Sail does multiple rounds of
//! monomorphisation. This works as we can decode until either the
//! string has no `z` prefix or `zz`, in which case we can do one more
//! decode step and the first letter of the original string was `z`.
//!
//! We could adapt this to support unicode by having something like
//! `zu<codepoint>` for each unicode character, but as Sail does not
//! allow unicode identifiers this is not supported at the moment.
//!
//! The inspiration for this name-mangling scheme is GHC, see:
//! <https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/symbol-names>

use std::string::FromUtf8Error;

pub fn encode(input: &str) -> String {
    let mut output = Vec::with_capacity(input.len() + 1);
    output.push(0x7a);
    for c in input[0..].bytes() {
        if c <= 41 {
            output.push(0x7a);
            output.push(c + 16);
        } else if c <= 47 {
            output.push(0x7a);
            output.push(c + 23);
        } else if c > 57 && c <= 64 {
            output.push(0x7a);
            output.push(c + 13);
        } else if (c > 90 && c <= 94) || c == 96 {
            output.push(0x7a);
            output.push(c - 13);
        } else if c == 0x7a {
            output.push(0x7a);
            output.push(0x7a);
        } else if c > 122 && c <= 126 {
            output.push(0x7a);
            output.push(c - 39);
        } else {
            output.push(c);
        }
    }
    String::from_utf8(output).unwrap()
}

pub fn try_decode(input: &str) -> Result<String, FromUtf8Error> {
    let mut output = Vec::with_capacity(input.len() - 1);
    let mut next_encoded = false;
    for c in input[1..].bytes() {
        if next_encoded {
            output.push(if c <= 57 {
                c - 16
            } else if c <= 70 {
                c - 23
            } else if c <= 77 {
                c - 13
            } else if c <= 83 {
                c + 13
            } else if c == 122 {
                122
            } else {
                c + 39
            });
            next_encoded = false
        } else if c == 0x7a {
            next_encoded = true
        } else {
            output.push(c)
        }
    }
    String::from_utf8(output)
}

pub fn decode(input: &str) -> String {
    try_decode(input).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zdecode() {
        assert!(decode("zz0") == " ".to_string());
        assert!(decode("zz1") == "!".to_string());
        assert!(decode("zz8") == "(".to_string());
        assert!(decode("zz9") == ")".to_string());
        assert!(decode("zzA") == "*".to_string());
        assert!(decode("zzB") == "+".to_string());
        assert!(decode("zzE") == ".".to_string());
        assert!(decode("zzF") == "/".to_string());
        assert!(decode("zzG") == ":".to_string());
        assert!(decode("zzL") == "?".to_string());
        assert!(decode("zzM") == "@".to_string());
        assert!(decode("zzN") == "[".to_string());
        assert!(decode("zzO") == "\\".to_string());
        assert!(decode("zzR") == "_".to_string());
        assert!(decode("zzS") == "`".to_string());
        assert!(decode("zzT") == "{".to_string());
        assert!(decode("zzW") == "~".to_string());
        assert!(decode("zzz") == "z".to_string());
        assert!(decode("z_") == "_".to_string());
        assert!(decode("za") == "a".to_string());
        assert!(decode("zA") == "A".to_string());
        assert!(decode("zZ") == "Z".to_string());
        assert!(decode("z1") == "1".to_string());
        assert!(decode("z9") == "9".to_string());
        assert!(decode("zy") == "y".to_string());
        assert!(decode("zz5i64zDzKz5i") == "%i64->%i".to_string());
    }

    #[test]
    fn zencode() {
        assert!("zz0".to_string() == encode(" "));
        assert!("zz1".to_string() == encode("!"));
        assert!("zz8".to_string() == encode("("));
        assert!("zz9".to_string() == encode(")"));
        assert!("zzA".to_string() == encode("*"));
        assert!("zzB".to_string() == encode("+"));
        assert!("zzE".to_string() == encode("."));
        assert!("zzF".to_string() == encode("/"));
        assert!("zzG".to_string() == encode(":"));
        assert!("zzL".to_string() == encode("?"));
        assert!("zzM".to_string() == encode("@"));
        assert!("zzN".to_string() == encode("["));
        assert!("zzO".to_string() == encode("\\"));
        assert!("zzS".to_string() == encode("`"));
        assert!("zzT".to_string() == encode("{"));
        assert!("zzW".to_string() == encode("~"));
        assert!("zzz".to_string() == encode("z"));
        assert!("z_".to_string() == encode("_"));
        assert!("za".to_string() == encode("a"));
        assert!("zA".to_string() == encode("A"));
        assert!("zZ".to_string() == encode("Z"));
        assert!("z1".to_string() == encode("1"));
        assert!("z9".to_string() == encode("9"));
        assert!("zz5i64zDzKz5i".to_string() == encode("%i64->%i"));
    }
}
