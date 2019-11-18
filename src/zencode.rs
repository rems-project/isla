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

pub fn decode(input: &str) -> String {
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
            })
        } else if c == 0x7a {
            next_encoded = true
        } else {
            output.push(c)
        }
    }
    String::from_utf8(output).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zdecode_edges() {
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
    }
}
