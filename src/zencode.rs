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
            });
            next_encoded = false
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
