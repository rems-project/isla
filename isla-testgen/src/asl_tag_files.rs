// BSD 2-Clause License
//
// Copyright (c) 2020 Brian Campbell
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

use regex::Regex;
use regex::RegexSet;

use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::str::FromStr;

#[derive(Clone, Copy)]
pub enum Encoding {
    A64,
    A32,
    T32,
    T16,
}

impl FromStr for Encoding {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use Encoding::*;
        Ok(match s {
            "A64" => A64,
            "A32" => A32,
            "T32" => T32,
            "T16" => T16,
            _ => return Err(format!("Bad encoding: {}", s)),
        })
    }
}
impl fmt::Display for Encoding {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Encoding::*;
        write!(
            f,
            "{}",
            match self {
                A64 => "A64",
                A32 => "A32",
                T32 => "T32",
                T16 => "T16",
            }
        )
    }
}

struct Field {
    high: u32,
    low: u32,
    name: String,
    pattern: String,
}


impl FromStr for Field {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref PATTERN : Regex = Regex::new(r"^[01x!()]+$").unwrap();
        }

        let components: Vec<&str> = s.splitn(3, ' ').collect();
        if components.len() < 2 || components.len() > 3 {
            return Err(format!("Bad field specifier line: {}", s));
        }
        let range: Vec<&str> = components[0].splitn(2, ':').collect();
        if range.len() < 1 || range.len() > 2 {
            return Err(format!("Bad range: {}", components[0]));
        }
        let high = range[0].parse().map_err(|_| "Bad range")?;
        let low = range[range.len() - 1].parse().map_err(|_| "Bad range")?;
        let name = components[1].to_string();
        let pattern = if components.len() == 3 {
            components[2].to_string()
        } else {
            if PATTERN.is_match(components[1]) {
                components[1].to_string()
            } else {
                "x".repeat((high-low+1) as usize)
            }
        };
        Ok(Field { high, low, name, pattern })
    }
}

impl Field {
    fn random(&self) -> (u32, String) {
        let mut bits: u32 = 0;
        let mut string_bits = format!("{}:", self.name);
        let mut chars = self.pattern.chars();
        for i in (self.low..self.high + 1).rev() {
            loop {
                match chars.next() {
                    Some('(') => continue,
                    Some(')') => continue,
                    Some('0') => {
                        string_bits.push('0');
                        break;
                    }
                    Some('1') => {
                        bits = bits | (1 << i);
                        string_bits.push('1');
                        break;
                    }
                    Some('x') => {
                        if rand::random() {
                            bits = bits | (1 << i);
                            string_bits.push('1');
                        } else {
                            string_bits.push('0');
                        }
                        break;
                    }
                    _ => panic!("Bad pattern {}", self.pattern),
                }
            }
        }
        (bits, string_bits)
    }
}

struct Diagram {
    name: String,
    patterns: Vec<Field>,
}

impl fmt::Display for Diagram {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;
        for pattern in self.patterns.iter() {
            write!(f, " {}:{}", pattern.name, pattern.pattern)?;
        }
        Ok(())
    }
}

impl Diagram {
    fn random(&self) -> (u32, String) {
        let mut bits: u32 = 0;
        let mut description = self.name.clone();
        for field in self.patterns.iter() {
            let (new_bits, new_string) = field.random();
            bits |= new_bits;
            description.push(' ');
            description.push_str(&new_string);
        }
        (bits, description)
    }
}

#[derive(Default)]
pub struct Encodings {
    a64: Vec<Diagram>,
    a32: Vec<Diagram>,
    t32: Vec<Diagram>,
    t16: Vec<Diagram>,
}

impl Encodings {
    fn get(&self, encoding: Encoding) -> &Vec<Diagram> {
        use Encoding::*;
        match encoding {
            A64 => &self.a64,
            A32 => &self.a32,
            T32 => &self.t32,
            T16 => &self.t16,
        }
    }

    fn get_mut(&mut self, encoding: Encoding) -> &mut Vec<Diagram> {
        use Encoding::*;
        match encoding {
            A64 => &mut self.a64,
            A32 => &mut self.a32,
            T32 => &mut self.t32,
            T16 => &mut self.t16,
        }
    }

    pub fn random(&self, encoding: Encoding) -> (u32, String) {
        use rand::Rng;
        let diagrams = self.get(encoding);
        if diagrams.len() == 0 {
            panic!("No diagrams for encoding {}", encoding);
        }
        let mut rng = rand::thread_rng();
        let i = rng.gen_range(0, diagrams.len());
        diagrams[i].random()
    }
}

fn read_diagram(name: &str, lines: &mut dyn Iterator<Item = String>, encodings: &mut Encodings) -> Result<(), String> {
    let encoding = lines.next().expect("End of file when encoding expected").parse::<Encoding>()?;

    let mut bits_found: u32 = 0;
    let mut patterns = Vec::new();

    while bits_found < 32 {
        match lines.next() {
            Some(line) => {
                let field = line.parse::<Field>()?;
                bits_found += field.high - field.low + 1;
                patterns.push(field);
            }
            None => return Err(format!("End of file during diagram for {}", name))
        }
    }
    if bits_found > 32 {
        return Err(format!("Too many bits in diagram for {}", name));
    }
    patterns.sort_by_key(|f| f.low);
    let mut high = 0;
    for field in &patterns {
        if field.low != high {
            return Err(format!("Missing bit {} in diagram for {}", high, name));
        }
        high = field.high+1;
    }
    let name = name.to_string();
    let diagram = Diagram { name, patterns };
    encodings.get_mut(encoding).push(diagram);
    return Ok(());
}

pub fn read_tag_file(file_name: &String, exclusions: &Vec<String>) -> Encodings {
    let file = File::open(file_name).unwrap();
    let reader = BufReader::new(file);
    let mut lines = reader.lines().map(|l| l.unwrap());
    let mut encodings = Encodings::default();
    let exclude = RegexSet::new(exclusions).unwrap();

    while let Some(line) = lines.next() {
        if line.starts_with("TAG:") {
            let components: Vec<&str> = line.split(':').collect();
            if (components.len() == 3) & (components[2] == "diagram") & !(exclude.is_match(components[1])) {
                read_diagram(components[1], &mut lines, &mut encodings).unwrap();
            } else if (components.len() == 4) & (components[3] == "diagram") {
                let name = components[1].to_owned() + ":" + components[2];
                if !(exclude.is_match(&name)) {
                    read_diagram(&name, &mut lines, &mut encodings).unwrap();
                }
            }
        }
    }
    encodings
}

pub fn dump_encodings(encodings: &Encodings) {
    use Encoding::*;
    for encoding in [A64, A32, T32, T16].iter() {
        println!("Encodings for {}", encoding);
        for diagram in encodings.get(*encoding) {
            println!("  {}", diagram);
        }
    }
}

/*
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn foo() {
        let encodings = read_tag_file(&String::from("test.tag"));
        dump_encodings(&encodings);
    }

    #[test]
    fn sample_a64() {
        let encodings = read_tag_file(&String::from("test.tag"));
        let (instr, description) = encodings.random(Encoding::A64);
        println!("{:#010x} {}", instr, description);
    }
}
*/
