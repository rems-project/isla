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

use std::borrow::Borrow;
use std::error::Error;
use std::io::Write;

use isla_lib::smt::Event;

// First we define an iterator over all candidate executions

pub struct Candidates<'a> {
    index: Vec<usize>,
    max_index: Vec<usize>,
    threads: &'a [Vec<Vec<Event>>],
    out_of_bounds: bool,
}

impl<'a> Candidates<'a> {
    pub fn new(threads: &'a [Vec<Vec<Event>>]) -> Self {
        Candidates {
            index: vec![0; threads.len()],
            max_index: threads.iter().map(|t| t.len()).collect(),
            threads,
            out_of_bounds: !threads.iter().all(|t| !t.is_empty()),
        }
    }

    pub fn total(&self) -> usize {
        if self.threads.len() > 0 {
            self.max_index.iter().product()
        } else {
            0
        }
    }
}

fn increment_index(index: &mut [usize], max_index: &[usize], carry: usize) -> bool {
    if carry == index.len() {
        return true;
    }

    index[carry] += 1;
    if index[carry] == max_index[carry] {
        index[carry] = 0;
        increment_index(index, max_index, carry + 1)
    } else {
        false
    }
}

impl<'a> Iterator for Candidates<'a> {
    type Item = Vec<&'a [Event]>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.out_of_bounds {
            None
        } else {
            let mut result = Vec::with_capacity(self.threads.len());
            self.threads.iter().zip(self.index.iter()).for_each(|(thread, i)| result.push(thread[*i].as_ref()));
            self.out_of_bounds = increment_index(&mut self.index, &self.max_index, 0);
            Some(result)
        }
    }
}

fn smt_enum<S>(output: &mut dyn Write, name: &str, elements: &[S]) -> Result<(), Box<dyn Error>>
where
    S: AsRef<str>,
{
    write!(output, "(declare-datatype {}\n  (", name)?;
    for element in elements {
        write!(output, "({})", element.as_ref())?
    }
    writeln!(output, "(IW)))\n")?;
    Ok(())
}

pub fn smt_addr(output: &mut dyn Write) -> Result<(), Box<dyn Error>> {
    writeln!(output, "(define-fun addr ((ev1 Event) (ev2 Event)) false)\n")?;
    Ok(())
}

pub fn smt_data(output: &mut dyn Write) -> Result<(), Box<dyn Error>> {
    writeln!(output, "(define-fun data ((ev1 Event) (ev2 Event)) false)\n")?;
    Ok(())
}

pub fn smt_ctrl(output: &mut dyn Write) -> Result<(), Box<dyn Error>> {
    writeln!(output, "(define-fun ctrl ((ev1 Event) (ev2 Event)) false)\n")?;
    Ok(())
}

pub fn smt_candidate(output: &mut dyn Write, candidate: &[&[Event]]) -> Result<(), Box<dyn Error>> {
    smt_enum(output, "Thread", &(0..candidate.len()).map(|i| format!("T{}", i)).collect::<Vec<_>>())?;

    let mut events: Vec<(Option<usize>, String, &Event)> = Vec::new();
    for (tid, thread) in candidate.iter().enumerate() {
        for (eid, event) in thread.iter().rev().enumerate() {
            match event {
                Event::ReadMem { .. } =>
                    events.push((Some(tid), format!("R{}_{}", eid, tid), event)),
                Event::WriteMem { .. } =>
                    events.push((Some(tid), format!("W{}_{}", eid, tid), event)),
                _ => (),
            }
        }
    }

    smt_enum(output, "Event", &events.iter().map(|(_, eid, _)| eid).collect::<Vec<_>>())?;

    smt_addr(output)?;
    smt_data(output)?;
    smt_ctrl(output)?;
    
    Ok(())
}
