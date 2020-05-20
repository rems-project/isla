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

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use isla_axiomatic::axiomatic::{AxEvent, ThreadId};
use isla_axiomatic::litmus::instruction_from_objdump;
use isla_lib::concrete::BV;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash)]
pub struct Request {
    pub arch: String,
    pub cat: String,
    pub litmus: String,
    pub litmus_format: String,
    pub ignore_ifetch: bool,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct JsEvent {
    instr: Option<String>,
    opcode: String,
    po: usize,
    thread_id: ThreadId,
    name: String,
    value: Option<String>,
}

impl JsEvent {
    /// Create an event to send to the client from an axiomatic
    /// event. For display, we use the objdump output to find the
    /// human-readable assembly instruction, and get values
    /// read/written by memory events as an event name -> read/write
    /// description map.
    #[allow(dead_code)]
    pub fn from_axiomatic<'a, B: BV>(
        ev: &'a AxEvent<B>,
        objdump: &str,
        rw_values: &mut HashMap<String, String>,
    ) -> Self {
        let instr = instruction_from_objdump(&format!("{:x}", ev.opcode), objdump);
        JsEvent {
            instr,
            opcode: format!("{}", ev.opcode),
            po: ev.po,
            thread_id: ev.thread_id,
            name: ev.name.clone(),
            value: rw_values.remove(&ev.name),
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct JsSet {
    pub name: String,
    pub elems: Vec<String>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct JsRelation {
    pub name: String,
    pub edges: Vec<(String, String)>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct JsGraph {
    pub events: Vec<JsEvent>,
    pub sets: Vec<JsSet>,
    pub relations: Vec<JsRelation>,
    pub show: Vec<String>,
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "tag", content = "content")]
pub enum Response {
    InternalError,
    Error { message: String },
    Done { graphs: Vec<JsGraph>, objdump: String, candidates: i32 },
}
