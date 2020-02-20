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

use isla_lib::axiomatic::{AxEvent, ThreadId};
use isla_lib::concrete::BV;
use isla_lib::litmus::instruction_from_objdump;

#[derive(Serialize, Deserialize, Debug)]
pub struct Request {
    pub arch: String,
    pub cat: String,
    pub litmus: String,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct JsEvent {
    instr: String,
    opcode: String,
    po: usize,
    thread_id: ThreadId,
    name: String,
}

impl JsEvent {
    pub fn from_axiomatic<B: BV>(ev: &AxEvent<B>, objdump: &str) -> Self {
        let instr = instruction_from_objdump(&format!("{:x}", ev.opcode.bits()), objdump)
            .unwrap_or_else(|| "".to_string());
        JsEvent { instr, opcode: format!("{}", ev.opcode), po: ev.po, thread_id: ev.thread_id, name: ev.name.clone() }
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
