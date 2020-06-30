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
