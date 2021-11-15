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

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash)]
pub struct Request {
    pub arch: String,
    pub cat: String,
    pub litmus: String,
    pub litmus_format: String,
    pub ignore_ifetch: bool,
    pub exhaustive: bool,
    pub armv8_page_tables: bool,
    pub remove_uninteresting: bool,
    pub merge_translations: bool,
    pub merge_split_stages: bool,
}

#[derive(Serialize, Deserialize)]
pub struct JsRelation {
    pub name: String,
    pub dot: String,
}

#[derive(Serialize, Deserialize)]
pub struct JsGraph {
    pub prefix: String,
    pub relations: Vec<JsRelation>,
    pub suffix: String,
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "tag", content = "content")]
pub enum Response {
    InternalError,
    Error { message: String },
    Done { graphs: Vec<JsGraph>, objdump: String, candidates: i32, shows: Vec<String> },
}
