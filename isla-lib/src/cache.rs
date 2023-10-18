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

use serde::de::DeserializeOwned;
use serde::Serialize;

use std::fs::File;
use std::path::Path;

pub trait Cachekey {
    fn key(&self) -> String;
}

pub trait Cacheable: Serialize + DeserializeOwned {
    type Key: Cachekey;

    fn from_cache<P: AsRef<Path>>(key: Self::Key, cache: P) -> Option<Self> {
        if !cache.as_ref().is_dir() {
            return None;
        };

        let cache_file = cache.as_ref().join(key.key());

        let fd = File::open(cache_file).ok()?;
        bincode::deserialize_from(fd).ok()
    }

    fn cache<P: AsRef<Path>>(&self, key: Self::Key, cache: P) {
        if !cache.as_ref().is_dir() {
            return;
        };

        let cache_file = cache.as_ref().join(key.key());

        if let Ok(fd) = File::create(cache_file) {
            if let Ok(()) = bincode::serialize_into(fd, self) {}
        }
    }
}
