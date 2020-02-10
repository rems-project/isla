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

        let fd = File::open(&cache_file).ok()?;
        bincode::deserialize_from(fd).ok()
    }

    fn cache<P: AsRef<Path>>(&self, key: Self::Key, cache: P) {
        if !cache.as_ref().is_dir() {
            return ();
        };

        let cache_file = cache.as_ref().join(key.key());

        if let Ok(fd) = File::create(&cache_file) {
            if let Ok(()) = bincode::serialize_into(fd, self) {
                ()
            }
        }
    }
}
