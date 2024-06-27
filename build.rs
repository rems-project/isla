// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Thibaut Pérami
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

use std::env;
use std::path::Path;
use std::process::Command;

fn main() {
    // We can't rely on the system having a reasonably up-to-date z3 on all linux distros, so we can
    // add a libz3.so in the project root and link using it if needed running with LD_LIBRARY_PATH
    println!("cargo:rustc-link-search=.");

    // On macos, libz3 might be installed via homebrew
    if cfg!(target_os = "macos") && cfg!(target_arch = "aarch64") {
        let homebrew_lib_dir = Path::new("/opt/homebrew/lib");
        if homebrew_lib_dir.exists() {
            println!("cargo:rustc-link-search=/opt/homebrew/lib")
        }
    }

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=ISLA_STATIC_Z3");

    // We can alternatively statically link z3
    if env::var("ISLA_STATIC_Z3").is_ok() {
        // if we don't have a z3 library ready-to-go, download and build one.
        if !Path::new("./libz3.a").exists() {
            Command::new("./vendor.sh").output().unwrap();
            Command::new("cp").args(["vendor/z3/build/libz3.a", "libz3.a"]).output().unwrap();
        }

        println!("cargo:rerun-if-changed=libz3.a");

        let target = std::env::var("TARGET").unwrap();
        let cxx = if target.contains("apple") {
            // sigh.
            "c++".to_string()
        } else {
            "stdc++".to_string()
        };

        println!("cargo:rustc-link-lib=static={}", cxx);
        println!("cargo:rustc-link-lib=static:+bundle=z3");
    }
}
