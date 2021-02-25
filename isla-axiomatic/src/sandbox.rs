// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
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

//! For running isla-axiomatic via the web interface, we support
//! sandboxing the various assembler and linker commands used when
//! building litmus tests. This is done using the
//! [bubblewrap](https://github.com/containers/bubblewrap) tool, and
//! controlled using the `sandbox` cargo feature.

use std::ffi::{OsStr, OsString};
use std::process::{Child, Command, ExitStatus, Output, Stdio};

use isla_lib::config::Tool;

pub struct SandboxedCommand {
    program: OsString,
    args: Vec<OsString>,
    stdin: Option<Stdio>,
    stdout: Option<Stdio>,
    stderr: Option<Stdio>,
}

impl SandboxedCommand {
    pub fn from_tool(tool: &Tool) -> Self {
        let mut cmd = Self::new(&tool.executable);
        cmd.args(&tool.options);
        cmd
    }

    pub fn new<S: AsRef<OsStr>>(program: S) -> Self {
        SandboxedCommand {
            program: program.as_ref().to_os_string(),
            args: vec![],
            stdin: None,
            stdout: None,
            stderr: None,
        }
    }

    pub fn arg<S: AsRef<OsStr>>(&mut self, arg: S) -> &mut Self {
        self.args.push(arg.as_ref().to_os_string());
        self
    }

    pub fn args<I, S>(&mut self, args: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        for arg in args.into_iter() {
            self.args.push(arg.as_ref().to_os_string());
        }
        self
    }

    pub fn stdin<T: Into<Stdio>>(&mut self, cfg: T) -> &mut Self {
        self.stdin = Some(cfg.into());
        self
    }

    pub fn stdout<T: Into<Stdio>>(&mut self, cfg: T) -> &mut Self {
        self.stdout = Some(cfg.into());
        self
    }

    pub fn stderr<T: Into<Stdio>>(&mut self, cfg: T) -> &mut Self {
        self.stderr = Some(cfg.into());
        self
    }

    #[cfg(feature = "sandbox")]
    fn sandbox(&mut self) -> Command {
        let mut bubblewrap = Command::new("bwrap");

        let sandbox_lib = std::env::var("ISLA_SANDBOX").expect("No ISLA_SANDBOX in environment");

        bubblewrap.args(&[OsStr::new("--ro-bind"), &self.program, &self.program]);
        bubblewrap.args(&["--bind", "/tmp/isla", "/tmp/isla"]);
        bubblewrap.args(&["--ro-bind", &sandbox_lib, "/lib"]);
        bubblewrap.args(&["--symlink", "/lib", "/lib64"]);
        bubblewrap.args(&["--symlink", "/lib", "/usr/lib64"]);
        bubblewrap.args(&["--symlink", "/lib", "/usr/lib"]);
        bubblewrap.arg("--unshare-all");
        bubblewrap.arg("--");

        bubblewrap.arg(&self.program);
        bubblewrap.args(&self.args);

        if let Some(stdin) = self.stdin.take() {
            bubblewrap.stdin(stdin);
        }
        if let Some(stdout) = self.stdout.take() {
            bubblewrap.stdout(stdout);
        }
        if let Some(stderr) = self.stderr.take() {
            bubblewrap.stderr(stderr);
        }

        bubblewrap
    }

    #[cfg(not(feature = "sandbox"))]
    fn sandbox(&mut self) -> Command {
        let mut command = Command::new(&self.program);
        command.args(&self.args);

        if let Some(stdin) = self.stdin.take() {
            command.stdin(stdin);
        }
        if let Some(stdout) = self.stdout.take() {
            command.stdout(stdout);
        }
        if let Some(stderr) = self.stderr.take() {
            command.stderr(stderr);
        }

        command
    }

    pub fn output(&mut self) -> std::io::Result<Output> {
        self.sandbox().output()
    }

    pub fn spawn(&mut self) -> std::io::Result<Child> {
        self.sandbox().spawn()
    }

    pub fn status(&mut self) -> std::io::Result<ExitStatus> {
        self.sandbox().status()
    }
}
