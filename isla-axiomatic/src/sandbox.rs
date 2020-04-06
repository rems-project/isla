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

use std::ffi::{OsStr, OsString};
use std::process::{Child, Command, ExitStatus, Output, Stdio};

pub struct SandboxedCommand {
    program: OsString,
    args: Vec<OsString>,
    stdin: Option<Stdio>,
    stdout: Option<Stdio>,
    stderr: Option<Stdio>,
}

impl SandboxedCommand {
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
        bubblewrap.args(&["--ro-bind", sandbox_lib, "/lib"]);
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
