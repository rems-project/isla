// BSD 2-Clause License
//
// Copyright (c) 2019, 2020 Alasdair Armstrong
// Copyright (c) 2020 Brian Campbell
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

use std::cmp;
use std::convert::TryInto;
use std::path::Path;

use serde::{Deserialize, Serialize};

pub static RED: &str = "\x1b[0;31m";
pub static GREEN: &str = "\x1b[0;32m";
pub static BLUE: &str = "\x1b[0;34m";
pub static NO_COLOR: &str = "\x1b[0m";

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct SourceLoc {
    file: i16,
    line1: u32,
    char1: u16,
    line2: u32,
    char2: u16,
}

impl SourceLoc {
    pub fn unknown() -> Self {
        SourceLoc { file: -1, line1: 0, char1: 0, line2: 0, char2: 0 }
    }

    pub fn is_unknown(self) -> bool {
        self.file == -1
    }

    pub(crate) fn unknown_unique(n: u32) -> Self {
        SourceLoc { file: -1, line1: n, char1: 0, line2: 0, char2: 0 }
    }

    pub fn command_line() -> Self {
        SourceLoc { file: -2, line1: 0, char1: 0, line2: 0, char2: 0 }
    }

    pub fn new(file: i16, line1: u32, char1: u16, line2: u32, char2: u16) -> Self {
        if file < 0 {
            SourceLoc::unknown()
        } else {
            SourceLoc { file, line1, char1, line2, char2 }
        }
    }

    fn canonicalize(self) -> Self {
        if self.line1 > self.line2 {
            SourceLoc { line1: self.line2, line2: self.line1, ..self }
        } else if self.line1 == self.line2 && self.char1 > self.char2 {
            SourceLoc { char1: self.char2, char2: self.char1, ..self }
        } else {
            self
        }
    }

    fn one_line_message(
        self,
        buf: &str,
        message: &str,
        file_info: &str,
        red: &str,
        blue: &str,
        no_color: &str,
    ) -> String {
        let mut line = "";

        for (n, l) in buf.lines().enumerate() {
            if n == (self.line1 - 1) as usize {
                line = l;
                break;
            };
        }

        let line_number = self.line1.to_string();
        let number_column_width = line_number.len();

        let file_info = format!("{:width$}{}", "", file_info, width = number_column_width);
        let extra_padding = format!("{:width$} {}|{}", "", blue, no_color, width = number_column_width);

        let line_display =
            format!("{}{:>width$} |{} {}", blue, line_number, no_color, line, width = number_column_width);
        let line_marker = {
            let dashes = "-".repeat(self.char2.saturating_sub(self.char1 + 2) as usize);
            let highlight = if self.char1 + 1 < self.char2 { format!("^{}^", dashes) } else { "^".to_string() };
            format!(
                "{:width$} {}|{} {:gap$}{}{}{}",
                "",
                blue,
                no_color,
                "",
                red,
                highlight,
                no_color,
                width = number_column_width,
                gap = (self.char1 as usize)
            )
        };

        format!("{}{}\n{}\n{}\n{}", message, file_info, extra_padding, line_display, line_marker,)
    }

    fn two_line_message(
        self,
        buf: &str,
        message: &str,
        file_info: &str,
        red: &str,
        blue: &str,
        no_color: &str,
    ) -> String {
        let mut line1 = "";
        let mut line2 = "";

        for (n, line) in buf.lines().enumerate() {
            if n == (self.line1 - 1) as usize {
                line1 = line
            };
            if n == (self.line2 - 1) as usize {
                line2 = line;
                break;
            };
        }

        let line1_number = self.line1.to_string();
        let line2_number = self.line2.to_string();
        let number_column_width = cmp::max(line1_number.len(), line2_number.len());

        let file_info = format!("{:width$}{}", "", file_info, width = number_column_width);
        let extra_padding = format!("{:width$} {}|{}", "", blue, no_color, width = number_column_width);

        let line1_display =
            format!("{}{:>width$} |{} {}", blue, line1_number, no_color, line1, width = number_column_width);
        let line1_marker = {
            let dashes = if usize::from(self.char1) >= line1.len() {
                "".to_string()
            } else {
                "-".repeat(line1.len() - (self.char1 as usize + 1))
            };
            format!(
                "{:width$} {}|{} {:gap$}{}^{}{}",
                "",
                blue,
                no_color,
                "",
                red,
                dashes,
                no_color,
                width = number_column_width,
                gap = (self.char1 as usize)
            )
        };

        let inbetween_marker =
            if self.line1 + 1 < self.line2 { format!("{}...{}\n", blue, no_color) } else { "".to_string() };

        let line2_display =
            format!("{}{:>width$} |{} {}", blue, line2_number, no_color, line2, width = number_column_width);
        let line2_marker = {
            let dashes = if self.char2 <= 1 { "".to_string() } else { "-".repeat(self.char2 as usize - 1) };
            format!("{:width$} {}|{} {}{}^{}", "", blue, no_color, red, dashes, no_color, width = number_column_width)
        };

        format!(
            "{}{}\n{}\n{}\n{}\n{}{}\n{}",
            message,
            file_info,
            extra_padding,
            line1_display,
            line1_marker,
            inbetween_marker,
            line2_display,
            line2_marker,
        )
    }

    fn message_str(self, buf: &str, message: &str, file_info: &str, red: &str, blue: &str, no_color: &str) -> String {
        if self.line1 == self.line2 {
            self.canonicalize().one_line_message(buf, message, file_info, red, blue, no_color)
        } else {
            self.canonicalize().two_line_message(buf, message, file_info, red, blue, no_color)
        }
    }

    pub fn location_string(self, files: &[&str]) -> String {
        if let Some(file) = TryInto::<usize>::try_into(self.file).ok().and_then(|i| files.get(i)) {
            format!("{} {}:{} - {}:{}", file, self.line1, self.char1, self.line2, self.char2)
        } else {
            format!("{}:{} - {}:{}", self.line1, self.char1, self.line2, self.char2)
        }
    }

    pub fn message_file_contents(
        self,
        buf_name: &str,
        buf: &str,
        message: &str,
        is_error: bool,
        use_colors: bool,
    ) -> String {
        let red = if use_colors && is_error {
            RED
        } else if use_colors {
            GREEN
        } else {
            ""
        };
        let blue = if use_colors { BLUE } else { "" };
        let no_color = if use_colors { NO_COLOR } else { "" };

        let file_info = format!("{}-->{} {}:{}:{}", blue, no_color, buf_name, self.line1, self.char1);

        self.message_str(buf, &format!("{}error{}: {}\n", red, no_color, message), &file_info, red, blue, no_color)
    }

    /// Print a message associated with an original source code
    /// location. It takes a base directory and a list of source file
    /// paths relative to that base directory. The file index in the
    /// location will then be used to choose while file to read.
    pub fn message<P: AsRef<Path>>(
        self,
        dir: Option<P>,
        files: &[&str],
        message: &str,
        is_error: bool,
        use_colors: bool,
    ) -> String {
        let red = if use_colors && is_error {
            RED
        } else if use_colors {
            GREEN
        } else {
            ""
        };
        let blue = if use_colors { BLUE } else { "" };
        let no_color = if use_colors { NO_COLOR } else { "" };

        let (short_error, error_sep) = if is_error {
            (format!("{}error{}: {}", red, no_color, message), "\n")
        } else {
            (message.to_string(), "\n")
        };

        let file = TryInto::<usize>::try_into(self.file).ok().and_then(|i| files.get(i));
        if file.is_none() {
            return short_error;
        }
        let file_info = format!("{}-->{} {}:{}:{}", blue, no_color, file.unwrap(), self.line1, self.char1);

        if let Some(dir) = dir {
            let path = dir.as_ref().join(file.unwrap());
            if !path.is_file() {
                return format!("{}{} {}", short_error, error_sep, file_info);
            }

            if let Ok(buf) = std::fs::read_to_string(&path) {
                self.message_str(&buf, &format!("{}{}", short_error, error_sep), &file_info, red, blue, no_color)
            } else {
                format!("{}{} {}", short_error, error_sep, file_info)
            }
        } else {
            format!("{}{} {}", short_error, error_sep, file_info)
        }
    }
}
