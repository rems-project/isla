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

use std::error::Error;
use std::io::Write;
use std::str::Lines;

use isla_lib::bitvector::BV;
use isla_lib::ir::{Loc, Name, Symtab};
use isla_lib::zencode;

use super::exp;
use super::exp::Exp;
use super::{Litmus, Thread};

fn ascii_usize(n: usize) -> String {
    let mut s = format!("{:X}", n);
    let bytes = unsafe { s.as_bytes_mut() };
    for byte in bytes.iter_mut() {
        if b'0' <= *byte && *byte <= b'9' {
            *byte += b'G' - b'0'
        }
    }
    s
}

// Because we format each thread in the test in a horizontal table, the
// maximum line length is quite short, meaning lines like:
//
// ldr x0, [x1] // some long comment
//
// can be a problem. This iterator rather then just returning each
// line, will separate the comment from the line and return them as:
//
// // some long comment
// ldr x1, [x1]
//
// It will also remove any blank lines it finds.
struct CompactLines<'a> {
    lines: Lines<'a>,
    remaining_line: Option<&'a str>,
}

impl<'a> CompactLines<'a> {
    fn from_str(s: &'a str) -> Self {
        CompactLines { lines: s.lines(), remaining_line: None }
    }
}

impl<'a> Iterator for CompactLines<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(line) = self.remaining_line {
            self.remaining_line = None;
            return Some(line);
        }

        let new_next = self.lines.next()?;

        if new_next.trim().is_empty() {
            self.next()
        } else if let Some(index) = new_next.find("//") {
            if !new_next[0..index].trim().is_empty() {
                self.remaining_line = Some(&new_next[0..index]);
            }
            Some(&new_next[index..])
        } else {
            Some(new_next)
        }
    }
}

fn loc_latex(loc: &Loc<Name>, symtab: &Symtab) -> String {
    match loc {
        Loc::Id(id) => zencode::decode(symtab.to_str(*id)),
        Loc::Field(loc, field) => format!("{}.{}", loc_latex(loc, symtab), zencode::decode(symtab.to_str(*field))),
        Loc::Addr(loc) => format!("(*{})", loc_latex(loc, symtab)),
    }
}

fn exp_loc_latex(loc: &exp::Loc<String>, symtab: &Symtab) -> String {
    match loc {
        exp::Loc::Register { reg, thread_id } => format!("{}:{}", thread_id, zencode::decode(symtab.to_str(*reg))),
        exp::Loc::LastWriteTo { address, .. } => address.clone(),
    }
}

fn exp_latex<B: BV>(exp: &Exp<String>, symtab: &Symtab, bracket: bool) -> String {
    match exp {
        Exp::Loc(id) => id.to_string(),
        Exp::Label(label) => format!("{}:", label),
        Exp::True => "true".to_string(),
        Exp::False => "false".to_string(),
        Exp::Bin(bin) => format!("0b{}", bin),
        Exp::Hex(hex) => format!("0x{}", hex),
        Exp::Bits64(bits, len) => B::new(*bits, *len).to_string().replace('#', "0"),
        Exp::Nat(n) => n.to_string(),
        // for display, make extz implicit
        Exp::App(f, args, _) if f == "extz" && args.len() == 2 => exp_latex::<B>(&args[0], symtab, bracket),
        Exp::App(f, args, kw_args) => {
            let args = args.iter().map(|arg| exp_latex::<B>(arg, symtab, bracket)).collect::<Vec<_>>().join(",");
            let kw_args = kw_args
                .iter()
                .map(|(kw, arg)| format!("{}={}", kw, exp_latex::<B>(arg, symtab, bracket)))
                .collect::<Vec<_>>()
                .join(",");
            if args.is_empty() {
                format!("{}({})", f, kw_args)
            } else if kw_args.is_empty() {
                format!("{}({})", f, args)
            } else {
                format!("{}({},{})", f, args, kw_args)
            }
        }
        Exp::And(exps) => {
            let exps = exps.iter().map(|exp| exp_latex::<B>(exp, symtab, true)).collect::<Vec<_>>().join(" & ");
            if bracket {
                format!("({})", exps)
            } else {
                exps
            }
        }
        Exp::Or(exps) => {
            let exps = exps.iter().map(|exp| exp_latex::<B>(exp, symtab, true)).collect::<Vec<_>>().join(" | ");
            if bracket {
                format!("({})", exps)
            } else {
                exps
            }
        }
        Exp::Not(exp) => format!("~{}", exp_latex::<B>(exp, symtab, true)),
        Exp::Implies(lhs, rhs) => {
            let exps = format!("{} -> {}", exp_latex::<B>(lhs, symtab, true), exp_latex::<B>(rhs, symtab, true));
            if bracket {
                format!("({})", exps)
            } else {
                exps
            }
        }
        Exp::EqLoc(loc, exp) => format!("{}={}", exp_loc_latex(loc, symtab), exp_latex::<B>(exp, symtab, true)),
    }
}

pub(crate) fn litmus_latex<B: BV>(
    output: &mut dyn Write,
    litmus: &Litmus<B>,
    latex_id: &str,
    vertical: bool,
    symtab: &Symtab,
) -> Result<(), Box<dyn Error>> {
    let mut id_count: usize = 0;
    let mut generate_id = || {
        id_count += 1;
        format!("{}{}", latex_id, ascii_usize(id_count))
    };

    let mut max_lines: usize = 0;
    for thread in &litmus.threads {
        if let Thread::Assembled(thread) = thread {
            max_lines = usize::max(max_lines, CompactLines::from_str(&thread.source).count())
        }
    }
    for section in &litmus.sections {
        max_lines = usize::max(max_lines, CompactLines::from_str(&section.source).count() + 1)
    }

    let mut codes: Vec<(String, String)> = Vec::new();
    let code_width = generate_id();
    writeln!(output, r"\newlength{{\{}}}", code_width)?;
    writeln!(output, r"\setlength{{\{}}}{{0cm}}", code_width)?;

    for (i, thread) in litmus.threads.iter().enumerate() {
        if let Thread::Assembled(thread) = thread {
            let savebox = generate_id();
            let width = generate_id();
            let padding_lines = max_lines - CompactLines::from_str(&thread.source).count();

            writeln!(output, r"\newsavebox{{\{}}}", savebox)?;
            writeln!(output, r"\begin{{lrbox}}{{\{}}}", savebox)?;
            writeln!(output, r"\begin{{lstlisting}}[language={},showlines=true]", &litmus.arch)?;
            for line in CompactLines::from_str(&thread.source) {
                writeln!(output, "{}", line.trim())?;
            }
            if !vertical {
                write!(output, "{}", "\n".repeat(padding_lines))?;
            }
            writeln!(output, r"\end{{lstlisting}}")?;
            writeln!(output, r"\end{{lrbox}}")?;
            writeln!(output, r"\newlength{{\{}}}", width)?;
            writeln!(output, r"\settowidth{{\{}}}{{\usebox{{\{}}}}}", width, savebox)?;
            writeln!(output, r"\addtolength{{\{}}}{{\{}}}", code_width, width)?;

            codes.push((format!("Thread {}", i), savebox))
        }
    }

    for section in &litmus.sections {
        let savebox = generate_id();
        let width = generate_id();
        let padding_lines = max_lines - (CompactLines::from_str(&section.source).count() + 1);
        writeln!(output, r"\newsavebox{{\{}}}", savebox)?;
        writeln!(output, r"\begin{{lrbox}}{{\{}}}", savebox)?;
        writeln!(output, r"\begin{{lstlisting}}[language={},showlines=true]", &litmus.arch)?;
        writeln!(output, "0x{:x}:", section.address)?;
        for line in CompactLines::from_str(&section.source) {
            writeln!(output, "{}", line.trim())?;
        }
        if !vertical {
            write!(output, "{}", "\n".repeat(padding_lines))?;
        }
        writeln!(output, r"\end{{lstlisting}}")?;
        writeln!(output, r"\end{{lrbox}}")?;
        writeln!(output, r"\newlength{{\{}}}", width)?;
        writeln!(output, r"\settowidth{{\{}}}{{\usebox{{\{}}}}}", width, savebox)?;
        writeln!(output, r"\addtolength{{\{}}}{{\{}}}", code_width, width)?;

        codes.push((section.name.replace('_', " "), savebox))
    }

    let page_table_setup_box = generate_id();
    let page_table_setup_width = generate_id();
    writeln!(output, r"\newsavebox{{\{}}}", page_table_setup_box)?;
    writeln!(output, r"\begin{{lrbox}}{{\{}}}", page_table_setup_box)?;
    writeln!(output, r"\begin{{lstlisting}}[language=IslaPageTableSetup,showlines=true]")?;
    write!(output, "{}", litmus.page_table_setup_source)?;
    writeln!(output, r"\end{{lstlisting}}")?;
    writeln!(output, r"\end{{lrbox}}")?;
    writeln!(output, r"\newlength{{\{}}}", page_table_setup_width)?;
    writeln!(output, r"\settowidth{{\{}}}{{\usebox{{\{}}}}}", page_table_setup_width, page_table_setup_box)?;

    let initial_state_box = generate_id();
    writeln!(output, r"\newsavebox{{\{}}}", initial_state_box)?;
    writeln!(output, r"\begin{{lrbox}}{{\{}}}", initial_state_box)?;
    writeln!(output, r"\begin{{minipage}}{{\{}}}", code_width)?;

    write!(output, r"\vphantom{{$\vcenter{{\hbox{{\rule{{0pt}}{{1.8em}}}}}}$}}Initial state:\\")?;
    for (tid, thread) in litmus.threads.iter().enumerate() {
        if let Thread::Assembled(thread) = thread {
            let tid = if litmus.threads.len() == 1 { "".to_string() } else { format!("{}:", tid) };
            for (reg, value) in &thread.inits {
                if *value <= 9 {
                    write!(
                        output,
                        "\n\\lstinline[language=IslaLitmusExp]|{}{}={}|,",
                        tid,
                        zencode::decode(symtab.to_str(*reg)),
                        value
                    )?
                } else {
                    write!(
                        output,
                        "\n\\lstinline[language=IslaLitmusExp]|{}{}=0x{:x}|,",
                        tid,
                        zencode::decode(symtab.to_str(*reg)),
                        value
                    )?
                }
            }
            let mut resets: Vec<(String, String)> = thread
                .reset
                .iter()
                .map(|(loc, exp)| (loc_latex(loc, symtab), exp_latex::<B>(exp, symtab, false)))
                .collect();
            // TODO: BS: retain order from toml rather than lexicographic sort...
            resets.sort_by(|(x, _), (y, _)| x.cmp(y));
            for (loc, exp) in resets {
                write!(output, "\n\\lstinline[language=IslaLitmusExp]|{}{}={}|\\\\", tid, loc, exp)?
            }
        }
    }
    writeln!(output, "\n\\end{{minipage}}")?;
    writeln!(output, r"\end{{lrbox}}")?;

    if vertical {
        writeln!(output, r"\begin{{tabular}}{{|l|l|}}")?;
        writeln!(
            output,
            r"  \multicolumn{{2}}{{l}}{{\textbf{{{}}} \lstinline[language=IslaLitmusName]|{}|}}\\",
            litmus.arch, litmus.name
        )?;
        writeln!(output, r"  \hline")?;

        let pts_header = r"\vphantom{$\vcenter{\hbox{\rule{0pt}{1.8em}}}$}Page table setup:\\".to_string();
        let pts_cell = format!(
            r"\begin{{minipage}}{{\{}}}{}\usebox{{\{}}}\end{{minipage}}",
            page_table_setup_width, pts_header, page_table_setup_box
        );
        writeln!(
            output,
            r"  \multirow{{6}}{{*}}{{{}}} & \cellcolor{{IslaInitialState}}{{\usebox{{\{}}}}}\\",
            pts_cell, initial_state_box
        )?;

        for (name, savebox) in codes.iter() {
            writeln!(output, r"  \cline{{2-2}}")?;
            writeln!(output, r"  & {}\\", name)?;
            writeln!(output, r"  \cline{{2-2}}")?;
            writeln!(output, r"  & \usebox{{\{}}}\\", savebox)?;
        }

        writeln!(output, r"  \cline{{2-2}}")?;
    } else {
        let columns = litmus.threads.len() + litmus.sections.len();
        writeln!(output, r"\begin{{tabular}}{{{}|}}", "|l".repeat(columns))?;
        writeln!(
            output,
            r"  \multicolumn{{{}}}{{l}}{{\textbf{{{}}} \lstinline[language=IslaLitmusName]|{}|}}\\",
            columns, litmus.arch, litmus.name
        )?;
        writeln!(output, r"  \hline")?;
        writeln!(output, r"  \rowcolor{{IslaInitialState}}")?;
        writeln!(output, r"  \multicolumn{{{}}}{{|l|}}{{\usebox{{\{}}}}}\\", columns, initial_state_box)?;
        write!(output, "  \\hline\n  ")?;
        for (i, (column_name, _)) in codes.iter().enumerate() {
            if i != 0 {
                write!(output, " & ")?
            }
            write!(output, "{}", column_name)?;
        }
        writeln!(output, r"\\")?;
        write!(output, "  \\hline\n  ")?;
        for (i, (_, savebox)) in codes.iter().enumerate() {
            if i != 0 {
                write!(output, " & ")?
            }
            write!(output, r"\usebox{{\{}}}", savebox)?;
        }
        writeln!(output, r"\\")?;
        writeln!(output, r"  \hline")?;
    }
    writeln!(
        output,
        r"  & Final state: \lstinline[language=IslaLitmusExp]|{}|\\",
        exp_latex::<B>(&litmus.final_assertion, symtab, false)
    )?;
    writeln!(output, r"  \hline")?;
    writeln!(output, r"\end{{tabular}}")?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ascii_usize() {
        assert_eq!(ascii_usize(0), "G");
        assert_eq!(ascii_usize(0x1234567890), "HIJKLMNOPG");
        assert_eq!(ascii_usize(0x901), "PGH");
        assert_eq!(ascii_usize(0xABCDEF), "ABCDEF")
    }

    #[test]
    fn test_comments_and_lines() {
        let mut source = CompactLines::from_str("mov x0, #2 // comment\neret\n  // indent comment\ndsb sy");
        assert_eq!(source.next().unwrap(), "// comment");
        assert_eq!(source.next().unwrap(), "mov x0, #2 ");
        assert_eq!(source.next().unwrap(), "eret");
        assert_eq!(source.next().unwrap(), "// indent comment");
        assert_eq!(source.next().unwrap(), "dsb sy");
        assert!(source.next().is_none())
    }
}
