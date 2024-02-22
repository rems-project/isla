// BSD 2-Clause License
//
// Copyright (c) 2021 Alasdair Armstrong
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

use gimli::{read::Dwarf, read::EndianSlice, DwarfFileType, RunTimeEndian};
use goblin::{elf, elf::sym::SymIterator, elf::Elf, Object};
use std::marker::PhantomData;

use isla_lib::bitvector::BV;
use isla_lib::smt::Solver;
use isla_lib::source_loc::SourceLoc;

use crate::arch::{get_table_entry, Architecture, AsBits};
use crate::relocation_types::{SymbolicRelocation, TableEntry};

#[derive(Debug)]
pub enum Place<'elf> {
    Section { name: &'elf str, offset: u64 },
    Global { name: &'elf str },
    Func { name: &'elf str },
    Object { name: &'elf str },
}

#[derive(Debug)]
pub struct Relocation<'elf> {
    pub addend: Option<i64>,
    pub place: Place<'elf>,
    r_type: u32,
}

#[derive(Debug)]
pub struct Instr<'elf, O> {
    offset: u64,
    pub opcode: O,
    pub relocation: Option<Relocation<'elf>>,
}

impl<'elf, O: AsBits> Instr<'elf, O> {
    pub fn has_relocation(&self) -> bool {
        self.relocation.is_some()
    }

    pub fn relocation_table_entry<A: Architecture>(&self) -> Option<&'static TableEntry<A::RelocationCode>> {
        Some(get_table_entry::<A>(self.relocation.as_ref()?.r_type))
    }

    pub fn relocate_symbolic<A: Architecture, B: BV>(
        &self,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Option<SymbolicRelocation<B>> {
        let entry = self.relocation_table_entry::<A>()?;
        let addend = self.relocation.as_ref()?.addend.unwrap_or(0);

        Some(entry.symbolic(self.opcode.as_bits::<B>(), addend, solver, info))
    }
}

#[derive(Debug)]
pub struct Function<'elf, O> {
    name: &'elf str,
    sh_offset: u64,
    pub st_value: u64,
    pub st_size: u64,
    pub instructions: Vec<Instr<'elf, O>>,
}

impl<'elf, O> Function<'elf, O> {
    pub fn name(&self) -> &'elf str {
        self.name
    }

    pub fn section_offset(&self) -> usize {
        self.sh_offset as usize
    }

    pub fn function_offset(&self) -> usize {
        self.st_value as usize
    }

    /// Return the nth instruction in a function
    pub fn get_instruction<'a>(&'a self, i: usize) -> Option<&'a Instr<'elf, O>> {
        self.instructions.get(i)
    }

    /// Return the instruction at an offset from the start of the
    /// section containing the function. This is useful as these
    /// offsets are what is shown by `objdump -d` when disassembling
    /// object files.
    pub fn get_instruction_at_section_offset<'a>(&'a self, offset: u64) -> Option<&'a Instr<'elf, O>> {
        self.instructions.iter().find(|&instr| self.st_value + instr.offset == offset)
    }
}

pub fn elf_function<'elf, A>(elf: &Elf<'elf>, buf: &'elf [u8], function_name: &str) -> Option<Function<'elf, A::Opcode>>
where
    A: Architecture,
{
    for sym in elf.syms.iter() {
        if sym.is_function() {
            let name = elf.strtab.get_at(sym.st_name);
            if name == Some(function_name) {
                let section = elf.section_headers.get(sym.st_shndx)?;

                let offset = (section.sh_offset + sym.st_value) as usize;
                let opcodes = A::instructions_from_buffer(&buf[offset..(offset + sym.st_size as usize)])?;

                let mut relocation_section = None;
                for (shndx, relocs) in &elf.shdr_relocs {
                    let section = elf.section_headers.get(*shndx)?;
                    if section.sh_info as usize == sym.st_shndx {
                        relocation_section = Some(relocs)
                    }
                }

                let mut instructions = Vec::new();
                for (instr_offset, opcode) in opcodes.into_iter() {
                    let mut relocation = None;
                    for reloc in relocation_section.iter().flat_map(|s| s.iter()) {
                        if reloc.r_offset == instr_offset + sym.st_value {
                            let r_sym = elf.syms.get(reloc.r_sym)?;
                            let r_sec = elf.section_headers.get(r_sym.st_shndx)?;
                            relocation = Some(Relocation {
                                addend: reloc.r_addend,
                                place: match (r_sym.st_type(), r_sym.st_bind()) {
                                    (t, b) if t == elf::sym::STT_SECTION && b == elf::sym::STB_LOCAL => {
                                        Place::Section {
                                            name: elf.shdr_strtab.get_at(r_sec.sh_name)?,
                                            offset: r_sym.st_value,
                                        }
                                    }
                                    (t, b) if t == elf::sym::STT_NOTYPE && b == elf::sym::STB_GLOBAL => {
                                        Place::Global { name: elf.strtab.get_at(r_sym.st_name)? }
                                    }
                                    (t, b) if t == elf::sym::STT_FUNC && b == elf::sym::STB_WEAK => {
                                        Place::Func { name: elf.strtab.get_at(r_sym.st_name)? }
                                    }
                                    (t, b) => {
                                        eprintln!(
                                            "Warn: Could not interpret STT {} or STB {} in function relocation",
                                            t, b
                                        );
                                        return None;
                                    }
                                },
                                r_type: reloc.r_type,
                            });
                            break;
                        }
                    }

                    instructions.push(Instr { offset: instr_offset, opcode, relocation })
                }

                return Some(Function {
                    name: name.unwrap(),
                    sh_offset: section.sh_offset,
                    st_value: sym.st_value,
                    st_size: sym.st_size,
                    instructions,
                });
            }
        }
    }
    None
}

pub struct ElfFunctions<'a, 'elf, A> {
    elf: &'a Elf<'elf>,
    buf: &'elf [u8],
    syms: SymIterator<'elf>,
    phantom: PhantomData<A>,
}

impl<'a, 'elf, A: Architecture> Iterator for ElfFunctions<'a, 'elf, A> {
    type Item = Function<'elf, A::Opcode>;

    fn next(&mut self) -> Option<Self::Item> {
        let sym = self.syms.next()?;
        if sym.is_function() {
            let name = self.elf.strtab.get_at(sym.st_name).expect("Could not find function name in strtab");

            let section = self.elf.section_headers.get(sym.st_shndx).unwrap();

            let offset = (section.sh_offset + sym.st_value) as usize;
            let opcodes = A::instructions_from_buffer(&self.buf[offset..(offset + sym.st_size as usize)]).unwrap();

            let mut relocation_section = None;
            for (shndx, relocs) in &self.elf.shdr_relocs {
                let section = self.elf.section_headers.get(*shndx)?;
                if section.sh_info as usize == sym.st_shndx {
                    relocation_section = Some(relocs)
                }
            }

            let mut instructions = Vec::new();
            for (instr_offset, opcode) in opcodes.into_iter() {
                let mut relocation = None;
                for reloc in relocation_section.iter().flat_map(|s| s.iter()) {
                    if reloc.r_offset == instr_offset + sym.st_value {
                        let r_sym = self.elf.syms.get(reloc.r_sym)?;
                        let r_sec = self.elf.section_headers.get(r_sym.st_shndx)?;
                        relocation = Some(Relocation {
                            addend: reloc.r_addend,
                            place: match (r_sym.st_type(), r_sym.st_bind()) {
                                (t, b) if t == elf::sym::STT_SECTION && b == elf::sym::STB_LOCAL => Place::Section {
                                    name: self.elf.shdr_strtab.get_at(r_sec.sh_name)?,
                                    offset: r_sym.st_value,
                                },
                                (t, b) if t == elf::sym::STT_NOTYPE && b == elf::sym::STB_GLOBAL => {
                                    Place::Global { name: self.elf.strtab.get_at(r_sym.st_name)? }
                                }
                                (t, _) if t == elf::sym::STT_FUNC => {
                                    Place::Func { name: self.elf.strtab.get_at(r_sym.st_name)? }
                                }
                                (t, _) if t == elf::sym::STT_OBJECT => {
                                    Place::Object { name: self.elf.strtab.get_at(r_sym.st_name)? }
                                }
                                (t, b) => {
                                    eprintln!(
                                        "Warn: Could not interpret STT {} or STB {} in function relocation",
                                        t, b
                                    );
                                    return None;
                                }
                            },
                            r_type: reloc.r_type,
                        });
                        break;
                    }
                }

                instructions.push(Instr { offset: instr_offset, opcode, relocation })
            }

            Some(Function {
                name,
                sh_offset: section.sh_offset,
                st_value: sym.st_value,
                st_size: sym.st_size,
                instructions,
            })
        } else {
            self.next()
        }
    }
}

pub fn functions_iter<'a, 'elf, A: Architecture>(elf: &'a Elf<'elf>, buf: &'elf [u8]) -> ElfFunctions<'a, 'elf, A> {
    ElfFunctions { elf, buf, syms: elf.syms.iter(), phantom: PhantomData }
}

pub fn parse_elf_with_debug_info(
    buf: &[u8],
) -> Option<(RunTimeEndian, Elf<'_>, Dwarf<EndianSlice<'_, RunTimeEndian>>)> {
    if let Object::Elf(elf) = Object::parse(buf).unwrap() {
        let endianness = if elf.little_endian { RunTimeEndian::Little } else { RunTimeEndian::Big };

        // Load the DWARF debugging info from the ELF file
        let mut dwarf = Dwarf::load::<_, ()>(|dwarf_section| {
            for section in &elf.section_headers {
                if elf.shdr_strtab.get_at(section.sh_name) == Some(dwarf_section.name()) {
                    return Ok(EndianSlice::new(
                        &buf[section.sh_offset as usize..(section.sh_offset + section.sh_size) as usize],
                        endianness,
                    ));
                }
            }
            Ok(EndianSlice::new(&[], endianness))
        })
        .unwrap();
        dwarf.file_type = DwarfFileType::Main;

        Some((endianness, elf, dwarf))
    } else {
        None
    }
}
