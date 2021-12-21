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

use crate::relocation_types::*;

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug)]
#[repr(u32)]
pub enum RelocationCode {
    R_NONE = 0,
    R_ABS64 = 257,
    R_ABS32 = 258,
    R_ABS16 = 259,
    R_PREL64 = 260,
    R_PREL32 = 261,
    R_PREL16 = 262,

    R_LD_PREL_LO19 = 273,
    R_ADR_PREL_LO21 = 274,
    R_ADR_PREL_PG_HI21 = 275,
    R_ADR_PREL_PG_HI21_NC = 276,
    R_ADD_ABS_LO12_NC = 277,
    R_LDST8_ABS_LO12_NC = 278,
    R_TSTBR14 = 279,
    R_CONDBR19 = 280,
    R_JUMP26 = 282,
    R_CALL26 = 283,
    R_LDST16_ABS_LO12_NC = 284,
    R_LDST32_ABS_LO12_NC = 285,
    R_LDST64_ABS_LO12_NC = 286,
    R_LDST128_ABS_LO12_NC = 299,
}

use Immediate::*;

const LDR_LIT_IMM: Immediate = Imm2(23, 5);
const ADR_IMM: Immediate = Imm4(23, 5, 30, 29);
const ADRP_IMM: Immediate = Imm4(23, 5, 30, 29);
const ADD_IMM: Immediate = Imm2(21, 10);
const LDST8_IMM: Immediate = Imm2(21, 10);
const LDST16_IMM: Immediate = Imm2(20, 10);
const LDST32_IMM: Immediate = Imm2(19, 10);
const LDST64_IMM: Immediate = Imm2(18, 10);
const LDST128_IMM: Immediate = Imm2(17, 10);
const CALL_JUMP_IMM: Immediate = Imm2(25, 0);
const CONDBR_IMM: Immediate = Imm2(23, 5);
const TBZ_IMM: Immediate = Imm2(18, 5);

#[rustfmt::skip]
lazy_static! {
    pub static ref RELOCATION_TABLE: Vec<TableEntry<RelocationCode>> = {
        use RelocationCode::*;
        use Operation::*;
        vec![
            entry(R_ABS64,  S + A,     None,           SLICE64, NoImm),
            entry(R_ABS32,  S + A,     bounds(31, 32), SLICE32, NoImm),
            entry(R_ABS16,  S + A,     bounds(15, 16), SLICE16, NoImm),
            entry(R_PREL64, S + A - P, None,           SLICE64, NoImm),
            entry(R_PREL32, S + A - P, bounds(31, 32), SLICE32, NoImm),
            entry(R_PREL16, S + A - P, bounds(15, 16), SLICE16, NoImm),
            
            entry(R_LD_PREL_LO19,        S + A - P,             bounds(20, 20), Slice::new(20, 2),  LDR_LIT_IMM),
            entry(R_ADR_PREL_LO21,       S + A - P,             bounds(20, 20), Slice::new(20, 0),  ADR_IMM),
            entry(R_ADR_PREL_PG_HI21,    page(S + A) - page(P), bounds(32, 32), Slice::new(32, 12), ADRP_IMM),
            entry(R_ADR_PREL_PG_HI21_NC, page(S + A) - page(P), bounds(32, 32), Slice::new(32, 12), ADRP_IMM),
            entry(R_ADD_ABS_LO12_NC,     S + A,                 None,           Slice::new(11, 0),  ADD_IMM),
            entry(R_LDST8_ABS_LO12_NC,   S + A,                 None,           Slice::new(11, 0),  LDST8_IMM),
            entry(R_LDST16_ABS_LO12_NC,  S + A,                 None,           Slice::new(11, 1),  LDST16_IMM),
            entry(R_LDST32_ABS_LO12_NC,  S + A,                 None,           Slice::new(11, 2),  LDST32_IMM),
            entry(R_LDST64_ABS_LO12_NC,  S + A,                 None,           Slice::new(11, 3),  LDST64_IMM),
            entry(R_LDST128_ABS_LO12_NC, S + A,                 None,           Slice::new(11, 4),  LDST128_IMM),

            entry(R_TSTBR14,  S + A - P, bounds(15, 15), Slice::new(15, 2), TBZ_IMM),
            entry(R_CONDBR19, S + A - P, bounds(20, 20), Slice::new(20, 2), CONDBR_IMM),
            entry(R_JUMP26,   S + A - P, bounds(27, 27), Slice::new(27, 2), CALL_JUMP_IMM),
            entry(R_CALL26,   S + A - P, bounds(27, 27), Slice::new(27, 2), CALL_JUMP_IMM),
        ]
    };
}

pub fn instructions_from_buffer(buf: &[u8]) -> Option<Vec<(u64, u32)>> {
    let mut instrs = Vec::new();

    let iter = buf.chunks_exact(4);
    if !iter.remainder().is_empty() {
        return None;
    }
    for (i, word) in iter.enumerate() {
        instrs.push((u64::try_from(i).ok()? * 4, u32::from_le_bytes([word[0], word[1], word[2], word[3]])))
    }

    Some(instrs)
}
