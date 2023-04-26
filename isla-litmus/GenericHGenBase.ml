(**************************************************************************)
(*                                  DIY                                   *)
(*                                                                        *)
(* Jade Alglave, Luc Maranget, INRIA Paris-Rocquencourt, France.          *)
(* Shaked Flur, Susmit Sarkar, Peter Sewell, University of Cambridge, UK. *)
(*                                                                        *)
(*  Copyright 2015 Institut National de Recherche en Informatique et en   *)
(*  Automatique and the authors. All rights reserved.                     *)
(*  This file is distributed  under the terms of the Lesser GNU General   *)
(*  Public License.                                                       *)
(**************************************************************************)

let arch = `Generic

type reg = string

let reg_compare = String.compare

let pp_reg str = str

(* TODO: Figure out what these are for *)
let base = "__BASE__"
let max_idx = "__MAX_IDX__"
let loop_idx = "__LOOP_IDX__"

type instruction = string
type parsedInstruction = string

let nop = "__NOP__"

let dump_instruction str = str
let pp_instruction _ str = str

type barrier = Sync

let pp_barrier = function
  | Sync -> "Sync"

let barrier_compare = Stdlib.compare

let symb_reg r = r

let symb_reg_name r = Some r

let parse_reg r = Some r

include Pseudo.Make
  (struct
    type ins = string
    type pins = string
    type parsedInstruction = string

    let parsed_tr i = i

    type reg_arg = reg

    let get_naccesses _ = failwith "get_naccesses"
    let fold_labels k f ins = k

    let map_labels f ins = ins
  end)

let rec string_of_pseudo = function
  | Nop -> "__NOP__"
  | Label (l, pseudo) -> l ^ ":\n" ^ string_of_pseudo pseudo
  | Instruction str -> "  " ^ str
  | Macro _ -> "MACRO?"
  | Symbolic str -> "SYMBOLIC?"

let allowed_for_symb = []

let fold_regs _f r _ins = r

let map_regs _ _ ins = ins

let fold_addrs _f c _ins = c

let map_addrs _f ins = ins

let norm_ins ins = ins

let get_next = function
  | _ -> [Label.Next]

let get_macro _ = failwith "get_macro"
