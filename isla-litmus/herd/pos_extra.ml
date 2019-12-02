open Lexing

let str_pos pos =
  Printf.sprintf
    "File \"%s\", line %i, character %i"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol)

let str_pos2 (pos1,  pos2) =
  Printf.sprintf
    "File \"%s\", line %i, characters %i-%i"
    pos1.pos_fname
    pos1.pos_lnum
    (pos1.pos_cnum - pos1.pos_bol)
    (pos2.pos_cnum - pos1.pos_bol)
