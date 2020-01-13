(* generated by Ott 0.30 from: smt_lang.ott *)
{
open Smt_lang_parser
exception Error of string
}

rule token = parse
| [' ' '\t']
    { token lexbuf }
| '
'
   { Lexing.new_line lexbuf; token lexbuf }
| "//" [^'\n']* '\n'
    { Lexing.new_line lexbuf; token lexbuf }
| eof
    { EOF }
| "sign_extend"
    { SIGN_UNDERSCORE_EXTEND }
| "zero_extend"
    { ZERO_UNDERSCORE_EXTEND }
| "declare-const"
    { DECLARE_MINUS_CONST }
| "define-const"
    { DEFINE_MINUS_CONST }
| "(_"
    { LPAREN_UNDERSCORE }
| "write-reg"
    { WRITE_MINUS_REG }
| "read-reg"
    { READ_MINUS_REG }
| "128"
    { ONE_TWO_EIGHT }
| "bvredand"
    { BVREDAND }
| "formulas"
    { FORMULAS }
| "64"
    { SIX_FOUR }
| "bvredor"
    { BVREDOR }
| "extract"
    { EXTRACT }
| "assert"
    { ASSERT }
| "BitVec"
    { BITVEC }
| "bvashr"
    { BVASHR }
| "bvlshr"
    { BVLSHR }
| "bvnand"
    { BVNAND }
| "bvsdiv"
    { BVSDIV }
| "bvsmod"
    { BVSMOD }
| "bvsrem"
    { BVSREM }
| "bvudiv"
    { BVUDIV }
| "bvurem"
    { BVUREM }
| "bvxnor"
    { BVXNOR }
| "concat"
    { CONCAT }
| "events"
    { EVENTS }
| "{"
    { LBRACE }
| "("
    { LPAREN }
| "poison"
    { POISON }
| "}"
    { RBRACE }
| ")"
    { RPAREN }
| "struct"
    { STRUCT }
| "bvadd"
    { BVADD }
| "bvand"
    { BVAND }
| "bvmul"
    { BVMUL }
| "bvneg"
    { BVNEG }
| "bvnor"
    { BVNOR }
| "bvnot"
    { BVNOT }
| "bvsge"
    { BVSGE }
| "bvsgt"
    { BVSGT }
| "bvshl"
    { BVSHL }
| "bvsle"
    { BVSLE }
| "bvslt"
    { BVSLT }
| "bvsub"
    { BVSUB }
| "bvuge"
    { BVUGE }
| "bvugt"
    { BVUGT }
| "bvule"
    { BVULE }
| "bvult"
    { BVULT }
| "bvxor"
    { BVXOR }
| ","
    { COMMA }
| "false"
    { FALSE }
| "field"
    { FIELD }
| "Bool"
    { BOOL }
| "bvor"
    { BVOR }
| "list"
    { LIST }
| "true"
    { TRUE }
| "unit"
    { UNIT }
| "and"
    { AND }
| "ite"
    { ITE }
| "neq"
    { NEQ }
| "nil"
    { NIL }
| "not"
    { NOT }
| "vec"
    { VEC }
| "eq"
    { EQ }
| "or"
    { OR }
| "s"
    { S }
| 'v'['0'-'9']* as vu32
    { VU_THREE_TWO (vu32) }
| ['0'-'9']* as u32
    { U_THREE_TWO (int_of_string u32) }
| ['0'-'9']* as u64
    { U_SIX_FOUR (u64) }
| '|'['0'-'9''a'-'z''A'-'Z''_']*'|' as name
    { NAME (name) }
| ('b''v''-'?['0'-'9']*) as bvi
    { BVI (bvi) }
| ('#''b'['0'-'1']*)|('#''x'['0'-'9''a'-'f''A'-'F']*) as bv
    { BV (bv) }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }


{
}

