
(* The type of tokens. *)

type token = 
  | ZEROEXTEND
  | WRITE_UNDERSCORE_KIND_COLON
  | WRITEREG
  | WRITEMEM
  | VU_THREE_TWO of (string)
  | VEC
  | VALU_COMMA
  | VALU_APOSTROPHE_COMMA
  | VALU_APOSTROPHE_APOSTROPHE_COMMA
  | VALUUE_COLON
  | U_THREE_TWO of (int)
  | U_SIX_FOUR of (string)
  | UNIT
  | TRUE
  | STRUCT
  | SMT
  | SIGNEXTEND
  | S
  | RPAREN
  | READ_UNDERSCORE_KIND_COLON
  | READREG
  | READMEM
  | RBRACK
  | RBRACE
  | QUESTIONMARK
  | POISON
  | OR
  | NOT
  | NEQ
  | LPAREN_UNDERSCORE
  | LPAREN
  | LIST
  | LBRACK
  | LBRACE
  | ITE
  | FIELD_UNDERSCORE_NAME
  | FIELD
  | FALSE
  | EXTRACT
  | EQ
  | EOF
  | DEFINECONST
  | DECLARECONST
  | DATA_COLON
  | CONCAT
  | COMMA
  | COLON
  | BYTES_COLON
  | BVXOR
  | BVXNOR
  | BVUREM
  | BVULT
  | BVULE
  | BVUGT
  | BVUGE
  | BVUDIV
  | BVSUB
  | BVSREM
  | BVSMOD
  | BVSLT
  | BVSLE
  | BVSHL
  | BVSGT
  | BVSGE
  | BVSDIV
  | BVREDOR
  | BVREDAND
  | BVOR
  | BVNOT
  | BVNOR
  | BVNEG
  | BVNAND
  | BVMUL
  | BVLSHR
  | BVI_SIX_FOUR
  | BVI_ONE_TWO_EIGHT
  | BVASHR
  | BVAND
  | BVADD
  | BV
  | BOOL
  | BITVEC
  | BAR
  | ASSERT
  | AND
  | ADDRESS_COLON

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val term_start: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Smt_lang_ast.term)
