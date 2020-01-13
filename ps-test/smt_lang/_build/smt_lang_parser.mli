
(* The type of tokens. *)

type token = 
  | ZERO_UNDERSCORE_EXTEND
  | WRITE_MINUS_REG
  | VU_THREE_TWO of (string)
  | VEC
  | U_THREE_TWO of (int)
  | U_SIX_FOUR of (string)
  | UNIT
  | TRUE
  | STRUCT
  | SIX_FOUR
  | SIGN_UNDERSCORE_EXTEND
  | S
  | RPAREN
  | READ_MINUS_REG
  | RBRACE
  | POISON
  | OR
  | ONE_TWO_EIGHT
  | NOT
  | NIL
  | NEQ
  | NAME of (string)
  | LPAREN_UNDERSCORE
  | LPAREN
  | LIST
  | LBRACE
  | ITE
  | FORMULAS
  | FIELD
  | FALSE
  | EXTRACT
  | EVENTS
  | EQ
  | EOF
  | DEFINE_MINUS_CONST
  | DECLARE_MINUS_CONST
  | CONCAT
  | COMMA
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
  | BVI of (string)
  | BVASHR
  | BVAND
  | BVADD
  | BV of (string)
  | BOOL
  | BITVEC
  | ASSERT
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val term_start: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Smt_lang_ast.term)
