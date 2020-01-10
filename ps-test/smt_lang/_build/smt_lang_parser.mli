
(* The type of tokens. *)

type token = 
  | ZEROEXTEND
  | VEC_UNDERSCORE_BOOL
  | VAR
  | U_THREE_TWO of (string)
  | U_SIX_FOUR of (string)
  | SIGNEXTEND
  | RPAREN
  | OR
  | NOT
  | NEQ
  | LPAREN
  | ITE
  | EXTRACT
  | EQ
  | EOF
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
  | BVASHR
  | BVAND
  | BVADD
  | BOOL2
  | BOOL1
  | BITVEC
  | BITS_SIX_FOUR
  | BITS
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val exp_start: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Smt_lang_ast.exp)
