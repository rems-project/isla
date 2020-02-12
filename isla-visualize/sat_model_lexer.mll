
{
open Sat_model_parser
}

let ws = [' ''\t']+

let letter = ['a'-'z''A'-'Z']
let digit = ['0'-'9']
let punctuation = [':''.''!''_''-''+''#''@''=''>''<']
let ident = letter|digit|punctuation
let extraident = ident|['('')'' ''\t']

rule token = parse
| '|' (extraident+ as i) '|'
  { IDENT ("|" ^ i ^ "|") }
| ws
  { token lexbuf }
| '\n'
  { Lexing.new_line lexbuf; token lexbuf }
| '('
  { LPAREN }
| ')'
  { RPAREN }
| (ident+ as i)
  { IDENT i }
| eof
  { EOF }
| _ as c
  { Output.fatal (Printf.sprintf "Unexpected character '%c' when parsing SMT model" c) }