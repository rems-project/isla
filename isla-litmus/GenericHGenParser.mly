/**************************************************************************/
/*                                  DIY                                   */
/*                                                                        */
/* Jade Alglave, Luc Maranget, INRIA Paris-Rocquencourt, France.          */
/* Shaked Flur, Susmit Sarkar, Peter Sewell, University of Cambridge, UK. */
/*                                                                        */
/*  Copyright 2015 Institut National de Recherche en Informatique et en   */
/*  Automatique and the authors. All rights reserved.                     */
/*  This file is distributed  under the terms of the Lesser GNU General   */
/*  Public License.                                                       */
/**************************************************************************/

%{
module Generic = GenericHGenBase

open Generic
%}

%token <string> CHUNK
%token <string> LABEL
%token <int> PROC

%token EOF

%token SEMI PIPE

%type <int list * (GenericHGenBase.parsedPseudo) list list * MiscParser.extra_data> main
%start main

%%

main:
| semi_opt proc_list iol_list EOF { $2,$3,MiscParser.NoExtra }

semi_opt:
| { () }
| SEMI { () }

proc_list:
| PROC SEMI { [$1] }
| PROC PIPE proc_list { $1 :: $3 }

iol_list:
| instr_option_list SEMI { [$1] }
| instr_option_list SEMI iol_list { $1 :: $3 }

instr_option_list:
| instr_option {[$1]}
| instr_option PIPE instr_option_list { $1 :: $3 }

instr_option:
| { Nop }
| LABEL instr_option { Label ($1, $2) }
| instr { Instruction $1 }

instr:
| CHUNK instr { $1 ^ " " ^ $2 }
| CHUNK { $1 }
