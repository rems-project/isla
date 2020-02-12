
%token <string> IDENT
%token LPAREN RPAREN
%token EOF

%start sexpr_eof
%start sexpr_list_eof
%type <Sexpr.sexpr> sexpr_eof
%type <Sexpr.sexpr list> sexpr_list_eof

%%

sexpr_eof:
| sexpr EOF { $1 }

sexpr_list_eof:
| empty_sexpr_list EOF { $1 }

sexpr:
| IDENT { Atom $1 }
| LPAREN empty_sexpr_list RPAREN { List $2 }

sexpr_list:
| sexpr { [$1] }
| sexpr sexpr_list { $1 :: $2 }

empty_sexpr_list:
| { [] }
| sexpr_list { $1 }
