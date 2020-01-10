# 2 "smt_lang_lexer.mll"
 
open Smt_lang_parser
exception Error of string

# 7 "smt_lang_lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\166\255\021\000\006\000\002\000\005\000\179\255\016\000\
    \013\000\001\000\188\255\189\255\019\000\208\255\209\255\210\255\
    \018\000\213\255\214\255\019\000\026\000\017\000\003\000\020\000\
    \020\000\006\000\004\000\039\000\241\255\037\000\039\000\000\000\
    \023\000\045\000\042\000\031\000\103\000\252\255\012\000\254\255\
    \255\255\001\000\253\255\113\000\047\000\039\000\031\000\132\000\
    \235\255\071\000\023\000\247\255\001\000\251\255\002\000\240\255\
    \174\255\068\000\058\000\074\000\001\000\070\000\073\000\069\000\
    \080\000\003\000\250\255\084\000\082\000\088\000\077\000\080\000\
    \076\000\087\000\006\000\249\255\080\000\088\000\082\000\091\000\
    \097\000\083\000\097\000\086\000\095\000\248\255\082\000\097\000\
    \187\255\083\000\104\000\088\000\086\000\095\000\108\000\123\000\
    \128\000\092\000\120\000\109\000\030\000\028\000\031\000\029\000\
    \246\255\243\255\117\000\131\000\119\000\124\000\136\000\233\255\
    \230\255\138\000\141\000\139\000\130\000\224\255\206\255\205\255\
    \141\000\132\000\223\255\134\000\144\000\141\000\152\000\222\255\
    \203\255\201\255\202\255\155\000\153\000\147\000\157\000\158\000\
    \149\000\156\000\144\000\221\255\163\000\220\255\155\000\219\255\
    \199\255\200\255\198\255\196\255\197\255\195\255\164\000\165\000\
    \166\000\163\000\152\000\218\255\162\000\217\255\193\255\194\255\
    \191\255\192\255\158\000\163\000\161\000\216\255\190\255\168\000\
    \204\255\184\255\176\000\163\000\028\000\239\255\245\255\179\000\
    \182\000\169\000\183\000\170\000\171\000\030\000\244\255\180\255\
    \188\000\183\000\181\000\194\000\178\000\192\000\022\000\183\000\
    \185\000\181\000\181\000\242\255\188\000\198\000\023\000\189\000\
    \191\000\187\000\187\000\238\255\188\000\208\000\034\000\237\255\
    \203\000\197\000\025\000\188\000\193\000\209\000\201\000\212\000\
    \236\255\199\000\203\000\246\000\196\000\201\000\217\000\209\000\
    \220\000\234\255\216\000\206\000\222\000\247\000\224\000\225\000\
    \218\000\232\255\225\000\231\255\172\255\214\000\217\000\235\000\
    \234\000\218\000\229\255\238\000\236\000\004\001\237\000\238\000\
    \231\000\228\255\238\000\227\255\228\000\243\000\231\000\230\000\
    \226\255\236\000\232\000\007\001\249\000\252\000\225\255\244\000\
    \185\255\243\000\255\000\002\001\240\000\215\255\252\000\243\000\
    \248\000\250\000\211\255\245\000\248\000\246\000\009\001\249\000\
    \207\255\175\255\251\000\251\000\183\255\251\000\012\001\182\255\
    \009\001\255\000\181\255\015\001\178\255\001\001\005\001\177\255\
    \176\255\171\255";
  Lexing.lex_backtrk =
   "\087\000\255\255\087\000\089\000\089\000\089\000\255\255\089\000\
    \089\000\089\000\255\255\255\255\089\000\255\255\255\255\255\255\
    \089\000\255\255\255\255\089\000\089\000\089\000\089\000\089\000\
    \089\000\089\000\085\000\089\000\255\255\089\000\089\000\043\000\
    \089\000\089\000\089\000\089\000\086\000\255\255\089\000\255\255\
    \255\255\255\255\255\255\086\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \069\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\082\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255";
  Lexing.lex_default =
   "\001\000\000\000\255\255\255\255\255\255\255\255\000\000\255\255\
    \255\255\255\255\000\000\000\000\255\255\000\000\000\000\000\000\
    \255\255\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\000\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000\255\255\000\000\
    \000\000\041\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\000\000\255\255\000\000\255\255\000\000\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\000\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\255\255\255\255\255\255\255\255\255\255\000\000\
    \000\000\255\255\255\255\255\255\255\255\000\000\000\000\000\000\
    \255\255\255\255\000\000\255\255\255\255\255\255\255\255\000\000\
    \000\000\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\000\000\255\255\000\000\255\255\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\255\255\255\255\
    \255\255\255\255\255\255\000\000\255\255\000\000\000\000\000\000\
    \000\000\000\000\255\255\255\255\255\255\000\000\000\000\255\255\
    \000\000\000\000\255\255\255\255\255\255\000\000\000\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\000\000\000\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\000\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\000\000\255\255\255\255\255\255\000\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\255\255\000\000\000\000\255\255\255\255\255\255\
    \255\255\255\255\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\255\255\000\000\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\000\000\255\255\
    \000\000\255\255\255\255\255\255\255\255\000\000\255\255\255\255\
    \255\255\255\255\000\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\255\255\255\255\000\000\255\255\255\255\000\000\
    \255\255\255\255\000\000\255\255\000\000\255\255\255\255\000\000\
    \000\000\000\000";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\040\000\039\000\042\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \040\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \031\000\013\000\000\000\000\000\010\000\053\000\000\000\038\000\
    \002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
    \002\000\002\000\011\000\041\000\055\000\066\000\052\000\028\000\
    \075\000\021\000\020\000\051\000\029\000\002\000\002\000\002\000\
    \002\000\002\000\002\000\002\000\002\000\002\000\002\000\102\000\
    \105\000\103\000\022\000\012\000\101\000\104\000\173\000\024\000\
    \182\000\191\000\199\000\017\000\207\000\014\000\211\000\174\000\
    \061\000\030\000\032\000\019\000\027\000\023\000\033\000\038\001\
    \243\000\005\000\026\001\217\000\009\000\208\000\004\000\003\000\
    \016\000\037\001\034\000\026\000\008\000\007\000\036\000\035\000\
    \041\001\035\001\025\000\018\000\006\000\015\000\032\001\029\001\
    \019\001\014\001\009\001\002\001\252\000\236\000\226\000\020\001\
    \204\000\001\001\184\000\176\000\237\000\090\000\076\000\067\000\
    \089\000\057\000\056\000\046\000\047\000\175\000\077\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\050\000\054\000\058\000\059\000\060\000\
    \048\000\062\000\063\000\064\000\065\000\068\000\069\000\070\000\
    \071\000\072\000\073\000\074\000\086\000\078\000\079\000\080\000\
    \081\000\082\000\083\000\084\000\085\000\087\000\088\000\170\000\
    \045\000\098\000\169\000\167\000\044\000\163\000\162\000\120\000\
    \153\000\100\000\106\000\151\000\097\000\092\000\096\000\091\000\
    \150\000\107\000\099\000\095\000\114\000\094\000\152\000\137\000\
    \093\000\125\000\134\000\133\000\109\000\124\000\113\000\132\000\
    \136\000\112\000\110\000\115\000\111\000\135\000\119\000\123\000\
    \131\000\118\000\108\000\116\000\117\000\121\000\122\000\128\000\
    \130\000\049\000\129\000\126\000\127\000\149\000\148\000\146\000\
    \037\000\255\255\145\000\142\000\140\000\138\000\139\000\141\000\
    \143\000\161\000\159\000\156\000\154\000\147\000\155\000\157\000\
    \166\000\144\000\164\000\165\000\168\000\171\000\172\000\183\000\
    \160\000\158\000\177\000\178\000\179\000\180\000\181\000\186\000\
    \196\000\187\000\185\000\188\000\189\000\190\000\192\000\193\000\
    \194\000\195\000\197\000\198\000\200\000\201\000\202\000\203\000\
    \205\000\206\000\209\000\210\000\212\000\213\000\214\000\215\000\
    \216\000\218\000\219\000\220\000\221\000\222\000\223\000\224\000\
    \225\000\227\000\228\000\229\000\231\000\234\000\232\000\233\000\
    \235\000\230\000\238\000\239\000\240\000\241\000\242\000\244\000\
    \245\000\247\000\250\000\248\000\249\000\251\000\246\000\253\000\
    \254\000\255\000\000\001\007\001\003\001\004\001\005\001\006\001\
    \008\001\010\001\011\001\012\001\013\001\015\001\016\001\017\001\
    \018\001\025\001\021\001\022\001\023\001\024\001\027\001\028\001\
    \030\001\031\001\033\001\034\001\036\001\040\001\039\001\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    ";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\041\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\255\255\255\255\000\000\052\000\255\255\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\038\000\054\000\065\000\050\000\000\000\
    \074\000\000\000\000\000\050\000\000\000\002\000\002\000\002\000\
    \002\000\002\000\002\000\002\000\002\000\002\000\002\000\100\000\
    \101\000\102\000\000\000\000\000\100\000\103\000\172\000\000\000\
    \181\000\190\000\198\000\000\000\206\000\000\000\210\000\031\000\
    \060\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\
    \022\000\000\000\009\000\025\000\000\000\026\000\000\000\000\000\
    \000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \003\000\005\000\000\000\000\000\000\000\000\000\007\000\008\000\
    \012\000\016\000\019\000\020\000\021\000\023\000\024\000\012\000\
    \027\000\020\000\029\000\030\000\023\000\032\000\033\000\034\000\
    \032\000\035\000\044\000\045\000\046\000\030\000\033\000\036\000\
    \036\000\036\000\036\000\036\000\036\000\036\000\036\000\036\000\
    \036\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
    \043\000\043\000\043\000\047\000\049\000\057\000\058\000\059\000\
    \047\000\061\000\062\000\063\000\064\000\067\000\068\000\069\000\
    \070\000\071\000\072\000\073\000\076\000\077\000\078\000\079\000\
    \080\000\081\000\082\000\083\000\084\000\086\000\087\000\089\000\
    \036\000\090\000\091\000\092\000\036\000\093\000\093\000\097\000\
    \094\000\090\000\099\000\094\000\090\000\090\000\090\000\090\000\
    \094\000\106\000\090\000\090\000\098\000\090\000\094\000\095\000\
    \090\000\096\000\095\000\095\000\107\000\096\000\098\000\095\000\
    \095\000\108\000\109\000\098\000\110\000\095\000\113\000\096\000\
    \095\000\114\000\107\000\115\000\116\000\120\000\121\000\124\000\
    \123\000\047\000\123\000\125\000\126\000\131\000\132\000\133\000\
    \000\000\041\000\134\000\135\000\136\000\137\000\138\000\140\000\
    \142\000\150\000\151\000\152\000\153\000\132\000\154\000\156\000\
    \162\000\134\000\163\000\164\000\167\000\170\000\171\000\175\000\
    \150\000\151\000\176\000\177\000\178\000\179\000\180\000\184\000\
    \185\000\186\000\184\000\187\000\188\000\189\000\191\000\192\000\
    \193\000\194\000\196\000\197\000\199\000\200\000\201\000\202\000\
    \204\000\205\000\208\000\209\000\211\000\212\000\213\000\214\000\
    \215\000\217\000\218\000\219\000\220\000\221\000\222\000\223\000\
    \224\000\226\000\227\000\228\000\229\000\230\000\231\000\232\000\
    \234\000\229\000\237\000\238\000\239\000\240\000\241\000\243\000\
    \244\000\245\000\246\000\247\000\248\000\250\000\245\000\252\000\
    \253\000\254\000\255\000\001\001\002\001\003\001\004\001\005\001\
    \007\001\009\001\010\001\011\001\012\001\014\001\015\001\016\001\
    \017\001\019\001\020\001\021\001\022\001\023\001\026\001\027\001\
    \029\001\030\001\032\001\033\001\035\001\037\001\038\001\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    ";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec token lexbuf =
   __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 9 "smt_lang_lexer.mll"
    ( token lexbuf )
# 283 "smt_lang_lexer.ml"

  | 1 ->
# 11 "smt_lang_lexer.mll"
   ( Lexing.new_line lexbuf; token lexbuf )
# 288 "smt_lang_lexer.ml"

  | 2 ->
# 13 "smt_lang_lexer.mll"
    ( Lexing.new_line lexbuf; token lexbuf )
# 293 "smt_lang_lexer.ml"

  | 3 ->
# 15 "smt_lang_lexer.mll"
    ( EOF )
# 298 "smt_lang_lexer.ml"

  | 4 ->
# 17 "smt_lang_lexer.mll"
    ( VALU_APOSTROPHE_APOSTROPHE_COMMA )
# 303 "smt_lang_lexer.ml"

  | 5 ->
# 19 "smt_lang_lexer.mll"
    ( WRITE_UNDERSCORE_KIND_COLON )
# 308 "smt_lang_lexer.ml"

  | 6 ->
# 21 "smt_lang_lexer.mll"
    ( READ_UNDERSCORE_KIND_COLON )
# 313 "smt_lang_lexer.ml"

  | 7 ->
# 23 "smt_lang_lexer.mll"
    ( FIELD_UNDERSCORE_NAME )
# 318 "smt_lang_lexer.ml"

  | 8 ->
# 25 "smt_lang_lexer.mll"
    ( VALU_APOSTROPHE_COMMA )
# 323 "smt_lang_lexer.ml"

  | 9 ->
# 27 "smt_lang_lexer.mll"
    ( BVI_ONE_TWO_EIGHT )
# 328 "smt_lang_lexer.ml"

  | 10 ->
# 29 "smt_lang_lexer.mll"
    ( LPAREN_UNDERSCORE )
# 333 "smt_lang_lexer.ml"

  | 11 ->
# 31 "smt_lang_lexer.mll"
    ( ADDRESS_COLON )
# 338 "smt_lang_lexer.ml"

  | 12 ->
# 33 "smt_lang_lexer.mll"
    ( BVI_SIX_FOUR )
# 343 "smt_lang_lexer.ml"

  | 13 ->
# 35 "smt_lang_lexer.mll"
    ( DECLARECONST )
# 348 "smt_lang_lexer.ml"

  | 14 ->
# 37 "smt_lang_lexer.mll"
    ( QUESTIONMARK )
# 353 "smt_lang_lexer.ml"

  | 15 ->
# 39 "smt_lang_lexer.mll"
    ( VALUUE_COLON )
# 358 "smt_lang_lexer.ml"

  | 16 ->
# 41 "smt_lang_lexer.mll"
    ( BYTES_COLON )
# 363 "smt_lang_lexer.ml"

  | 17 ->
# 43 "smt_lang_lexer.mll"
    ( DEFINECONST )
# 368 "smt_lang_lexer.ml"

  | 18 ->
# 45 "smt_lang_lexer.mll"
    ( DATA_COLON )
# 373 "smt_lang_lexer.ml"

  | 19 ->
# 47 "smt_lang_lexer.mll"
    ( SIGNEXTEND )
# 378 "smt_lang_lexer.ml"

  | 20 ->
# 49 "smt_lang_lexer.mll"
    ( VALU_COMMA )
# 383 "smt_lang_lexer.ml"

  | 21 ->
# 51 "smt_lang_lexer.mll"
    ( ZEROEXTEND )
# 388 "smt_lang_lexer.ml"

  | 22 ->
# 53 "smt_lang_lexer.mll"
    ( BVREDAND )
# 393 "smt_lang_lexer.ml"

  | 23 ->
# 55 "smt_lang_lexer.mll"
    ( WRITEMEM )
# 398 "smt_lang_lexer.ml"

  | 24 ->
# 57 "smt_lang_lexer.mll"
    ( WRITEREG )
# 403 "smt_lang_lexer.ml"

  | 25 ->
# 59 "smt_lang_lexer.mll"
    ( BVREDOR )
# 408 "smt_lang_lexer.ml"

  | 26 ->
# 61 "smt_lang_lexer.mll"
    ( EXTRACT )
# 413 "smt_lang_lexer.ml"

  | 27 ->
# 63 "smt_lang_lexer.mll"
    ( READMEM )
# 418 "smt_lang_lexer.ml"

  | 28 ->
# 65 "smt_lang_lexer.mll"
    ( READREG )
# 423 "smt_lang_lexer.ml"

  | 29 ->
# 67 "smt_lang_lexer.mll"
    ( ASSERT )
# 428 "smt_lang_lexer.ml"

  | 30 ->
# 69 "smt_lang_lexer.mll"
    ( BITVEC )
# 433 "smt_lang_lexer.ml"

  | 31 ->
# 71 "smt_lang_lexer.mll"
    ( BVASHR )
# 438 "smt_lang_lexer.ml"

  | 32 ->
# 73 "smt_lang_lexer.mll"
    ( BVLSHR )
# 443 "smt_lang_lexer.ml"

  | 33 ->
# 75 "smt_lang_lexer.mll"
    ( BVNAND )
# 448 "smt_lang_lexer.ml"

  | 34 ->
# 77 "smt_lang_lexer.mll"
    ( BVSDIV )
# 453 "smt_lang_lexer.ml"

  | 35 ->
# 79 "smt_lang_lexer.mll"
    ( BVSMOD )
# 458 "smt_lang_lexer.ml"

  | 36 ->
# 81 "smt_lang_lexer.mll"
    ( BVSREM )
# 463 "smt_lang_lexer.ml"

  | 37 ->
# 83 "smt_lang_lexer.mll"
    ( BVUDIV )
# 468 "smt_lang_lexer.ml"

  | 38 ->
# 85 "smt_lang_lexer.mll"
    ( BVUREM )
# 473 "smt_lang_lexer.ml"

  | 39 ->
# 87 "smt_lang_lexer.mll"
    ( BVXNOR )
# 478 "smt_lang_lexer.ml"

  | 40 ->
# 89 "smt_lang_lexer.mll"
    ( CONCAT )
# 483 "smt_lang_lexer.ml"

  | 41 ->
# 91 "smt_lang_lexer.mll"
    ( LBRACE )
# 488 "smt_lang_lexer.ml"

  | 42 ->
# 93 "smt_lang_lexer.mll"
    ( LBRACK )
# 493 "smt_lang_lexer.ml"

  | 43 ->
# 95 "smt_lang_lexer.mll"
    ( LPAREN )
# 498 "smt_lang_lexer.ml"

  | 44 ->
# 97 "smt_lang_lexer.mll"
    ( POISON )
# 503 "smt_lang_lexer.ml"

  | 45 ->
# 99 "smt_lang_lexer.mll"
    ( RBRACE )
# 508 "smt_lang_lexer.ml"

  | 46 ->
# 101 "smt_lang_lexer.mll"
    ( RBRACK )
# 513 "smt_lang_lexer.ml"

  | 47 ->
# 103 "smt_lang_lexer.mll"
    ( RPAREN )
# 518 "smt_lang_lexer.ml"

  | 48 ->
# 105 "smt_lang_lexer.mll"
    ( STRUCT )
# 523 "smt_lang_lexer.ml"

  | 49 ->
# 107 "smt_lang_lexer.mll"
    ( BVADD )
# 528 "smt_lang_lexer.ml"

  | 50 ->
# 109 "smt_lang_lexer.mll"
    ( BVAND )
# 533 "smt_lang_lexer.ml"

  | 51 ->
# 111 "smt_lang_lexer.mll"
    ( BVMUL )
# 538 "smt_lang_lexer.ml"

  | 52 ->
# 113 "smt_lang_lexer.mll"
    ( BVNEG )
# 543 "smt_lang_lexer.ml"

  | 53 ->
# 115 "smt_lang_lexer.mll"
    ( BVNOR )
# 548 "smt_lang_lexer.ml"

  | 54 ->
# 117 "smt_lang_lexer.mll"
    ( BVNOT )
# 553 "smt_lang_lexer.ml"

  | 55 ->
# 119 "smt_lang_lexer.mll"
    ( BVSGE )
# 558 "smt_lang_lexer.ml"

  | 56 ->
# 121 "smt_lang_lexer.mll"
    ( BVSGT )
# 563 "smt_lang_lexer.ml"

  | 57 ->
# 123 "smt_lang_lexer.mll"
    ( BVSHL )
# 568 "smt_lang_lexer.ml"

  | 58 ->
# 125 "smt_lang_lexer.mll"
    ( BVSLE )
# 573 "smt_lang_lexer.ml"

  | 59 ->
# 127 "smt_lang_lexer.mll"
    ( BVSLT )
# 578 "smt_lang_lexer.ml"

  | 60 ->
# 129 "smt_lang_lexer.mll"
    ( BVSUB )
# 583 "smt_lang_lexer.ml"

  | 61 ->
# 131 "smt_lang_lexer.mll"
    ( BVUGE )
# 588 "smt_lang_lexer.ml"

  | 62 ->
# 133 "smt_lang_lexer.mll"
    ( BVUGT )
# 593 "smt_lang_lexer.ml"

  | 63 ->
# 135 "smt_lang_lexer.mll"
    ( BVULE )
# 598 "smt_lang_lexer.ml"

  | 64 ->
# 137 "smt_lang_lexer.mll"
    ( BVULT )
# 603 "smt_lang_lexer.ml"

  | 65 ->
# 139 "smt_lang_lexer.mll"
    ( BVXOR )
# 608 "smt_lang_lexer.ml"

  | 66 ->
# 141 "smt_lang_lexer.mll"
    ( COLON )
# 613 "smt_lang_lexer.ml"

  | 67 ->
# 143 "smt_lang_lexer.mll"
    ( COMMA )
# 618 "smt_lang_lexer.ml"

  | 68 ->
# 145 "smt_lang_lexer.mll"
    ( FALSE )
# 623 "smt_lang_lexer.ml"

  | 69 ->
# 147 "smt_lang_lexer.mll"
    ( FIELD )
# 628 "smt_lang_lexer.ml"

  | 70 ->
# 149 "smt_lang_lexer.mll"
    ( BOOL )
# 633 "smt_lang_lexer.ml"

  | 71 ->
# 151 "smt_lang_lexer.mll"
    ( BVOR )
# 638 "smt_lang_lexer.ml"

  | 72 ->
# 153 "smt_lang_lexer.mll"
    ( LIST )
# 643 "smt_lang_lexer.ml"

  | 73 ->
# 155 "smt_lang_lexer.mll"
    ( TRUE )
# 648 "smt_lang_lexer.ml"

  | 74 ->
# 157 "smt_lang_lexer.mll"
    ( UNIT )
# 653 "smt_lang_lexer.ml"

  | 75 ->
# 159 "smt_lang_lexer.mll"
    ( AND )
# 658 "smt_lang_lexer.ml"

  | 76 ->
# 161 "smt_lang_lexer.mll"
    ( BAR )
# 663 "smt_lang_lexer.ml"

  | 77 ->
# 163 "smt_lang_lexer.mll"
    ( ITE )
# 668 "smt_lang_lexer.ml"

  | 78 ->
# 165 "smt_lang_lexer.mll"
    ( NEQ )
# 673 "smt_lang_lexer.ml"

  | 79 ->
# 167 "smt_lang_lexer.mll"
    ( NOT )
# 678 "smt_lang_lexer.ml"

  | 80 ->
# 169 "smt_lang_lexer.mll"
    ( SMT )
# 683 "smt_lang_lexer.ml"

  | 81 ->
# 171 "smt_lang_lexer.mll"
    ( VEC )
# 688 "smt_lang_lexer.ml"

  | 82 ->
# 173 "smt_lang_lexer.mll"
    ( BV )
# 693 "smt_lang_lexer.ml"

  | 83 ->
# 175 "smt_lang_lexer.mll"
    ( EQ )
# 698 "smt_lang_lexer.ml"

  | 84 ->
# 177 "smt_lang_lexer.mll"
    ( OR )
# 703 "smt_lang_lexer.ml"

  | 85 ->
# 179 "smt_lang_lexer.mll"
    ( S )
# 708 "smt_lang_lexer.ml"

  | 86 ->
let
# 180 "smt_lang_lexer.mll"
                   vu32
# 714 "smt_lang_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 181 "smt_lang_lexer.mll"
    ( VU_THREE_TWO (vu32) )
# 718 "smt_lang_lexer.ml"

  | 87 ->
let
# 182 "smt_lang_lexer.mll"
                u32
# 724 "smt_lang_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 183 "smt_lang_lexer.mll"
    ( U_THREE_TWO (int_of_string u32) )
# 728 "smt_lang_lexer.ml"

  | 88 ->
let
# 184 "smt_lang_lexer.mll"
                u64
# 734 "smt_lang_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 185 "smt_lang_lexer.mll"
    ( U_SIX_FOUR (u64) )
# 738 "smt_lang_lexer.ml"

  | 89 ->
# 187 "smt_lang_lexer.mll"
    ( raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) )
# 743 "smt_lang_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

;;

# 190 "smt_lang_lexer.mll"
 

# 753 "smt_lang_lexer.ml"
