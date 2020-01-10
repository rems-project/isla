
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | ZEROEXTEND
    | WRITE_UNDERSCORE_KIND_COLON
    | WRITEREG
    | WRITEMEM
    | VU_THREE_TWO of (
# 88 "smt_lang_parser.mly"
       (string)
# 15 "smt_lang_parser.ml"
  )
    | VEC
    | VALU_COMMA
    | VALU_APOSTROPHE_COMMA
    | VALU_APOSTROPHE_APOSTROPHE_COMMA
    | VALUUE_COLON
    | U_THREE_TWO of (
# 89 "smt_lang_parser.mly"
       (int)
# 25 "smt_lang_parser.ml"
  )
    | U_SIX_FOUR of (
# 90 "smt_lang_parser.mly"
       (string)
# 30 "smt_lang_parser.ml"
  )
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
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState271
  | MenhirState267
  | MenhirState257
  | MenhirState248
  | MenhirState231
  | MenhirState230
  | MenhirState227
  | MenhirState226
  | MenhirState223
  | MenhirState222
  | MenhirState219
  | MenhirState218
  | MenhirState215
  | MenhirState214
  | MenhirState211
  | MenhirState210
  | MenhirState207
  | MenhirState206
  | MenhirState203
  | MenhirState200
  | MenhirState199
  | MenhirState196
  | MenhirState193
  | MenhirState192
  | MenhirState189
  | MenhirState186
  | MenhirState183
  | MenhirState182
  | MenhirState179
  | MenhirState178
  | MenhirState175
  | MenhirState174
  | MenhirState171
  | MenhirState170
  | MenhirState167
  | MenhirState166
  | MenhirState163
  | MenhirState162
  | MenhirState159
  | MenhirState158
  | MenhirState155
  | MenhirState154
  | MenhirState151
  | MenhirState150
  | MenhirState147
  | MenhirState146
  | MenhirState143
  | MenhirState142
  | MenhirState139
  | MenhirState138
  | MenhirState135
  | MenhirState134
  | MenhirState131
  | MenhirState130
  | MenhirState127
  | MenhirState126
  | MenhirState123
  | MenhirState122
  | MenhirState119
  | MenhirState118
  | MenhirState115
  | MenhirState114
  | MenhirState111
  | MenhirState110
  | MenhirState107
  | MenhirState106
  | MenhirState105
  | MenhirState102
  | MenhirState96
  | MenhirState91
  | MenhirState85
  | MenhirState84
  | MenhirState81
  | MenhirState77
  | MenhirState75
  | MenhirState69
  | MenhirState65
  | MenhirState42
  | MenhirState34
  | MenhirState23
  | MenhirState17
  | MenhirState14
  | MenhirState10
  | MenhirState8
  | MenhirState4
  | MenhirState0

# 2 "smt_lang_parser.mly"
  
open Smt_lang_ast

# 213 "smt_lang_parser.ml"

let rec _menhir_goto_loption_separated_nonempty_list_COMMA_valu__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.valu list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, (xs : (Smt_lang_ast.valu list))) = _menhir_stack in
                let _6 = () in
                let _5 = () in
                let _3 = () in
                let _2 = () in
                let _1 = () in
                let _v : (Smt_lang_ast.valu) = let valu0 = 
# 232 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( xs )
# 242 "smt_lang_parser.ml"
                 in
                
# 118 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Vector(valu0) )
# 247 "smt_lang_parser.ml"
                 in
                _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, (xs : (Smt_lang_ast.valu list))) = _menhir_stack in
                let _6 = () in
                let _5 = () in
                let _3 = () in
                let _2 = () in
                let _1 = () in
                let _v : (Smt_lang_ast.valu) = let valu0 = 
# 232 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( xs )
# 285 "smt_lang_parser.ml"
                 in
                
# 120 "smt_lang_parser.mly"
    ( (*Case 2*) Val_List(valu0) )
# 290 "smt_lang_parser.ml"
                 in
                _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_COMMA_tuple3_U_THREE_TWO_COLON_valu__ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Smt_lang_ast.u32 * unit * Smt_lang_ast.valu) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : ((Smt_lang_ast.u32 * unit * Smt_lang_ast.valu) list)) = _v in
        let ((_menhir_stack, _menhir_s, (x1 : (
# 89 "smt_lang_parser.mly"
       (int)
# 318 "smt_lang_parser.ml"
        ))), _, (x3 : (Smt_lang_ast.valu))) = _menhir_stack in
        let _2 = () in
        let x2 = () in
        let _v : ((Smt_lang_ast.u32 * unit * Smt_lang_ast.valu) list) = let x = 
# 51 "../../../../ott/menhir/menhir_library_extra.mly"
    ( (x1, x2, x3) )
# 325 "smt_lang_parser.ml"
         in
        
# 243 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x :: xs )
# 330 "smt_lang_parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_tuple3_U_THREE_TWO_COLON_valu__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : ((Smt_lang_ast.u32 * unit * Smt_lang_ast.valu) list)) = _v in
        let _v : ((Smt_lang_ast.u32 * unit * Smt_lang_ast.valu) list) = 
# 144 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x )
# 340 "smt_lang_parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_tuple3_U_THREE_TWO_COLON_valu___ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_COMMA_valu_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.valu list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (Smt_lang_ast.valu list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (Smt_lang_ast.valu))) = _menhir_stack in
        let _2 = () in
        let _v : (Smt_lang_ast.valu list) = 
# 243 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x :: xs )
# 358 "smt_lang_parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_valu_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState34 | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (Smt_lang_ast.valu list)) = _v in
        let _v : (Smt_lang_ast.valu list) = 
# 144 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x )
# 368 "smt_lang_parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_valu__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_def : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.def) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (def : (Smt_lang_ast.def))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.event) = 
# 240 "smt_lang_parser.mly"
    ( (*Case 2*) Smt(def) )
# 399 "smt_lang_parser.ml"
             in
            _menhir_goto_event _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (def : (Smt_lang_ast.def))) = _menhir_stack in
        let _v : (Smt_lang_ast.term) = 
# 252 "smt_lang_parser.mly"
    ( (*Case 2*) Def(def) )
# 415 "smt_lang_parser.ml"
         in
        _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_bool : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.bool) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (bool : (Smt_lang_ast.bool))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.valu) = 
# 110 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Bool(bool) )
# 441 "smt_lang_parser.ml"
             in
            _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState248 | MenhirState69 | MenhirState230 | MenhirState231 | MenhirState226 | MenhirState227 | MenhirState222 | MenhirState223 | MenhirState218 | MenhirState219 | MenhirState214 | MenhirState215 | MenhirState210 | MenhirState211 | MenhirState206 | MenhirState207 | MenhirState203 | MenhirState199 | MenhirState200 | MenhirState196 | MenhirState192 | MenhirState193 | MenhirState189 | MenhirState186 | MenhirState182 | MenhirState183 | MenhirState178 | MenhirState179 | MenhirState174 | MenhirState175 | MenhirState170 | MenhirState171 | MenhirState166 | MenhirState167 | MenhirState162 | MenhirState163 | MenhirState158 | MenhirState159 | MenhirState154 | MenhirState155 | MenhirState150 | MenhirState151 | MenhirState146 | MenhirState147 | MenhirState142 | MenhirState143 | MenhirState138 | MenhirState139 | MenhirState134 | MenhirState135 | MenhirState130 | MenhirState131 | MenhirState126 | MenhirState127 | MenhirState122 | MenhirState123 | MenhirState118 | MenhirState119 | MenhirState114 | MenhirState115 | MenhirState110 | MenhirState111 | MenhirState105 | MenhirState106 | MenhirState107 | MenhirState102 | MenhirState96 | MenhirState91 | MenhirState84 | MenhirState85 | MenhirState81 | MenhirState75 | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (bool : (Smt_lang_ast.bool))) = _menhir_stack in
        let _v : (Smt_lang_ast.exp) = 
# 146 "smt_lang_parser.mly"
    ( (*Case 2*) Bool(bool) )
# 457 "smt_lang_parser.ml"
         in
        _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_exp : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState77
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77)
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 154 "smt_lang_parser.mly"
    ( (*Case 2*) Or(exp,exp_prime) )
# 504 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 156 "smt_lang_parser.mly"
    ( (*Case 2*) Not(exp) )
# 529 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState85
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState85
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState85
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState85
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState85
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85)
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 150 "smt_lang_parser.mly"
    ( (*Case 2*) Neq(exp,exp_prime) )
# 575 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 596 "smt_lang_parser.ml"
            ))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 212 "smt_lang_parser.mly"
    ( (*Case 2*) ZeroExtend(u32,exp_prime) )
# 606 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 627 "smt_lang_parser.ml"
            ))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 214 "smt_lang_parser.mly"
    ( (*Case 2*) SignExtend(u32,exp_prime) )
# 637 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 658 "smt_lang_parser.ml"
            ))), (u32_prime : (
# 89 "smt_lang_parser.mly"
       (int)
# 662 "smt_lang_parser.ml"
            ))), _, (exp_prime_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 210 "smt_lang_parser.mly"
    ( (*Case 2*) Extract(u32,u32_prime,exp_prime_prime) )
# 672 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState106
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState106
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState106
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState106
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState106
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState106)
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107)
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))), _, (exp_prime_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 224 "smt_lang_parser.mly"
    ( (*Case 2*) Ite(exp,exp_prime,exp_prime_prime) )
# 739 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState111
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState111
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState111
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState111
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState111
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState111)
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 148 "smt_lang_parser.mly"
    ( (*Case 2*) Eq(exp,exp_prime) )
# 785 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState115
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState115
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState115
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState115
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState115
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115)
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 222 "smt_lang_parser.mly"
    ( (*Case 2*) Concat(exp,exp_prime) )
# 831 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState119
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState119
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState119
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState119
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState119
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState119)
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 168 "smt_lang_parser.mly"
    ( (*Case 2*) Bvxor(exp,exp_prime) )
# 877 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState123)
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 174 "smt_lang_parser.mly"
    ( (*Case 2*) Bvxnor(exp,exp_prime) )
# 923 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState126 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState127
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState127
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState127
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState127
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState127
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127)
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 188 "smt_lang_parser.mly"
    ( (*Case 2*) Bvurem(exp,exp_prime) )
# 969 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState131
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState131
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState131
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState131
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState131
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131)
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 194 "smt_lang_parser.mly"
    ( (*Case 2*) Bvult(exp,exp_prime) )
# 1015 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState135
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState135
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState135
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState135
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState135
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState135)
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 198 "smt_lang_parser.mly"
    ( (*Case 2*) Bvule(exp,exp_prime) )
# 1061 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState138 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState139
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState139
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState139
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState139
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState139
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139)
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 206 "smt_lang_parser.mly"
    ( (*Case 2*) Bvugt(exp,exp_prime) )
# 1107 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState143
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState143
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState143
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState143
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState143
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143)
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 202 "smt_lang_parser.mly"
    ( (*Case 2*) Bvuge(exp,exp_prime) )
# 1153 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState147
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState147
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState147
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState147
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState147
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState147)
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 184 "smt_lang_parser.mly"
    ( (*Case 2*) Bvudiv(exp,exp_prime) )
# 1199 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState151
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState151
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState151
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState151
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState151
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState151)
    | MenhirState151 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 180 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsub(exp,exp_prime) )
# 1245 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState155
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState155)
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 190 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsrem(exp,exp_prime) )
# 1291 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState158 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState159
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState159
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState159
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState159
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState159
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState159)
    | MenhirState159 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 192 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsmod(exp,exp_prime) )
# 1337 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState162 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState163
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState163
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState163
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState163
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState163
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState163)
    | MenhirState163 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 196 "smt_lang_parser.mly"
    ( (*Case 2*) Bvslt(exp,exp_prime) )
# 1383 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState167
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState167
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState167
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState167
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState167
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState167)
    | MenhirState167 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 200 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsle(exp,exp_prime) )
# 1429 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState170 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState171
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState171
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState171
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState171
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState171
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState171)
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 216 "smt_lang_parser.mly"
    ( (*Case 2*) Bvshl(exp,exp_prime) )
# 1475 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState174 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState175
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState175
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState175
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState175
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState175
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState175)
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 208 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsgt(exp,exp_prime) )
# 1521 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState178 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState179
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState179
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState179
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState179
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState179
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState179)
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 204 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsge(exp,exp_prime) )
# 1567 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState182 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState183
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState183
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState183
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState183
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState183
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState183)
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 186 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsdiv(exp,exp_prime) )
# 1613 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState186 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 162 "smt_lang_parser.mly"
    ( (*Case 2*) Bvredor(exp) )
# 1638 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState189 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 160 "smt_lang_parser.mly"
    ( (*Case 2*) Bvredand(exp) )
# 1663 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState192 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState193)
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 166 "smt_lang_parser.mly"
    ( (*Case 2*) Bvor(exp,exp_prime) )
# 1709 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState196 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 158 "smt_lang_parser.mly"
    ( (*Case 2*) Bvnot(exp) )
# 1734 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState199 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState200
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState200
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState200
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState200
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState200
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState200)
    | MenhirState200 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 172 "smt_lang_parser.mly"
    ( (*Case 2*) Bvnor(exp,exp_prime) )
# 1780 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState203 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 176 "smt_lang_parser.mly"
    ( (*Case 2*) Bvneg(exp) )
# 1805 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState206 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState207)
    | MenhirState207 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 170 "smt_lang_parser.mly"
    ( (*Case 2*) Bvnand(exp,exp_prime) )
# 1851 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState210 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState211
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState211
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState211
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState211
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState211
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState211)
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 182 "smt_lang_parser.mly"
    ( (*Case 2*) Bvmul(exp,exp_prime) )
# 1897 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState215
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState215
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState215
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState215
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState215
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState215)
    | MenhirState215 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 218 "smt_lang_parser.mly"
    ( (*Case 2*) Bvlshr(exp,exp_prime) )
# 1943 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState218 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState219)
    | MenhirState219 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 220 "smt_lang_parser.mly"
    ( (*Case 2*) Bvashr(exp,exp_prime) )
# 1989 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState223)
    | MenhirState223 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 164 "smt_lang_parser.mly"
    ( (*Case 2*) Bvand(exp,exp_prime) )
# 2035 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState226 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState227
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState227
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState227
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState227
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState227
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState227)
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 178 "smt_lang_parser.mly"
    ( (*Case 2*) Bvadd(exp,exp_prime) )
# 2081 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState231 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState231)
    | MenhirState231 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 152 "smt_lang_parser.mly"
    ( (*Case 2*) And(exp,exp_prime) )
# 2127 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 2148 "smt_lang_parser.ml"
            ))), _, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.def) = 
# 230 "smt_lang_parser.mly"
    ( (*Case 2*) DefineConst(u32,exp) )
# 2157 "smt_lang_parser.ml"
             in
            _menhir_goto_def _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState248 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.def) = 
# 232 "smt_lang_parser.mly"
    ( (*Case 2*) Assert(exp) )
# 2182 "smt_lang_parser.ml"
             in
            _menhir_goto_def _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_COMMA_tuple3_U_THREE_TWO_COLON_valu___ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Smt_lang_ast.u32 * unit * Smt_lang_ast.valu) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (xs : ((Smt_lang_ast.u32 * unit * Smt_lang_ast.valu) list))) = _menhir_stack in
            let _6 = () in
            let _5 = () in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.valu) = let u320_valu0 = 
# 232 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( xs )
# 2219 "smt_lang_parser.ml"
             in
            
# 122 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Struct(List.map (function (u320,(),valu0) -> (u320,valu0)) u320_valu0) )
# 2224 "smt_lang_parser.ml"
             in
            _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 89 "smt_lang_parser.mly"
       (int)
# 2243 "smt_lang_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COLON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | BV ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | LPAREN_UNDERSCORE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | S ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | STRUCT ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | VU_THREE_TWO _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce59 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smt_lang_ast.valu list) = 
# 142 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [] )
# 2283 "smt_lang_parser.ml"
     in
    _menhir_goto_loption_separated_nonempty_list_COMMA_valu__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_valu : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.valu) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState34 | MenhirState23 | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | BV ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | LPAREN_UNDERSCORE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | S ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | STRUCT ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | VU_THREE_TWO _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23)
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (Smt_lang_ast.valu))) = _menhir_stack in
            let _v : (Smt_lang_ast.valu list) = 
# 241 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [ x ] )
# 2323 "smt_lang_parser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_valu_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | U_THREE_TWO _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42)
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (x1 : (
# 89 "smt_lang_parser.mly"
       (int)
# 2353 "smt_lang_parser.ml"
            ))), _, (x3 : (Smt_lang_ast.valu))) = _menhir_stack in
            let x2 = () in
            let _v : ((Smt_lang_ast.u32 * unit * Smt_lang_ast.valu) list) = let x = 
# 51 "../../../../ott/menhir/menhir_library_extra.mly"
    ( (x1, x2, x3) )
# 2359 "smt_lang_parser.ml"
             in
            
# 241 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [ x ] )
# 2364 "smt_lang_parser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_tuple3_U_THREE_TWO_COLON_valu__ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 2385 "smt_lang_parser.ml"
            ))), _, (valu : (Smt_lang_ast.valu))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.event) = 
# 244 "smt_lang_parser.mly"
    ( (*Case 2*) WriteReg(u32,valu) )
# 2394 "smt_lang_parser.ml"
             in
            _menhir_goto_event _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState267 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 2415 "smt_lang_parser.ml"
            ))), _, (xs : (Smt_lang_ast.accessor list))), _, (valu : (Smt_lang_ast.valu))) = _menhir_stack in
            let _10 = () in
            let _8 = () in
            let _7 = () in
            let _5 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.event) = let accessor0 = 
# 232 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( xs )
# 2427 "smt_lang_parser.ml"
             in
            
# 242 "smt_lang_parser.mly"
    ( (*Case 2*) ReadReg(u32,accessor0,valu) )
# 2432 "smt_lang_parser.ml"
             in
            _menhir_goto_event _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_COMMA_accessor_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.accessor list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState257 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (Smt_lang_ast.accessor list)) = _v in
        let _v : (Smt_lang_ast.accessor list) = 
# 144 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x )
# 2454 "smt_lang_parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_accessor__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState271 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (Smt_lang_ast.accessor list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (Smt_lang_ast.accessor))) = _menhir_stack in
        let _2 = () in
        let _v : (Smt_lang_ast.accessor list) = 
# 243 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x :: xs )
# 2466 "smt_lang_parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_accessor_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_term : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.term) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EOF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (term : (Smt_lang_ast.term))) = _menhir_stack in
        let _2 = () in
        let _v : (
# 93 "smt_lang_parser.mly"
       (Smt_lang_ast.term)
# 2487 "smt_lang_parser.ml"
        ) = 
# 100 "smt_lang_parser.mly"
    ( term )
# 2491 "smt_lang_parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_1 : (
# 93 "smt_lang_parser.mly"
       (Smt_lang_ast.term)
# 2498 "smt_lang_parser.ml"
        )) = _v in
        Obj.magic _1
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_ty : _menhir_env -> 'ttv_tail -> (Smt_lang_ast.ty) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 2522 "smt_lang_parser.ml"
        ))), (ty : (Smt_lang_ast.ty))) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Smt_lang_ast.def) = 
# 228 "smt_lang_parser.mly"
    ( (*Case 2*) DeclareConst(u32,ty) )
# 2531 "smt_lang_parser.ml"
         in
        _menhir_goto_def _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run70 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 88 "smt_lang_parser.mly"
       (string)
# 2544 "smt_lang_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (vu32 : (
# 88 "smt_lang_parser.mly"
       (string)
# 2552 "smt_lang_parser.ml"
    )) = _v in
    let _v : (Smt_lang_ast.exp) = 
# 140 "smt_lang_parser.mly"
    ( (*Case 2*) Var(vu32) )
# 2557 "smt_lang_parser.ml"
     in
    _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Smt_lang_ast.bool) = 
# 134 "smt_lang_parser.mly"
    ( (*Case 2*) True )
# 2569 "smt_lang_parser.ml"
     in
    _menhir_goto_bool _menhir_env _menhir_stack _menhir_s _v

and _menhir_run71 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | U_SIX_FOUR _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | U_THREE_TWO _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 2592 "smt_lang_parser.ml"
            )) = _v in
            let ((_menhir_stack, _menhir_s), (u64 : (
# 90 "smt_lang_parser.mly"
       (string)
# 2597 "smt_lang_parser.ml"
            ))) = _menhir_stack in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 144 "smt_lang_parser.mly"
    ( (*Case 2*) Bits64(u64,u32) )
# 2603 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run74 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AND ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState230
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState230
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState230
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState230
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState230
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState230 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState230)
    | BVADD ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState226
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState226
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState226
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState226
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState226
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState226 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState226)
    | BVAND ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState222
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState222
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState222
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState222
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState222
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState222)
    | BVASHR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState218
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState218
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState218
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState218
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState218
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState218 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState218)
    | BVLSHR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState214
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState214
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState214
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState214
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState214
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState214)
    | BVMUL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState210 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState210)
    | BVNAND ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState206
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState206
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState206
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState206
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState206
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState206)
    | BVNEG ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState203
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState203
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState203
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState203
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState203
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState203)
    | BVNOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState199
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState199
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState199
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState199
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState199
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState199)
    | BVNOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState196
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState196
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState196
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState196
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState196
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState196 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState196)
    | BVOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState192)
    | BVREDAND ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState189)
    | BVREDOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState186
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState186
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState186
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState186
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState186
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState186)
    | BVSDIV ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState182
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState182
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState182
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState182
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState182
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState182 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState182)
    | BVSGE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState178
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState178
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState178
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState178
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState178
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState178 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState178)
    | BVSGT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState174
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState174
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState174
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState174
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState174
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState174)
    | BVSHL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState170
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState170
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState170
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState170
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState170
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState170)
    | BVSLE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState166
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState166
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState166
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState166
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState166
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState166)
    | BVSLT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState162
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState162
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState162
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState162
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState162
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState162)
    | BVSMOD ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState158
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState158
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState158
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState158
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState158
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState158)
    | BVSREM ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState154
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState154
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState154
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState154
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState154
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState154)
    | BVSUB ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState150
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState150
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState150
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState150
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState150
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150)
    | BVUDIV ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState146
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState146
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState146
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState146
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState146
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState146)
    | BVUGE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState142
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState142 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState142)
    | BVUGT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState138
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState138
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState138
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState138
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState138
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState138)
    | BVULE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState134
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState134
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState134
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState134
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState134
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState134 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState134)
    | BVULT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130)
    | BVUREM ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState126
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState126
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState126
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState126
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState126
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState126 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState126)
    | BVXNOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState122
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState122
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState122
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState122
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState122
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122)
    | BVXOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState118
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState118
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState118
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState118
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState118
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState118)
    | CONCAT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState114
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState114
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState114
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState114
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState114
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114)
    | EQ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110)
    | ITE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState105
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState105
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState105
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState105
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState105
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105)
    | LPAREN_UNDERSCORE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EXTRACT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | U_THREE_TWO _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | U_THREE_TWO _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = (_menhir_stack, _v) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | RPAREN ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | BV ->
                            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                        | FALSE ->
                            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                        | LPAREN ->
                            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                        | QUESTIONMARK ->
                            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                        | TRUE ->
                            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                        | VU_THREE_TWO _v ->
                            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | SIGNEXTEND ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | U_THREE_TWO _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | RPAREN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | BV ->
                        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState96
                    | FALSE ->
                        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState96
                    | LPAREN ->
                        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState96
                    | QUESTIONMARK ->
                        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState96
                    | TRUE ->
                        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState96
                    | VU_THREE_TWO _v ->
                        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | ZEROEXTEND ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | U_THREE_TWO _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | RPAREN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | BV ->
                        _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                    | FALSE ->
                        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                    | LPAREN ->
                        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                    | QUESTIONMARK ->
                        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                    | TRUE ->
                        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState91
                    | VU_THREE_TWO _v ->
                        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | NEQ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84)
    | NOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState81
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState81
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState81
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState81
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState81
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81)
    | OR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run19 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Smt_lang_ast.bool) = 
# 136 "smt_lang_parser.mly"
    ( (*Case 2*) False )
# 3551 "smt_lang_parser.ml"
     in
    _menhir_goto_bool _menhir_env _menhir_stack _menhir_s _v

and _menhir_run76 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Smt_lang_ast.exp) = 
# 142 "smt_lang_parser.mly"
    ( (*Case 2*) Bits )
# 3563 "smt_lang_parser.ml"
     in
    _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 88 "smt_lang_parser.mly"
       (string)
# 3570 "smt_lang_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (vu32 : (
# 88 "smt_lang_parser.mly"
       (string)
# 3578 "smt_lang_parser.ml"
    )) = _v in
    let _v : (Smt_lang_ast.valu) = 
# 104 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Symbolic(vu32) )
# 3583 "smt_lang_parser.ml"
     in
    _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | U_THREE_TWO _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
            | RBRACE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState8 in
                let _v : ((Smt_lang_ast.u32 * unit * Smt_lang_ast.valu) list) = 
# 142 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [] )
# 3611 "smt_lang_parser.ml"
                 in
                _menhir_goto_loption_separated_nonempty_list_COMMA_tuple3_U_THREE_TWO_COLON_valu___ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Smt_lang_ast.valu) = 
# 114 "smt_lang_parser.mly"
    ( (*Case 2*) Val_String )
# 3639 "smt_lang_parser.ml"
     in
    _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v

and _menhir_run12 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BVI_ONE_TWO_EIGHT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Smt_lang_ast.valu) = 
# 108 "smt_lang_parser.mly"
    ( (*Case 2*) Val_I128 )
# 3659 "smt_lang_parser.ml"
         in
        _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
    | BVI_SIX_FOUR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.valu) = 
# 106 "smt_lang_parser.mly"
    ( (*Case 2*) Val_I64 )
# 3678 "smt_lang_parser.ml"
             in
            _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | LIST ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState34
            | BV ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState34
            | LPAREN_UNDERSCORE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState34
            | S ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState34
            | STRUCT ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState34
            | VU_THREE_TWO _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
            | RBRACE ->
                _menhir_reduce59 _menhir_env (Obj.magic _menhir_stack) MenhirState34
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | POISON ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.valu) = 
# 124 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Poison )
# 3737 "smt_lang_parser.ml"
             in
            _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | UNIT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.valu) = 
# 116 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Unit )
# 3762 "smt_lang_parser.ml"
             in
            _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | VEC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState14
            | BV ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState14
            | LPAREN_UNDERSCORE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState14
            | S ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState14
            | STRUCT ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState14
            | VU_THREE_TWO _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState14 _v
            | RBRACE ->
                _menhir_reduce59 _menhir_env (Obj.magic _menhir_stack) MenhirState14
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Smt_lang_ast.valu) = 
# 112 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Bits )
# 3820 "smt_lang_parser.ml"
     in
    _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v

and _menhir_run16 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState17
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_loption_separated_nonempty_list_COMMA_accessor__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.accessor list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RBRACK ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState267
            | BV ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState267
            | LPAREN_UNDERSCORE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState267
            | S ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState267
            | STRUCT ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState267
            | VU_THREE_TWO _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState267 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState267)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run258 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FIELD ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | FIELD_UNDERSCORE_NAME ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BAR ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | RPAREN ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let (_menhir_stack, _menhir_s) = _menhir_stack in
                        let _6 = () in
                        let _5 = () in
                        let _4 = () in
                        let _3 = () in
                        let _2 = () in
                        let _1 = () in
                        let _v : (Smt_lang_ast.accessor) = 
# 236 "smt_lang_parser.mly"
    ( (*Case 2*) Field )
# 3936 "smt_lang_parser.ml"
                         in
                        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                        let _menhir_stack = Obj.magic _menhir_stack in
                        assert (not _menhir_env._menhir_error);
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | COMMA ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _menhir_env = _menhir_discard _menhir_env in
                            let _tok = _menhir_env._menhir_token in
                            (match _tok with
                            | LPAREN_UNDERSCORE ->
                                _menhir_run258 _menhir_env (Obj.magic _menhir_stack) MenhirState271
                            | _ ->
                                assert (not _menhir_env._menhir_error);
                                _menhir_env._menhir_error <- true;
                                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState271)
                        | RBRACK ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let (_menhir_stack, _menhir_s, (x : (Smt_lang_ast.accessor))) = _menhir_stack in
                            let _v : (Smt_lang_ast.accessor list) = 
# 241 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [ x ] )
# 3960 "smt_lang_parser.ml"
                             in
                            _menhir_goto_separated_nonempty_list_COMMA_accessor_ _menhir_env _menhir_stack _menhir_s _v
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let (_menhir_stack, _menhir_s) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState271 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState267 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState257 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState248 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState231 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState226 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState223 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState219 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState218 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState215 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState210 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState207 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState206 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState203 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState200 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState199 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState196 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState192 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState189 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState186 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState182 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState178 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState174 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState170 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState167 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState163 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState162 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState159 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState158 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState151 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState138 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState126 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_goto_event : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.event) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (event : (Smt_lang_ast.event)) = _v in
    let _v : (Smt_lang_ast.term) = 
# 254 "smt_lang_parser.mly"
    ( (*Case 2*) Event(event) )
# 4355 "smt_lang_parser.ml"
     in
    _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v

and _menhir_run66 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | U_THREE_TWO _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BV ->
                    _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState69
                | FALSE ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState69
                | LPAREN ->
                    _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState69
                | QUESTIONMARK ->
                    _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState69
                | TRUE ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState69
                | VU_THREE_TWO _v ->
                    _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run236 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | U_THREE_TWO _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BITVEC ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | LPAREN ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | U_THREE_TWO _v ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _menhir_stack = (_menhir_stack, _v) in
                            let _menhir_env = _menhir_discard _menhir_env in
                            let _tok = _menhir_env._menhir_token in
                            (match _tok with
                            | RPAREN ->
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let _menhir_env = _menhir_discard _menhir_env in
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let (_menhir_stack, (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 4461 "smt_lang_parser.ml"
                                ))) = _menhir_stack in
                                let _4 = () in
                                let _2 = () in
                                let _1 = () in
                                let _v : (Smt_lang_ast.ty) = 
# 130 "smt_lang_parser.mly"
    ( (*Case 2*) Ty_BitVec(u32) )
# 4469 "smt_lang_parser.ml"
                                 in
                                _menhir_goto_ty _menhir_env _menhir_stack _v
                            | _ ->
                                assert (not _menhir_env._menhir_error);
                                _menhir_env._menhir_error <- true;
                                let _menhir_stack = Obj.magic _menhir_stack in
                                raise _eRR)
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            let _menhir_stack = Obj.magic _menhir_stack in
                            raise _eRR)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        raise _eRR)
                | BOOL ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _1 = () in
                    let _v : (Smt_lang_ast.ty) = 
# 128 "smt_lang_parser.mly"
    ( (*Case 2*) Ty_Bool )
# 4495 "smt_lang_parser.ml"
                     in
                    _menhir_goto_ty _menhir_env _menhir_stack _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run247 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV ->
            _menhir_run76 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | FALSE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | LPAREN ->
            _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | QUESTIONMARK ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | TRUE ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | VU_THREE_TWO _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState248 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState248)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and term_start : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 93 "smt_lang_parser.mly"
       (Smt_lang_ast.term)
# 4572 "smt_lang_parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = let _tok = Obj.magic () in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASSERT ->
        _menhir_run247 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | DECLARECONST ->
        _menhir_run236 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | DEFINECONST ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | READMEM ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | VALUUE_COLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | U_THREE_TWO _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = (_menhir_stack, _v) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | COMMA ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | READ_UNDERSCORE_KIND_COLON ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _menhir_env = _menhir_discard _menhir_env in
                            let _tok = _menhir_env._menhir_token in
                            (match _tok with
                            | VALU_COMMA ->
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let _menhir_env = _menhir_discard _menhir_env in
                                let _tok = _menhir_env._menhir_token in
                                (match _tok with
                                | ADDRESS_COLON ->
                                    let _menhir_stack = Obj.magic _menhir_stack in
                                    let _menhir_env = _menhir_discard _menhir_env in
                                    let _tok = _menhir_env._menhir_token in
                                    (match _tok with
                                    | VALU_APOSTROPHE_COMMA ->
                                        let _menhir_stack = Obj.magic _menhir_stack in
                                        let _menhir_env = _menhir_discard _menhir_env in
                                        let _tok = _menhir_env._menhir_token in
                                        (match _tok with
                                        | BYTES_COLON ->
                                            let _menhir_stack = Obj.magic _menhir_stack in
                                            let _menhir_env = _menhir_discard _menhir_env in
                                            let _tok = _menhir_env._menhir_token in
                                            (match _tok with
                                            | U_THREE_TWO _v ->
                                                let _menhir_stack = Obj.magic _menhir_stack in
                                                let _menhir_stack = (_menhir_stack, _v) in
                                                let _menhir_env = _menhir_discard _menhir_env in
                                                let _tok = _menhir_env._menhir_token in
                                                (match _tok with
                                                | RBRACE ->
                                                    let _menhir_stack = Obj.magic _menhir_stack in
                                                    let _menhir_env = _menhir_discard _menhir_env in
                                                    let _menhir_stack = Obj.magic _menhir_stack in
                                                    let (((_menhir_stack, _menhir_s), (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 4658 "smt_lang_parser.ml"
                                                    ))), (u32_prime : (
# 89 "smt_lang_parser.mly"
       (int)
# 4662 "smt_lang_parser.ml"
                                                    ))) = _menhir_stack in
                                                    let _12 = () in
                                                    let _10 = () in
                                                    let _9 = () in
                                                    let _8 = () in
                                                    let _7 = () in
                                                    let _6 = () in
                                                    let _5 = () in
                                                    let _3 = () in
                                                    let _2 = () in
                                                    let _1 = () in
                                                    let _v : (Smt_lang_ast.event) = 
# 246 "smt_lang_parser.mly"
    ( (*Case 2*) ReadMem(u32,u32_prime) )
# 4677 "smt_lang_parser.ml"
                                                     in
                                                    _menhir_goto_event _menhir_env _menhir_stack _menhir_s _v
                                                | _ ->
                                                    assert (not _menhir_env._menhir_error);
                                                    _menhir_env._menhir_error <- true;
                                                    let _menhir_stack = Obj.magic _menhir_stack in
                                                    let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                                                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                            | _ ->
                                                assert (not _menhir_env._menhir_error);
                                                _menhir_env._menhir_error <- true;
                                                let _menhir_stack = Obj.magic _menhir_stack in
                                                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                        | _ ->
                                            assert (not _menhir_env._menhir_error);
                                            _menhir_env._menhir_error <- true;
                                            let _menhir_stack = Obj.magic _menhir_stack in
                                            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                    | _ ->
                                        assert (not _menhir_env._menhir_error);
                                        _menhir_env._menhir_error <- true;
                                        let _menhir_stack = Obj.magic _menhir_stack in
                                        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                | _ ->
                                    assert (not _menhir_env._menhir_error);
                                    _menhir_env._menhir_error <- true;
                                    let _menhir_stack = Obj.magic _menhir_stack in
                                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                            | _ ->
                                assert (not _menhir_env._menhir_error);
                                _menhir_env._menhir_error <- true;
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | READREG ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | U_THREE_TWO _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | COMMA ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | LBRACK ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | LPAREN_UNDERSCORE ->
                            _menhir_run258 _menhir_env (Obj.magic _menhir_stack) MenhirState257
                        | RBRACK ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _menhir_s = MenhirState257 in
                            let _v : (Smt_lang_ast.accessor list) = 
# 142 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [] )
# 4782 "smt_lang_parser.ml"
                             in
                            _menhir_goto_loption_separated_nonempty_list_COMMA_accessor__ _menhir_env _menhir_stack _menhir_s _v
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState257)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | SMT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASSERT ->
                _menhir_run247 _menhir_env (Obj.magic _menhir_stack) MenhirState65
            | DECLARECONST ->
                _menhir_run236 _menhir_env (Obj.magic _menhir_stack) MenhirState65
            | DEFINECONST ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState65
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | WRITEMEM ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | VALUUE_COLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | U_THREE_TWO _v ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_stack = (_menhir_stack, _v) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | COMMA ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | WRITE_UNDERSCORE_KIND_COLON ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _menhir_env = _menhir_discard _menhir_env in
                            let _tok = _menhir_env._menhir_token in
                            (match _tok with
                            | VALU_COMMA ->
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let _menhir_env = _menhir_discard _menhir_env in
                                let _tok = _menhir_env._menhir_token in
                                (match _tok with
                                | ADDRESS_COLON ->
                                    let _menhir_stack = Obj.magic _menhir_stack in
                                    let _menhir_env = _menhir_discard _menhir_env in
                                    let _tok = _menhir_env._menhir_token in
                                    (match _tok with
                                    | VALU_APOSTROPHE_COMMA ->
                                        let _menhir_stack = Obj.magic _menhir_stack in
                                        let _menhir_env = _menhir_discard _menhir_env in
                                        let _tok = _menhir_env._menhir_token in
                                        (match _tok with
                                        | DATA_COLON ->
                                            let _menhir_stack = Obj.magic _menhir_stack in
                                            let _menhir_env = _menhir_discard _menhir_env in
                                            let _tok = _menhir_env._menhir_token in
                                            (match _tok with
                                            | VALU_APOSTROPHE_APOSTROPHE_COMMA ->
                                                let _menhir_stack = Obj.magic _menhir_stack in
                                                let _menhir_env = _menhir_discard _menhir_env in
                                                let _tok = _menhir_env._menhir_token in
                                                (match _tok with
                                                | BYTES_COLON ->
                                                    let _menhir_stack = Obj.magic _menhir_stack in
                                                    let _menhir_env = _menhir_discard _menhir_env in
                                                    let _tok = _menhir_env._menhir_token in
                                                    (match _tok with
                                                    | U_THREE_TWO _v ->
                                                        let _menhir_stack = Obj.magic _menhir_stack in
                                                        let _menhir_stack = (_menhir_stack, _v) in
                                                        let _menhir_env = _menhir_discard _menhir_env in
                                                        let _tok = _menhir_env._menhir_token in
                                                        (match _tok with
                                                        | RBRACE ->
                                                            let _menhir_stack = Obj.magic _menhir_stack in
                                                            let _menhir_env = _menhir_discard _menhir_env in
                                                            let _menhir_stack = Obj.magic _menhir_stack in
                                                            let (((_menhir_stack, _menhir_s), (u32 : (
# 89 "smt_lang_parser.mly"
       (int)
# 4917 "smt_lang_parser.ml"
                                                            ))), (u32_prime : (
# 89 "smt_lang_parser.mly"
       (int)
# 4921 "smt_lang_parser.ml"
                                                            ))) = _menhir_stack in
                                                            let _14 = () in
                                                            let _12 = () in
                                                            let _11 = () in
                                                            let _10 = () in
                                                            let _9 = () in
                                                            let _8 = () in
                                                            let _7 = () in
                                                            let _6 = () in
                                                            let _5 = () in
                                                            let _3 = () in
                                                            let _2 = () in
                                                            let _1 = () in
                                                            let _v : (Smt_lang_ast.event) = 
# 248 "smt_lang_parser.mly"
    ( (*Case 2*) WriteMem(u32,u32_prime) )
# 4938 "smt_lang_parser.ml"
                                                             in
                                                            _menhir_goto_event _menhir_env _menhir_stack _menhir_s _v
                                                        | _ ->
                                                            assert (not _menhir_env._menhir_error);
                                                            _menhir_env._menhir_error <- true;
                                                            let _menhir_stack = Obj.magic _menhir_stack in
                                                            let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                                                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                                    | _ ->
                                                        assert (not _menhir_env._menhir_error);
                                                        _menhir_env._menhir_error <- true;
                                                        let _menhir_stack = Obj.magic _menhir_stack in
                                                        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                                | _ ->
                                                    assert (not _menhir_env._menhir_error);
                                                    _menhir_env._menhir_error <- true;
                                                    let _menhir_stack = Obj.magic _menhir_stack in
                                                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                            | _ ->
                                                assert (not _menhir_env._menhir_error);
                                                _menhir_env._menhir_error <- true;
                                                let _menhir_stack = Obj.magic _menhir_stack in
                                                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                        | _ ->
                                            assert (not _menhir_env._menhir_error);
                                            _menhir_env._menhir_error <- true;
                                            let _menhir_stack = Obj.magic _menhir_stack in
                                            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                    | _ ->
                                        assert (not _menhir_env._menhir_error);
                                        _menhir_env._menhir_error <- true;
                                        let _menhir_stack = Obj.magic _menhir_stack in
                                        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                                | _ ->
                                    assert (not _menhir_env._menhir_error);
                                    _menhir_env._menhir_error <- true;
                                    let _menhir_stack = Obj.magic _menhir_stack in
                                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                            | _ ->
                                assert (not _menhir_env._menhir_error);
                                _menhir_env._menhir_error <- true;
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | WRITEREG ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | U_THREE_TWO _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | COMMA ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | BOOL ->
                        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                    | BV ->
                        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                    | LPAREN_UNDERSCORE ->
                        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                    | S ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                    | STRUCT ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                    | VU_THREE_TWO _v ->
                        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState4)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

# 70 "../../../../ott/menhir/menhir_library_extra.mly"
  




# 5087 "smt_lang_parser.ml"

# 269 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
  

# 5092 "smt_lang_parser.ml"
