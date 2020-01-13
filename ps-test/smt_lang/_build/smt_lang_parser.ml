
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | ZERO_UNDERSCORE_EXTEND
    | WRITE_MINUS_REG
    | VU_THREE_TWO of (
# 72 "smt_lang_parser.mly"
       (string)
# 13 "smt_lang_parser.ml"
  )
    | VEC
    | U_THREE_TWO of (
# 73 "smt_lang_parser.mly"
       (int)
# 19 "smt_lang_parser.ml"
  )
    | U_SIX_FOUR of (
# 74 "smt_lang_parser.mly"
       (string)
# 24 "smt_lang_parser.ml"
  )
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
    | NAME of (
# 75 "smt_lang_parser.mly"
       (string)
# 44 "smt_lang_parser.ml"
  )
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
    | BVI of (
# 76 "smt_lang_parser.mly"
       (string)
# 91 "smt_lang_parser.ml"
  )
    | BVASHR
    | BVAND
    | BVADD
    | BV of (
# 77 "smt_lang_parser.mly"
       (string)
# 99 "smt_lang_parser.ml"
  )
    | BOOL
    | BITVEC
    | ASSERT
    | AND
  
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
  | MenhirState251
  | MenhirState249
  | MenhirState245
  | MenhirState239
  | MenhirState225
  | MenhirState224
  | MenhirState221
  | MenhirState220
  | MenhirState217
  | MenhirState216
  | MenhirState213
  | MenhirState212
  | MenhirState209
  | MenhirState208
  | MenhirState205
  | MenhirState204
  | MenhirState201
  | MenhirState200
  | MenhirState197
  | MenhirState194
  | MenhirState193
  | MenhirState190
  | MenhirState187
  | MenhirState186
  | MenhirState183
  | MenhirState180
  | MenhirState177
  | MenhirState176
  | MenhirState173
  | MenhirState172
  | MenhirState169
  | MenhirState168
  | MenhirState165
  | MenhirState164
  | MenhirState161
  | MenhirState160
  | MenhirState157
  | MenhirState156
  | MenhirState153
  | MenhirState152
  | MenhirState149
  | MenhirState148
  | MenhirState145
  | MenhirState144
  | MenhirState141
  | MenhirState140
  | MenhirState137
  | MenhirState136
  | MenhirState133
  | MenhirState132
  | MenhirState129
  | MenhirState128
  | MenhirState125
  | MenhirState124
  | MenhirState121
  | MenhirState120
  | MenhirState117
  | MenhirState116
  | MenhirState113
  | MenhirState112
  | MenhirState109
  | MenhirState108
  | MenhirState105
  | MenhirState104
  | MenhirState101
  | MenhirState100
  | MenhirState99
  | MenhirState96
  | MenhirState90
  | MenhirState85
  | MenhirState79
  | MenhirState78
  | MenhirState75
  | MenhirState71
  | MenhirState69
  | MenhirState66
  | MenhirState63
  | MenhirState60
  | MenhirState58
  | MenhirState51
  | MenhirState37
  | MenhirState30
  | MenhirState27
  | MenhirState25
  | MenhirState17
  | MenhirState11
  | MenhirState8
  | MenhirState3
  | MenhirState0

# 2 "smt_lang_parser.mly"
  
open Smt_lang_ast

# 215 "smt_lang_parser.ml"

let rec _menhir_goto_list_struct_element_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.struct_element list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smt_lang_ast.struct_element))), _, (xs : (Smt_lang_ast.struct_element list))) = _menhir_stack in
        let _v : (Smt_lang_ast.struct_element list) = 
# 213 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x :: xs )
# 228 "smt_lang_parser.ml"
         in
        _menhir_goto_list_struct_element_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (struct_element0 : (Smt_lang_ast.struct_element list))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.valu) = 
# 109 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Struct(struct_element0) )
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
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_COMMA_valu__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.valu list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState8 ->
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
# 232 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( xs )
# 286 "smt_lang_parser.ml"
                 in
                
# 105 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Vector(valu0) )
# 291 "smt_lang_parser.ml"
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
    | MenhirState37 ->
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
# 232 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( xs )
# 329 "smt_lang_parser.ml"
                 in
                
# 107 "smt_lang_parser.mly"
    ( (*Case 2*) Val_List(valu0) )
# 334 "smt_lang_parser.ml"
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

and _menhir_goto_event : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.event) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState249 | MenhirState245 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run246 _menhir_env (Obj.magic _menhir_stack) MenhirState249
        | RPAREN ->
            _menhir_reduce57 _menhir_env (Obj.magic _menhir_stack) MenhirState249
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState249)
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (event : (Smt_lang_ast.event))) = _menhir_stack in
        let _v : (Smt_lang_ast.term) = 
# 243 "smt_lang_parser.mly"
    ( (*Case 2*) Event(event) )
# 376 "smt_lang_parser.ml"
         in
        _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_COMMA_valu_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.valu list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (Smt_lang_ast.valu list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (Smt_lang_ast.valu))) = _menhir_stack in
        let _2 = () in
        let _v : (Smt_lang_ast.valu list) = 
# 243 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x :: xs )
# 394 "smt_lang_parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_valu_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState37 | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (Smt_lang_ast.valu list)) = _v in
        let _v : (Smt_lang_ast.valu list) = 
# 144 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x )
# 404 "smt_lang_parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_valu__ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_event_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.event list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState245 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (def0 : (Smt_lang_ast.def list))), _, (event0 : (Smt_lang_ast.event list))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _5 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.term) = 
# 245 "smt_lang_parser.mly"
    ( (*Case 2*) Top(def0,event0) )
# 433 "smt_lang_parser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState249 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smt_lang_ast.event))), _, (xs : (Smt_lang_ast.event list))) = _menhir_stack in
        let _v : (Smt_lang_ast.event list) = 
# 213 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x :: xs )
# 449 "smt_lang_parser.ml"
         in
        _menhir_goto_list_event_ _menhir_env _menhir_stack _menhir_s _v
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
# 80 "smt_lang_parser.mly"
       (Smt_lang_ast.term)
# 470 "smt_lang_parser.ml"
        ) = 
# 87 "smt_lang_parser.mly"
    ( term )
# 474 "smt_lang_parser.ml"
         in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_1 : (
# 80 "smt_lang_parser.mly"
       (Smt_lang_ast.term)
# 481 "smt_lang_parser.ml"
        )) = _v in
        Obj.magic _1
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce59 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smt_lang_ast.struct_element list) = 
# 211 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [] )
# 496 "smt_lang_parser.ml"
     in
    _menhir_goto_list_struct_element_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run26 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | NAME _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState27
        | BV _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
        | LPAREN_UNDERSCORE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState27
        | S ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState27
        | VU_THREE_TWO _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce61 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smt_lang_ast.valu list) = 
# 142 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [] )
# 538 "smt_lang_parser.ml"
     in
    _menhir_goto_loption_separated_nonempty_list_COMMA_valu__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_valu : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.valu) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState37 | MenhirState17 | MenhirState8 ->
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
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState17
            | BV _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
            | LPAREN_UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState17
            | S ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState17
            | VU_THREE_TWO _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17)
        | RBRACE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (Smt_lang_ast.valu))) = _menhir_stack in
            let _v : (Smt_lang_ast.valu list) = 
# 241 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [ x ] )
# 576 "smt_lang_parser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_valu_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (name : (
# 75 "smt_lang_parser.mly"
       (string)
# 597 "smt_lang_parser.ml"
            ))), _, (valu : (Smt_lang_ast.valu))) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.struct_element) = 
# 115 "smt_lang_parser.mly"
    ( (*Case 2*) Struct_elem(name,valu) )
# 604 "smt_lang_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LPAREN ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState30
            | RPAREN ->
                _menhir_reduce59 _menhir_env (Obj.magic _menhir_stack) MenhirState30
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState30)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (name : (
# 75 "smt_lang_parser.mly"
       (string)
# 637 "smt_lang_parser.ml"
            ))), _, (valu : (Smt_lang_ast.valu))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.event) = 
# 237 "smt_lang_parser.mly"
    ( (*Case 2*) WriteReg(name,valu) )
# 645 "smt_lang_parser.ml"
             in
            _menhir_goto_event _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState60 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), (name : (
# 75 "smt_lang_parser.mly"
       (string)
# 666 "smt_lang_parser.ml"
            ))), (accessor_list : (Smt_lang_ast.accessor_list))), _, (valu : (Smt_lang_ast.valu))) = _menhir_stack in
            let _6 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.event) = 
# 235 "smt_lang_parser.mly"
    ( (*Case 2*) ReadReg(name,accessor_list,valu) )
# 674 "smt_lang_parser.ml"
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

and _menhir_goto_list_accessor_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.accessor list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, (accessor0 : (Smt_lang_ast.accessor list))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.accessor_list) = 
# 231 "smt_lang_parser.mly"
    ( (*Case 2*) Cons(accessor0) )
# 705 "smt_lang_parser.ml"
             in
            _menhir_goto_accessor_list _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smt_lang_ast.accessor))), _, (xs : (Smt_lang_ast.accessor list))) = _menhir_stack in
        let _v : (Smt_lang_ast.accessor list) = 
# 213 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x :: xs )
# 721 "smt_lang_parser.ml"
         in
        _menhir_goto_list_accessor_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_reduce57 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smt_lang_ast.event list) = 
# 211 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [] )
# 737 "smt_lang_parser.ml"
     in
    _menhir_goto_list_event_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run246 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | READ_MINUS_REG ->
        _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
    | WRITE_MINUS_REG ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_def : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.def) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState251 | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | RPAREN ->
            _menhir_reduce55 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState251)
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (def : (Smt_lang_ast.def))) = _menhir_stack in
        let _v : (Smt_lang_ast.term) = 
# 241 "smt_lang_parser.mly"
    ( (*Case 2*) Def(def) )
# 782 "smt_lang_parser.ml"
         in
        _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_bool : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.bool) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState11 ->
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
# 97 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Bool(bool) )
# 808 "smt_lang_parser.ml"
             in
            _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState239 | MenhirState66 | MenhirState224 | MenhirState225 | MenhirState220 | MenhirState221 | MenhirState216 | MenhirState217 | MenhirState212 | MenhirState213 | MenhirState208 | MenhirState209 | MenhirState204 | MenhirState205 | MenhirState200 | MenhirState201 | MenhirState197 | MenhirState193 | MenhirState194 | MenhirState190 | MenhirState186 | MenhirState187 | MenhirState183 | MenhirState180 | MenhirState176 | MenhirState177 | MenhirState172 | MenhirState173 | MenhirState168 | MenhirState169 | MenhirState164 | MenhirState165 | MenhirState160 | MenhirState161 | MenhirState156 | MenhirState157 | MenhirState152 | MenhirState153 | MenhirState148 | MenhirState149 | MenhirState144 | MenhirState145 | MenhirState140 | MenhirState141 | MenhirState136 | MenhirState137 | MenhirState132 | MenhirState133 | MenhirState128 | MenhirState129 | MenhirState124 | MenhirState125 | MenhirState120 | MenhirState121 | MenhirState116 | MenhirState117 | MenhirState112 | MenhirState113 | MenhirState108 | MenhirState109 | MenhirState104 | MenhirState105 | MenhirState99 | MenhirState100 | MenhirState101 | MenhirState96 | MenhirState90 | MenhirState85 | MenhirState78 | MenhirState79 | MenhirState75 | MenhirState69 | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (bool : (Smt_lang_ast.bool))) = _menhir_stack in
        let _v : (Smt_lang_ast.exp) = 
# 135 "smt_lang_parser.mly"
    ( (*Case 2*) Bool(bool) )
# 824 "smt_lang_parser.ml"
         in
        _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_exp : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71)
    | MenhirState71 ->
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
# 143 "smt_lang_parser.mly"
    ( (*Case 2*) Or(exp,exp_prime) )
# 869 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState75 ->
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
# 145 "smt_lang_parser.mly"
    ( (*Case 2*) Not(exp) )
# 894 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79)
    | MenhirState79 ->
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
# 139 "smt_lang_parser.mly"
    ( (*Case 2*) Neq(exp,exp_prime) )
# 938 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (u32 : (
# 73 "smt_lang_parser.mly"
       (int)
# 959 "smt_lang_parser.ml"
            ))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 201 "smt_lang_parser.mly"
    ( (*Case 2*) ZeroExtend(u32,exp_prime) )
# 969 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState90 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (u32 : (
# 73 "smt_lang_parser.mly"
       (int)
# 990 "smt_lang_parser.ml"
            ))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 203 "smt_lang_parser.mly"
    ( (*Case 2*) SignExtend(u32,exp_prime) )
# 1000 "smt_lang_parser.ml"
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
            let ((((_menhir_stack, _menhir_s), (u32 : (
# 73 "smt_lang_parser.mly"
       (int)
# 1021 "smt_lang_parser.ml"
            ))), (u32_prime : (
# 73 "smt_lang_parser.mly"
       (int)
# 1025 "smt_lang_parser.ml"
            ))), _, (exp_prime_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _3 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 199 "smt_lang_parser.mly"
    ( (*Case 2*) Extract(u32,u32_prime,exp_prime_prime) )
# 1035 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState100
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState100
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState100
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100)
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState101
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101)
    | MenhirState101 ->
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
# 213 "smt_lang_parser.mly"
    ( (*Case 2*) Ite(exp,exp_prime,exp_prime_prime) )
# 1098 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState105
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState105
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState105
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105)
    | MenhirState105 ->
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
# 137 "smt_lang_parser.mly"
    ( (*Case 2*) Eq(exp,exp_prime) )
# 1142 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState108 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState109
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState109
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState109
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState109)
    | MenhirState109 ->
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
# 211 "smt_lang_parser.mly"
    ( (*Case 2*) Concat(exp,exp_prime) )
# 1186 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState112 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState113
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState113
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState113
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState113)
    | MenhirState113 ->
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
# 157 "smt_lang_parser.mly"
    ( (*Case 2*) Bvxor(exp,exp_prime) )
# 1230 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState117
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState117
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState117
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState117)
    | MenhirState117 ->
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
# 163 "smt_lang_parser.mly"
    ( (*Case 2*) Bvxnor(exp,exp_prime) )
# 1274 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState121
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState121
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState121
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState121)
    | MenhirState121 ->
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
# 177 "smt_lang_parser.mly"
    ( (*Case 2*) Bvurem(exp,exp_prime) )
# 1318 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState125
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState125
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState125
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState125)
    | MenhirState125 ->
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
# 183 "smt_lang_parser.mly"
    ( (*Case 2*) Bvult(exp,exp_prime) )
# 1362 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState129
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState129
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState129
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129)
    | MenhirState129 ->
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
# 187 "smt_lang_parser.mly"
    ( (*Case 2*) Bvule(exp,exp_prime) )
# 1406 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState132 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState133
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState133
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState133
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState133)
    | MenhirState133 ->
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
# 195 "smt_lang_parser.mly"
    ( (*Case 2*) Bvugt(exp,exp_prime) )
# 1450 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState137
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState137
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState137
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState137)
    | MenhirState137 ->
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
# 191 "smt_lang_parser.mly"
    ( (*Case 2*) Bvuge(exp,exp_prime) )
# 1494 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState141
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState141
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState141
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState141)
    | MenhirState141 ->
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
# 173 "smt_lang_parser.mly"
    ( (*Case 2*) Bvudiv(exp,exp_prime) )
# 1538 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState144 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState145
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState145
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState145
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState145)
    | MenhirState145 ->
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
# 169 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsub(exp,exp_prime) )
# 1582 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState149)
    | MenhirState149 ->
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
# 179 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsrem(exp,exp_prime) )
# 1626 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState152 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState153
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState153
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState153
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState153)
    | MenhirState153 ->
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
# 181 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsmod(exp,exp_prime) )
# 1670 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState157
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState157
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState157
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState157)
    | MenhirState157 ->
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
# 185 "smt_lang_parser.mly"
    ( (*Case 2*) Bvslt(exp,exp_prime) )
# 1714 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState161
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState161
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState161
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState161)
    | MenhirState161 ->
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
# 189 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsle(exp,exp_prime) )
# 1758 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState164 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState165
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState165
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState165
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState165)
    | MenhirState165 ->
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
# 205 "smt_lang_parser.mly"
    ( (*Case 2*) Bvshl(exp,exp_prime) )
# 1802 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState168 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState169
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState169
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState169
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState169)
    | MenhirState169 ->
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
# 197 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsgt(exp,exp_prime) )
# 1846 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState172 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState173
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState173
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState173
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState173)
    | MenhirState173 ->
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
# 193 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsge(exp,exp_prime) )
# 1890 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState176 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState177
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState177
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState177
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState177)
    | MenhirState177 ->
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
# 175 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsdiv(exp,exp_prime) )
# 1934 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState180 ->
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
# 151 "smt_lang_parser.mly"
    ( (*Case 2*) Bvredor(exp) )
# 1959 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState183 ->
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
# 149 "smt_lang_parser.mly"
    ( (*Case 2*) Bvredand(exp) )
# 1984 "smt_lang_parser.ml"
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
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState187
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState187
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState187
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState187)
    | MenhirState187 ->
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
# 155 "smt_lang_parser.mly"
    ( (*Case 2*) Bvor(exp,exp_prime) )
# 2028 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState190 ->
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
# 147 "smt_lang_parser.mly"
    ( (*Case 2*) Bvnot(exp) )
# 2053 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState194 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState194
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState194
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState194
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState194 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState194)
    | MenhirState194 ->
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
# 161 "smt_lang_parser.mly"
    ( (*Case 2*) Bvnor(exp,exp_prime) )
# 2097 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState197 ->
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
# 165 "smt_lang_parser.mly"
    ( (*Case 2*) Bvneg(exp) )
# 2122 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState200 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState201
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState201
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState201
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState201)
    | MenhirState201 ->
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
# 159 "smt_lang_parser.mly"
    ( (*Case 2*) Bvnand(exp,exp_prime) )
# 2166 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState204 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState205
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState205
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState205
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState205)
    | MenhirState205 ->
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
# 171 "smt_lang_parser.mly"
    ( (*Case 2*) Bvmul(exp,exp_prime) )
# 2210 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState209
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState209
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState209
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState209)
    | MenhirState209 ->
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
# 207 "smt_lang_parser.mly"
    ( (*Case 2*) Bvlshr(exp,exp_prime) )
# 2254 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState212 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState213
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState213
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState213
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState213)
    | MenhirState213 ->
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
# 209 "smt_lang_parser.mly"
    ( (*Case 2*) Bvashr(exp,exp_prime) )
# 2298 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState216 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState217
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState217
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState217
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState217)
    | MenhirState217 ->
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
# 153 "smt_lang_parser.mly"
    ( (*Case 2*) Bvand(exp,exp_prime) )
# 2342 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState220 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState221
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState221
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState221
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState221)
    | MenhirState221 ->
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
# 167 "smt_lang_parser.mly"
    ( (*Case 2*) Bvadd(exp,exp_prime) )
# 2386 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState225
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState225
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState225
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState225)
    | MenhirState225 ->
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
# 141 "smt_lang_parser.mly"
    ( (*Case 2*) And(exp,exp_prime) )
# 2430 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (vu32 : (
# 72 "smt_lang_parser.mly"
       (string)
# 2451 "smt_lang_parser.ml"
            ))), _, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.def) = 
# 219 "smt_lang_parser.mly"
    ( (*Case 2*) DefineConst(vu32,exp) )
# 2459 "smt_lang_parser.ml"
             in
            _menhir_goto_def _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState239 ->
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
# 221 "smt_lang_parser.mly"
    ( (*Case 2*) Assert(exp) )
# 2484 "smt_lang_parser.ml"
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

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 72 "smt_lang_parser.mly"
       (string)
# 2499 "smt_lang_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (vu32 : (
# 72 "smt_lang_parser.mly"
       (string)
# 2507 "smt_lang_parser.ml"
    )) = _v in
    let _v : (Smt_lang_ast.valu) = 
# 91 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Symbolic(vu32) )
# 2512 "smt_lang_parser.ml"
     in
    _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Smt_lang_ast.valu) = 
# 101 "smt_lang_parser.mly"
    ( (*Case 2*) Val_String )
# 2524 "smt_lang_parser.ml"
     in
    _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BVI _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ONE_TWO_EIGHT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), (bvi : (
# 76 "smt_lang_parser.mly"
       (string)
# 2552 "smt_lang_parser.ml"
                ))) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _1 = () in
                let _v : (Smt_lang_ast.valu) = 
# 95 "smt_lang_parser.mly"
    ( (*Case 2*) Val_I128(bvi) )
# 2560 "smt_lang_parser.ml"
                 in
                _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | SIX_FOUR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), (bvi : (
# 76 "smt_lang_parser.mly"
       (string)
# 2581 "smt_lang_parser.ml"
                ))) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _1 = () in
                let _v : (Smt_lang_ast.valu) = 
# 93 "smt_lang_parser.mly"
    ( (*Case 2*) Val_I64(bvi) )
# 2589 "smt_lang_parser.ml"
                 in
                _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
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
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState37
            | BV _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
            | LPAREN_UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState37
            | S ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState37
            | VU_THREE_TWO _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
            | RBRACE ->
                _menhir_reduce61 _menhir_env (Obj.magic _menhir_stack) MenhirState37
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState37)
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
# 111 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Poison )
# 2652 "smt_lang_parser.ml"
             in
            _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | STRUCT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState25
        | RPAREN ->
            _menhir_reduce59 _menhir_env (Obj.magic _menhir_stack) MenhirState25
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25)
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
# 103 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Unit )
# 2690 "smt_lang_parser.ml"
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
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState8
            | BV _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
            | LPAREN_UNDERSCORE ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState8
            | S ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState8
            | VU_THREE_TWO _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
            | RBRACE ->
                _menhir_reduce61 _menhir_env (Obj.magic _menhir_stack) MenhirState8
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

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 77 "smt_lang_parser.mly"
       (string)
# 2741 "smt_lang_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (bv : (
# 77 "smt_lang_parser.mly"
       (string)
# 2749 "smt_lang_parser.ml"
    )) = _v in
    let _v : (Smt_lang_ast.valu) = 
# 99 "smt_lang_parser.mly"
    ( (*Case 2*) Val_Bits(bv) )
# 2754 "smt_lang_parser.ml"
     in
    _menhir_goto_valu _menhir_env _menhir_stack _menhir_s _v

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState11
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState11
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState11)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_accessor_list : _menhir_env -> 'ttv_tail -> (Smt_lang_ast.accessor_list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState60
    | BV _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
    | LPAREN_UNDERSCORE ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState60
    | S ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState60
    | VU_THREE_TWO _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState60

and _menhir_reduce53 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smt_lang_ast.accessor list) = 
# 211 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [] )
# 2811 "smt_lang_parser.ml"
     in
    _menhir_goto_list_accessor_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run52 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | NAME _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), (name : (
# 75 "smt_lang_parser.mly"
       (string)
# 2839 "smt_lang_parser.ml"
                ))) = _menhir_stack in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _v : (Smt_lang_ast.accessor) = 
# 225 "smt_lang_parser.mly"
    ( (*Case 2*) Field(name) )
# 2847 "smt_lang_parser.ml"
                 in
                let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LPAREN_UNDERSCORE ->
                    _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState58
                | RPAREN ->
                    _menhir_reduce53 _menhir_env (Obj.magic _menhir_stack) MenhirState58
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58)
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

and _menhir_goto_list_def_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.def list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | EVENTS ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | LPAREN ->
                        _menhir_run246 _menhir_env (Obj.magic _menhir_stack) MenhirState245
                    | RPAREN ->
                        _menhir_reduce57 _menhir_env (Obj.magic _menhir_stack) MenhirState245
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState245)
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
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState251 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smt_lang_ast.def))), _, (xs : (Smt_lang_ast.def list))) = _menhir_stack in
        let _v : (Smt_lang_ast.def list) = 
# 213 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( x :: xs )
# 2938 "smt_lang_parser.ml"
         in
        _menhir_goto_list_def_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

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
        let (((_menhir_stack, _menhir_s), (vu32 : (
# 72 "smt_lang_parser.mly"
       (string)
# 2958 "smt_lang_parser.ml"
        ))), (ty : (Smt_lang_ast.ty))) = _menhir_stack in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Smt_lang_ast.def) = 
# 217 "smt_lang_parser.mly"
    ( (*Case 2*) DeclareConst(vu32,ty) )
# 2966 "smt_lang_parser.ml"
         in
        _menhir_goto_def _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run67 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 72 "smt_lang_parser.mly"
       (string)
# 2979 "smt_lang_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (vu32 : (
# 72 "smt_lang_parser.mly"
       (string)
# 2987 "smt_lang_parser.ml"
    )) = _v in
    let _v : (Smt_lang_ast.exp) = 
# 131 "smt_lang_parser.mly"
    ( (*Case 2*) Var(vu32) )
# 2992 "smt_lang_parser.ml"
     in
    _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v

and _menhir_run12 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Smt_lang_ast.bool) = 
# 125 "smt_lang_parser.mly"
    ( (*Case 2*) True )
# 3004 "smt_lang_parser.ml"
     in
    _menhir_goto_bool _menhir_env _menhir_stack _menhir_s _v

and _menhir_run68 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState224 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState224
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState224
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState224
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState224 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState224)
    | BVADD ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState220 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState220 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState220)
    | BVAND ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState216 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState216
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState216
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState216
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState216 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState216)
    | BVASHR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState212 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState212
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState212
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState212
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState212 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState212)
    | BVLSHR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState208
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState208
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState208
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState208)
    | BVMUL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState204)
    | BVNAND ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState200
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState200
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState200
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState200)
    | BVNEG ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState197
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState197
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState197
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197)
    | BVNOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState193)
    | BVNOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState190 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState190
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState190
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState190
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState190 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState190)
    | BVOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState186
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState186
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState186
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState186)
    | BVREDAND ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState183
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState183
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState183
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState183)
    | BVREDOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState180
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState180
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState180
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState180)
    | BVSDIV ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState176)
    | BVSGE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState172
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState172
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState172
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172)
    | BVSGT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState168
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState168
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState168
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState168)
    | BVSHL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState164
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState164
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState164
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState164)
    | BVSLE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState160
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState160
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState160
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState160)
    | BVSLT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState156
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState156)
    | BVSMOD ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState152
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState152
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState152
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState152)
    | BVSREM ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState148)
    | BVSUB ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState144
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState144
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState144
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState144)
    | BVUDIV ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState140
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState140
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState140
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState140)
    | BVUGE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState136
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState136
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState136
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState136)
    | BVUGT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState132)
    | BVULE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState128 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState128
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState128
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState128
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState128 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState128)
    | BVULT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState124
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState124
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState124
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState124)
    | BVUREM ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState120
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState120
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState120
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState120)
    | BVXNOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState116
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState116
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState116
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116)
    | BVXOR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState112
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState112
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState112
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState112)
    | CONCAT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState108
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState108
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState108
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState108)
    | EQ ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState104)
    | ITE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState99
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState99)
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
                        | BV _v ->
                            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
                        | FALSE ->
                            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState96
                        | LPAREN ->
                            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState96
                        | TRUE ->
                            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState96
                        | VU_THREE_TWO _v ->
                            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96)
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
        | SIGN_UNDERSCORE_EXTEND ->
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
                    | BV _v ->
                        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _v
                    | FALSE ->
                        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState90
                    | LPAREN ->
                        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState90
                    | TRUE ->
                        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState90
                    | VU_THREE_TWO _v ->
                        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState90)
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
        | ZERO_UNDERSCORE_EXTEND ->
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
                    | BV _v ->
                        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
                    | FALSE ->
                        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState85
                    | LPAREN ->
                        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState85
                    | TRUE ->
                        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState85
                    | VU_THREE_TWO _v ->
                        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85)
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
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78)
    | NOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState75
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
    | OR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState69
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run13 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Smt_lang_ast.bool) = 
# 127 "smt_lang_parser.mly"
    ( (*Case 2*) False )
# 3862 "smt_lang_parser.ml"
     in
    _menhir_goto_bool _menhir_env _menhir_stack _menhir_s _v

and _menhir_run70 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 77 "smt_lang_parser.mly"
       (string)
# 3869 "smt_lang_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (bv : (
# 77 "smt_lang_parser.mly"
       (string)
# 3877 "smt_lang_parser.ml"
    )) = _v in
    let _v : (Smt_lang_ast.exp) = 
# 133 "smt_lang_parser.mly"
    ( (*Case 2*) Bits(bv) )
# 3882 "smt_lang_parser.ml"
     in
    _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v

and _menhir_run2 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | NAME _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState3
        | BV _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
        | LPAREN_UNDERSCORE ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState3
        | S ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState3
        | VU_THREE_TWO _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run48 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | NAME _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LPAREN_UNDERSCORE ->
                _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState51
            | RPAREN ->
                _menhir_reduce53 _menhir_env (Obj.magic _menhir_stack) MenhirState51
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState51)
        | NIL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _1 = () in
            let _v : (Smt_lang_ast.accessor_list) = 
# 229 "smt_lang_parser.mly"
    ( (*Case 2*) Nil )
# 3950 "smt_lang_parser.ml"
             in
            _menhir_goto_accessor_list _menhir_env _menhir_stack _v
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

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState251 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState249 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState245 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState239 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState221 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState220 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState217 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState216 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState213 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState212 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState209 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState205 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState204 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState201 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState200 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState194 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState190 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState187 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState186 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState180 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState177 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState176 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState172 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState169 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState168 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState165 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState164 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState161 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState160 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState157 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState153 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState152 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState149 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState148 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState145 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState144 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState141 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState137 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState133 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState132 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState125 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState124 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState121 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState117 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState112 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState109 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState108 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState90 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState60 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState37 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_reduce55 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smt_lang_ast.def list) = 
# 211 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
    ( [] )
# 4329 "smt_lang_parser.ml"
     in
    _menhir_goto_list_def_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run64 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASSERT ->
        _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
    | DECLARE_MINUS_CONST ->
        _menhir_run230 _menhir_env (Obj.magic _menhir_stack)
    | DEFINE_MINUS_CONST ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run65 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | VU_THREE_TWO _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BV _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
        | FALSE ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | LPAREN ->
            _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | TRUE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | VU_THREE_TWO _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState66)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run230 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | VU_THREE_TWO _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _1 = () in
            let _v : (Smt_lang_ast.ty) = 
# 119 "smt_lang_parser.mly"
    ( (*Case 2*) Ty_Bool )
# 4403 "smt_lang_parser.ml"
             in
            _menhir_goto_ty _menhir_env _menhir_stack _v
        | LPAREN_UNDERSCORE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BITVEC ->
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
# 73 "smt_lang_parser.mly"
       (int)
# 4429 "smt_lang_parser.ml"
                        ))) = _menhir_stack in
                        let _4 = () in
                        let _2 = () in
                        let _1 = () in
                        let _v : (Smt_lang_ast.ty) = 
# 121 "smt_lang_parser.mly"
    ( (*Case 2*) Ty_BitVec(u32) )
# 4437 "smt_lang_parser.ml"
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

and _menhir_run239 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BV _v ->
        _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | FALSE ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | LPAREN ->
        _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | TRUE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState239
    | VU_THREE_TWO _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState239

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
# 80 "smt_lang_parser.mly"
       (Smt_lang_ast.term)
# 4503 "smt_lang_parser.ml"
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
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASSERT ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack)
        | DECLARE_MINUS_CONST ->
            _menhir_run230 _menhir_env (Obj.magic _menhir_stack)
        | DEFINE_MINUS_CONST ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack)
        | FORMULAS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LPAREN ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState63
            | RPAREN ->
                _menhir_reduce55 _menhir_env (Obj.magic _menhir_stack) MenhirState63
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63)
        | READ_MINUS_REG ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | WRITE_MINUS_REG ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack)
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
  




# 4564 "smt_lang_parser.ml"

# 269 "/local/scratch/pes20/myopamroot/default/lib/menhir/standard.mly"
  

# 4569 "smt_lang_parser.ml"
