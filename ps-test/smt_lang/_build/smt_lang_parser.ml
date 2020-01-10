
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | ZEROEXTEND
    | VEC_UNDERSCORE_BOOL
    | VAR
    | U_THREE_TWO of (
# 55 "smt_lang_parser.mly"
       (string)
# 14 "smt_lang_parser.ml"
  )
    | U_SIX_FOUR of (
# 56 "smt_lang_parser.mly"
       (string)
# 19 "smt_lang_parser.ml"
  )
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
  | MenhirState240
  | MenhirState234
  | MenhirState230
  | MenhirState228
  | MenhirState222
  | MenhirState218
  | MenhirState214
  | MenhirState210
  | MenhirState206
  | MenhirState202
  | MenhirState198
  | MenhirState194
  | MenhirState190
  | MenhirState186
  | MenhirState182
  | MenhirState178
  | MenhirState174
  | MenhirState170
  | MenhirState166
  | MenhirState162
  | MenhirState158
  | MenhirState154
  | MenhirState150
  | MenhirState142
  | MenhirState136
  | MenhirState130
  | MenhirState126
  | MenhirState122
  | MenhirState118
  | MenhirState114
  | MenhirState110
  | MenhirState106
  | MenhirState104
  | MenhirState88
  | MenhirState86
  | MenhirState84
  | MenhirState82
  | MenhirState80
  | MenhirState78
  | MenhirState76
  | MenhirState74
  | MenhirState72
  | MenhirState70
  | MenhirState68
  | MenhirState66
  | MenhirState64
  | MenhirState62
  | MenhirState60
  | MenhirState58
  | MenhirState56
  | MenhirState54
  | MenhirState52
  | MenhirState50
  | MenhirState48
  | MenhirState46
  | MenhirState44
  | MenhirState42
  | MenhirState40
  | MenhirState38
  | MenhirState36
  | MenhirState34
  | MenhirState32
  | MenhirState30
  | MenhirState28
  | MenhirState26
  | MenhirState20
  | MenhirState18
  | MenhirState16
  | MenhirState14
  | MenhirState12
  | MenhirState4
  | MenhirState0

# 2 "smt_lang_parser.mly"
  
open Smt_lang_ast

# 161 "smt_lang_parser.ml"

let rec _menhir_goto_exp : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smt_lang_ast.exp) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState106
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState106)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 88 "smt_lang_parser.mly"
    ( (*Case 2*) And(exp,exp_prime) )
# 290 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState110
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 114 "smt_lang_parser.mly"
    ( (*Case 2*) Bvadd(exp,exp_prime) )
# 422 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 100 "smt_lang_parser.mly"
    ( (*Case 2*) Bvand(exp,exp_prime) )
# 554 "smt_lang_parser.ml"
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
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState118
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState118)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 156 "smt_lang_parser.mly"
    ( (*Case 2*) Bvashr(exp,exp_prime) )
# 686 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState122
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 154 "smt_lang_parser.mly"
    ( (*Case 2*) Bvlshr(exp,exp_prime) )
# 818 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState126
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState126)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 118 "smt_lang_parser.mly"
    ( (*Case 2*) Bvmul(exp,exp_prime) )
# 950 "smt_lang_parser.ml"
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
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 106 "smt_lang_parser.mly"
    ( (*Case 2*) Bvnand(exp,exp_prime) )
# 1082 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState76 ->
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
# 112 "smt_lang_parser.mly"
    ( (*Case 2*) Bvneg(exp) )
# 1107 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState136)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 108 "smt_lang_parser.mly"
    ( (*Case 2*) Bvnor(exp,exp_prime) )
# 1239 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState72 ->
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
# 94 "smt_lang_parser.mly"
    ( (*Case 2*) Bvnot(exp) )
# 1264 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState142
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState142)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 102 "smt_lang_parser.mly"
    ( (*Case 2*) Bvor(exp,exp_prime) )
# 1396 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState68 ->
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
# 96 "smt_lang_parser.mly"
    ( (*Case 2*) Bvredand(exp) )
# 1421 "smt_lang_parser.ml"
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
            let ((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 98 "smt_lang_parser.mly"
    ( (*Case 2*) Bvredor(exp) )
# 1446 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState150
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 122 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsdiv(exp,exp_prime) )
# 1578 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState154)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 140 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsge(exp,exp_prime) )
# 1710 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
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
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState158
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState158)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 144 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsgt(exp,exp_prime) )
# 1842 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState162
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState162)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 152 "smt_lang_parser.mly"
    ( (*Case 2*) Bvshl(exp,exp_prime) )
# 1974 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState166
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState166)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 136 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsle(exp,exp_prime) )
# 2106 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState170)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 132 "smt_lang_parser.mly"
    ( (*Case 2*) Bvslt(exp,exp_prime) )
# 2238 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState174)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 128 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsmod(exp,exp_prime) )
# 2370 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState178
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState178)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 126 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsrem(exp,exp_prime) )
# 2502 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState182)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 116 "smt_lang_parser.mly"
    ( (*Case 2*) Bvsub(exp,exp_prime) )
# 2634 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState186
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState186)
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
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 120 "smt_lang_parser.mly"
    ( (*Case 2*) Bvudiv(exp,exp_prime) )
# 2766 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState190
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState190)
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
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 138 "smt_lang_parser.mly"
    ( (*Case 2*) Bvuge(exp,exp_prime) )
# 2898 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState194
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState194)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
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
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 142 "smt_lang_parser.mly"
    ( (*Case 2*) Bvugt(exp,exp_prime) )
# 3030 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState198
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState198)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState198 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 134 "smt_lang_parser.mly"
    ( (*Case 2*) Bvule(exp,exp_prime) )
# 3162 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState202
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState202)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState202 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 130 "smt_lang_parser.mly"
    ( (*Case 2*) Bvult(exp,exp_prime) )
# 3294 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState206)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 124 "smt_lang_parser.mly"
    ( (*Case 2*) Bvurem(exp,exp_prime) )
# 3426 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
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
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState210
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState210)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 110 "smt_lang_parser.mly"
    ( (*Case 2*) Bvxnor(exp,exp_prime) )
# 3558 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState214
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState214)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 104 "smt_lang_parser.mly"
    ( (*Case 2*) Bvxor(exp,exp_prime) )
# 3690 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState218
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState218)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 158 "smt_lang_parser.mly"
    ( (*Case 2*) Concat(exp,exp_prime) )
# 3822 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState222
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState222)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 84 "smt_lang_parser.mly"
    ( (*Case 2*) Eq(exp,exp_prime) )
# 3954 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), (u32 : (
# 55 "smt_lang_parser.mly"
       (string)
# 3975 "smt_lang_parser.ml"
            ))), (u32_prime : (
# 55 "smt_lang_parser.mly"
       (string)
# 3979 "smt_lang_parser.ml"
            ))), _, (exp_prime_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 146 "smt_lang_parser.mly"
    ( (*Case 2*) Extract(u32,u32_prime,exp_prime_prime) )
# 3989 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState228)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState230
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState230)
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
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))), _, (exp_prime_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 160 "smt_lang_parser.mly"
    ( (*Case 2*) Ite(exp,exp_prime,exp_prime_prime) )
# 4228 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState234
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState234)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState234 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 86 "smt_lang_parser.mly"
    ( (*Case 2*) Neq(exp,exp_prime) )
# 4360 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState16 ->
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
# 92 "smt_lang_parser.mly"
    ( (*Case 2*) Not(exp) )
# 4385 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | AND ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BITS ->
                _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BITS_SIX_FOUR ->
                _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BOOL1 ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVADD ->
                _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVAND ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVASHR ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVLSHR ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVMUL ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVNAND ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVNEG ->
                _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVNOR ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVNOT ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVOR ->
                _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVREDAND ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVREDOR ->
                _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVSDIV ->
                _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVSGE ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVSGT ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVSHL ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVSLE ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVSLT ->
                _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVSMOD ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVSREM ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVSUB ->
                _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVUDIV ->
                _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVUGE ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVUGT ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVULE ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVULT ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVUREM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVXNOR ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | BVXOR ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | CONCAT ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | EQ ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | EXTRACT ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | ITE ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | NEQ ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | NOT ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | OR ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | SIGNEXTEND ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | VAR ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | ZEROEXTEND ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState240
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState240)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState240 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (exp : (Smt_lang_ast.exp))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 90 "smt_lang_parser.mly"
    ( (*Case 2*) Or(exp,exp_prime) )
# 4517 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (u32 : (
# 55 "smt_lang_parser.mly"
       (string)
# 4538 "smt_lang_parser.ml"
            ))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 150 "smt_lang_parser.mly"
    ( (*Case 2*) SignExtend(u32,exp_prime) )
# 4547 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
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
# 55 "smt_lang_parser.mly"
       (string)
# 4568 "smt_lang_parser.ml"
            ))), _, (exp_prime : (Smt_lang_ast.exp))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Smt_lang_ast.exp) = 
# 148 "smt_lang_parser.mly"
    ( (*Case 2*) ZeroExtend(u32,exp_prime) )
# 4577 "smt_lang_parser.ml"
             in
            _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (exp : (Smt_lang_ast.exp))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 59 "smt_lang_parser.mly"
       (Smt_lang_ast.exp)
# 4599 "smt_lang_parser.ml"
            ) = 
# 66 "smt_lang_parser.mly"
    ( exp )
# 4603 "smt_lang_parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (
# 59 "smt_lang_parser.mly"
       (Smt_lang_ast.exp)
# 4610 "smt_lang_parser.ml"
            )) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState240 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState234 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState230 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState228 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState218 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState210 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState206 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState202 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState198 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState194 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState190 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState186 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState182 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState178 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState174 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState170 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState162 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState158 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState126 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState88 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState86 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState60 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
                | AND ->
                    _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BITS ->
                    _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BITS_SIX_FOUR ->
                    _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BOOL1 ->
                    _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVADD ->
                    _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVAND ->
                    _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVASHR ->
                    _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVLSHR ->
                    _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVMUL ->
                    _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVNAND ->
                    _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVNEG ->
                    _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVNOR ->
                    _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVNOT ->
                    _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVOR ->
                    _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVREDAND ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVREDOR ->
                    _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVSDIV ->
                    _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVSGE ->
                    _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVSGT ->
                    _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVSHL ->
                    _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVSLE ->
                    _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVSLT ->
                    _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVSMOD ->
                    _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVSREM ->
                    _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVSUB ->
                    _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVUDIV ->
                    _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVUGE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVUGT ->
                    _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVULE ->
                    _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVULT ->
                    _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVUREM ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVXNOR ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | BVXOR ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | CONCAT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | EQ ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | EXTRACT ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | ITE ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | NEQ ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | NOT ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | OR ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | SIGNEXTEND ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | VAR ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState4
                | ZEROEXTEND ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState4
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
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), (u32 : (
# 55 "smt_lang_parser.mly"
       (string)
# 5066 "smt_lang_parser.ml"
                ))) = _menhir_stack in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _v : (Smt_lang_ast.exp) = 
# 76 "smt_lang_parser.mly"
    ( (*Case 2*) Var(u32) )
# 5074 "smt_lang_parser.ml"
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
                | AND ->
                    _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BITS ->
                    _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BITS_SIX_FOUR ->
                    _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BOOL1 ->
                    _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVADD ->
                    _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVAND ->
                    _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVASHR ->
                    _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVLSHR ->
                    _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVMUL ->
                    _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVNAND ->
                    _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVNEG ->
                    _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVNOR ->
                    _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVNOT ->
                    _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVOR ->
                    _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVREDAND ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVREDOR ->
                    _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVSDIV ->
                    _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVSGE ->
                    _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVSGT ->
                    _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVSHL ->
                    _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVSLE ->
                    _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVSLT ->
                    _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVSMOD ->
                    _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVSREM ->
                    _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVSUB ->
                    _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVUDIV ->
                    _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVUGE ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVUGT ->
                    _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVULE ->
                    _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVULT ->
                    _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVUREM ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVXNOR ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | BVXOR ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | CONCAT ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | EQ ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | EXTRACT ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | ITE ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | NEQ ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | NOT ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | OR ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | SIGNEXTEND ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | VAR ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | ZEROEXTEND ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState12
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12)
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

and _menhir_run13 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState14
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState16
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run17 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState18
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run19 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState20
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
                        | AND ->
                            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BITS ->
                            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BITS_SIX_FOUR ->
                            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BOOL1 ->
                            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVADD ->
                            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVAND ->
                            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVASHR ->
                            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVLSHR ->
                            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVMUL ->
                            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVNAND ->
                            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVNEG ->
                            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVNOR ->
                            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVNOT ->
                            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVOR ->
                            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVREDAND ->
                            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVREDOR ->
                            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVSDIV ->
                            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVSGE ->
                            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVSGT ->
                            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVSHL ->
                            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVSLE ->
                            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVSLT ->
                            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVSMOD ->
                            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVSREM ->
                            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVSUB ->
                            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVUDIV ->
                            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVUGE ->
                            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVUGT ->
                            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVULE ->
                            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVULT ->
                            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVUREM ->
                            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVXNOR ->
                            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | BVXOR ->
                            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | CONCAT ->
                            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | EQ ->
                            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | EXTRACT ->
                            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | ITE ->
                            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | NEQ ->
                            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | NOT ->
                            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | OR ->
                            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | SIGNEXTEND ->
                            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | VAR ->
                            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | ZEROEXTEND ->
                            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState26
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState26)
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
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState28)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run29 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState30
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState30)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run31 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState32
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run33 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState34
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState36
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run37 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState38
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run39 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState40
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run41 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState42
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run43 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run45 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run47 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState48
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run49 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState50
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run51 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState52
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState52)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run53 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState54
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run55 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState56
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState56)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run57 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState58
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run59 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState60)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run61 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run63 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run65 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState66
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState66
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

and _menhir_run67 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState68
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run69 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState70
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run71 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run73 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run75 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run77 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run79 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run81 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState82
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run85 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState86
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run87 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState88
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState88)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run89 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | BOOL2 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _2 = () in
                let _1 = () in
                let _v : (Smt_lang_ast.exp) = 
# 82 "smt_lang_parser.mly"
    ( (*Case 2*) Bool )
# 9189 "smt_lang_parser.ml"
                 in
                _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
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

and _menhir_run93 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | U_SIX_FOUR _v ->
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
                        let (((_menhir_stack, _menhir_s), (u64 : (
# 56 "smt_lang_parser.mly"
       (string)
# 9246 "smt_lang_parser.ml"
                        ))), (u32 : (
# 55 "smt_lang_parser.mly"
       (string)
# 9250 "smt_lang_parser.ml"
                        ))) = _menhir_stack in
                        let _6 = () in
                        let _4 = () in
                        let _2 = () in
                        let _1 = () in
                        let _v : (Smt_lang_ast.exp) = 
# 80 "smt_lang_parser.mly"
    ( (*Case 2*) Bits64(u64,u32) )
# 9259 "smt_lang_parser.ml"
                         in
                        _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
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
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run99 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | VEC_UNDERSCORE_BOOL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RPAREN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _2 = () in
                let _1 = () in
                let _v : (Smt_lang_ast.exp) = 
# 78 "smt_lang_parser.mly"
    ( (*Case 2*) Bits )
# 9321 "smt_lang_parser.ml"
                 in
                _menhir_goto_exp _menhir_env _menhir_stack _menhir_s _v
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

and _menhir_run103 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
        | AND ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BITS ->
            _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BITS_SIX_FOUR ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BOOL1 ->
            _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVADD ->
            _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVAND ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVASHR ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVLSHR ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVMUL ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVNAND ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVNEG ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVNOR ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVNOT ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVOR ->
            _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVREDAND ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVREDOR ->
            _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVSDIV ->
            _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVSGE ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVSGT ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVSHL ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVSLE ->
            _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVSLT ->
            _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVSMOD ->
            _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVSREM ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVSUB ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVUDIV ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVUGE ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVUGT ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVULE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVULT ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVUREM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVXNOR ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | BVXOR ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | CONCAT ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | EQ ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | EXTRACT ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | ITE ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | NEQ ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | NOT ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | OR ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | SIGNEXTEND ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | VAR ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | ZEROEXTEND ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState104
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState104)
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

and exp_start : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 59 "smt_lang_parser.mly"
       (Smt_lang_ast.exp)
# 9466 "smt_lang_parser.ml"
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
    | AND ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BITS ->
        _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BITS_SIX_FOUR ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BOOL1 ->
        _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVADD ->
        _menhir_run87 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVAND ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVASHR ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVLSHR ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVMUL ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVNAND ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVNEG ->
        _menhir_run75 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVNOR ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVNOT ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVOR ->
        _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVREDAND ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVREDOR ->
        _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVSDIV ->
        _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVSGE ->
        _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVSGT ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVSHL ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVSLE ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVSLT ->
        _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVSMOD ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVSREM ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVSUB ->
        _menhir_run47 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVUDIV ->
        _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVUGE ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVUGT ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVULE ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVULT ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVUREM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVXNOR ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | BVXOR ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | CONCAT ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EQ ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EXTRACT ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | ITE ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | NEQ ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | NOT ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | OR ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | SIGNEXTEND ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | VAR ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | ZEROEXTEND ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

# 269 "/home/pes20/myopamroot/default/lib/menhir/standard.mly"
  

# 9574 "smt_lang_parser.ml"
