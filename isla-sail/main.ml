(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Ast
open Ast_util
open Jib
open Jib_util

let opt_output : string ref = ref "out.ir"

let options =
  Arg.align [
      ( "-o",
        Arg.String (fun file -> opt_output := file ^ ".ir"),
        "<file> The name of the output file");
      ( "-v",
        Arg.Int (fun verbosity -> Util.opt_verbosity := verbosity),
        "<verbosity> produce verbose output");
    ]

let usage_msg = "usage: isla-sail <options> <file1.sail> ... <fileN.sail>\n"

module Ir_config : Jib_compile.Config = struct
  open Type_check
  open Jib_compile

  let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
  let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

  let rec convert_typ ctx typ =
    let Typ_aux (typ_aux, l) as typ = Env.expand_synonyms ctx.tc_env typ in
    match typ_aux with
    | Typ_id id when string_of_id id = "bit"    -> CT_bit
    | Typ_id id when string_of_id id = "bool"   -> CT_bool
    | Typ_id id when string_of_id id = "int"    -> CT_lint
    | Typ_id id when string_of_id id = "nat"    -> CT_lint
    | Typ_id id when string_of_id id = "unit"   -> CT_unit
    | Typ_id id when string_of_id id = "string" -> CT_string
    | Typ_id id when string_of_id id = "real"   -> CT_real

    | Typ_app (id, _) when string_of_id id = "atom_bool" -> CT_bool

    | Typ_app (id, args) when string_of_id id = "itself" ->
       convert_typ ctx (Typ_aux (Typ_app (mk_id "atom", args), l))
    | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" || string_of_id id = "implicit" ->
       begin match destruct_range Env.empty typ with
       | None -> assert false (* Checked if range type in guard *)
       | Some (kids, constr, n, m) ->
          let ctx = { ctx with local_env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env }in
          match nexp_simp n, nexp_simp m with
          | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
               when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
             CT_fint 64
          | n, m ->
             if prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n) && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64))) then
               CT_fint 64
             else
               CT_lint
       end

    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" ->
       CT_list (convert_typ ctx typ)

    (* Note that we have to use lbits for zero-length bitvectors because they are not allowed by SMTLIB *)
    | Typ_app (id, [A_aux (A_nexp n, _); A_aux (A_order ord, _)])
         when string_of_id id = "bitvector"  ->
       let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
       begin match nexp_simp n with
       | Nexp_aux (Nexp_constant n, _) when Big_int.equal n Big_int.zero -> CT_lbits direction
       | Nexp_aux (Nexp_constant n, _) -> CT_fbits (Big_int.to_int n, direction)
       | _ -> CT_lbits direction
       end

    | Typ_app (id, [A_aux (A_nexp _, _);
                    A_aux (A_order ord, _);
                    A_aux (A_typ typ, _)])
         when string_of_id id = "vector" ->
       let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
       CT_vector (direction, convert_typ ctx typ)

    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "register" ->
       CT_ref (convert_typ ctx typ)

    | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.records  -> CT_struct (id, Bindings.find id ctx.records |> UBindings.bindings)
    | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.variants -> CT_variant (id, Bindings.find id ctx.variants |> UBindings.bindings)
    | Typ_id id when Bindings.mem id ctx.enums -> CT_enum (id, Bindings.find id ctx.enums |> IdSet.elements)

    | Typ_tup typs -> CT_tup (List.map (convert_typ ctx) typs)

    | Typ_exist _ ->
       (* Use Type_check.destruct_exist when optimising with SMT, to
          ensure that we don't cause any type variable clashes in
          local_env, and that we can optimize the existential based
          upon it's constraints. *)
       begin match destruct_exist (Env.expand_synonyms ctx.local_env typ) with
       | Some (kids, nc, typ) ->
          let env = add_existential l kids nc ctx.local_env in
          convert_typ { ctx with local_env = env } typ
       | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
       end

    | Typ_var _ -> CT_poly

    | _ -> raise (Reporting.err_unreachable l __POS__ ("No C type for type " ^ string_of_typ typ))

  let optimize_anf _ aexp = aexp

  let unroll_loops () = None
  let specialize_calls = false
  let ignore_64 = false
  let struct_value = false
  let use_real = false
end

let jib_of_ast env ast =
  let open Jib_compile in
  let module Jibc = Make(Ir_config) in
  let ctx = initial_ctx (add_special_functions env) in
  Jibc.compile_ast ctx ast

let remove_casts cdefs =
  let module StringMap = Map.Make(String) in
  let conversions = ref StringMap.empty in

  let legal_cast = function
    | CT_fbits _, CT_lbits _ -> true
    | CT_lbits _, CT_fbits _ -> true
    | _, _ -> false
  in

  let remove_instr_casts = function
    | I_aux (I_copy (clexp, cval), aux) ->
       let ctyp_to = clexp_ctyp clexp in
       let ctyp_from = cval_ctyp cval in
       if ctyp_equal ctyp_to ctyp_from || legal_cast (ctyp_to, ctyp_from) then
         [I_aux (I_copy (clexp, cval), aux)]
       else (
         let fid = Printf.sprintf "%s->%s" (string_of_ctyp ctyp_from) (string_of_ctyp ctyp_to) in
         conversions := StringMap.add fid (ctyp_from, ctyp_to) !conversions;
         [I_aux (I_funcall (clexp, false, (mk_id fid, []), [cval]), aux)]
       )
    | I_aux (I_init (ctyp_to, id, cval), aux) ->
       let ctyp_from = cval_ctyp cval in
       if ctyp_equal ctyp_to ctyp_from || legal_cast (ctyp_to, ctyp_from) then (
         [I_aux (I_init (ctyp_to, id, cval), aux)]
       ) else (
         let fid = Printf.sprintf "%s->%s" (string_of_ctyp ctyp_from) (string_of_ctyp ctyp_to) in
         conversions := StringMap.add fid (ctyp_from, ctyp_to) !conversions;
         [I_aux (I_decl (ctyp_to, id), aux);
          ifuncall (CL_id (id, ctyp_to)) (mk_id fid, []) [cval]]
       )
    | instr -> [instr]
  in
  let cdefs = List.map (fun cdef -> cdef_concatmap_instr remove_instr_casts cdef) cdefs in
  let vals =
    List.map (fun (fid, (ctyp_from, ctyp_to)) ->
        CDEF_spec (mk_id fid, Some fid, [ctyp_from], ctyp_to)
      ) (StringMap.bindings !conversions)
  in
  vals @ cdefs

(** Sail allows val x = "y" declarations to also have an
   implementation, which is used for some backends. Currently these
   can be preserved by the Sail->Jib compiler, so we remove any
   here. *)
let remove_extern_impls cdefs =
  let exts = ref IdSet.empty in
  List.iter
    (function
     | CDEF_spec (id, Some _, _, _) -> exts := IdSet.add id !exts
     | _ -> ()
    ) cdefs;
  List.filter
    (function
     | CDEF_fundef (id, _, _, _) when IdSet.mem id !exts -> false
     | _ -> true
    ) cdefs

let main () =
  let open Process_file in
  let opt_file_arguments = ref [] in
  Arg.parse options (fun s ->
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg;

  (* These options are either needed for ARM, or increase performance significantly (memo_z3) *)
  Nl_flow.opt_nl_flow := true;
  Type_check.opt_no_lexp_bounds_check := true;
  Process_file.opt_memo_z3 := true;
  Reporting.opt_warnings := false;
  Initial_check.opt_undefined_gen := true;

  let _, ast, env = load_files options Type_check.initial_env !opt_file_arguments in
  let ast, env = descatter env ast in
  let ast, env = rewrite_ast_target "smt" env ast in
  let ast, env = Specialize.(specialize typ_ord_specialization env ast) in
  let cdefs, ctx = jib_of_ast env ast in
  let cdefs, _ = Jib_optimize.remove_tuples cdefs ctx in
  let cdefs = remove_casts cdefs |> remove_extern_impls in
  let buf = Buffer.create 256 in
  Jib_ir.Flat_ir_formatter.output_defs buf cdefs;
  let out_chan = open_out !opt_output in
  output_string out_chan (Buffer.contents buf);
  flush out_chan;
  close_out out_chan

let () =
  try main () with
  | Reporting.Fatal_error e ->
     Reporting.print_error e;
     exit 1
