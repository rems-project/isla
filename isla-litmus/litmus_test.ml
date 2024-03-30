(*========================================================================================*)
(*                                                                                        *)
(*                rmem executable model                                                   *)
(*                =====================                                                   *)
(*                                                                                        *)
(*  This file is:                                                                         *)
(*                                                                                        *)
(*  Copyright Shaked Flur, University of Cambridge                            2016-2018   *)
(*  Copyright Christopher Pulte, University of Cambridge                      2016-2018   *)
(*  Copyright Jon French, University of Cambridge                             2016-2018   *)
(*  Copyright Robert Norton-Wright, University of Cambridge                        2017   *)
(*  Copyright Peter Sewell, University of Cambridge                                2016   *)
(*  Copyright Luc Maranget, INRIA, Paris, France                                   2017   *)
(*  Copyright Linden Ralph, University of Cambridge (when this work was done)      2017   *)
(*                                                                                        *)
(*  All rights reserved.                                                                  *)
(*                                                                                        *)
(*  It is part of the rmem tool, distributed under the 2-clause BSD licence in            *)
(*  LICENCE.txt.                                                                          *)
(*                                                                                        *)
(*========================================================================================*)

open Printf

let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x::ls -> (string_of x) ^ sep ^ (string_of_list sep string_of ls)

let rec option_these = function
  | Some x :: xs -> x :: option_these xs
  | None :: xs -> option_these xs
  | [] -> []

let rec map_filter (f : 'a -> 'b option) (l : 'a list) : 'b list =
  match l with [] -> []
    | x :: xs ->
      let xs' = map_filter f xs in
      match (f x) with None -> xs'
        | Some x' -> x' :: xs'

module Arch_config =
struct
  let memory = Memory.Direct
  let cautious = true
  let hexa = true
  let asmcomment = None
end

module SymbConstant = SymbConstant.Make(ParsedConstant.StringScalar)

module GenericHGen = GenericHGenArch.Make(Arch_config)(SymbConstant)

module GenericHGenLexParse =
struct
  type instruction = GenericHGen.pseudo
  type token = GenericHGenParser.token

  module LexConfig = struct let debug = false end

  module PL = GenericHGenLexer.Make(LexConfig)
  let lexer = PL.token
  let parser = GenericHGenParser.main
end

module Make_litmus_parser
    (Arch: Arch_litmus.S with type V.Scalar.t = string)
    (LexParse: GenParser.LexParse with type instruction = Arch.parsedPseudo)
    (GenParserConfig : GenParser.Config)
    =
struct
  module Parser = GenParser.Make(GenParserConfig)(Arch)(LexParse)
  let parse in_chan test_splitted =
    Parser.parse in_chan test_splitted
end

let read_channel
      (name: string)
      (in_chan: in_channel)
      (overwrite_check_cond : string -> string option)
  =
  (* First split the input file in sections *)
  let module SPL = Splitter.Make(Splitter.Default) in
  let test_splitted  = SPL.split name in_chan in

  let module GenParserConfig : GenParser.Config = struct
    let debuglexer = false
    let check_kind _ = None
    let check_cond = overwrite_check_cond
    let verbose = 0
  end in

  let litmus_test =
    let module Parser =
      Make_litmus_parser(GenericHGen)(GenericHGenLexParse)(GenParserConfig)
    in
    Parser.parse in_chan test_splitted
  in

  (test_splitted, litmus_test)

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

(* Initial state processing *)

type initial_register_value =
  | Label of string
  | RegisterValue of string

type initial_state = {
    symbolic_values : StringSet.t;
    symbolic_locations : string StringMap.t;
    symbolic_run_types : string StringMap.t;
    registers : (int * (string * initial_register_value)) list
  }

let empty_initial_state = {
    symbolic_values = StringSet.empty;
    symbolic_locations = StringMap.empty;
    symbolic_run_types = StringMap.empty;
    registers = []
  }

type location =
  | Loc_reg of int * string
  | Loc_symbolic of string

let string_of_register_value = function
  | Label name -> sprintf "%s:" name
  | RegisterValue v -> v

let location_info = function
  | MiscParser.Location_reg (tid, reg) -> Some (Loc_reg (tid, reg))
  | MiscParser.Location_global (Symbolic (name, _)) -> Some (Loc_symbolic name)
  | loc ->
     Output.fatal (sprintf "Register type in %s not supported by isla-litmus" (MiscParser.dump_location loc))

let process_initial_state init =
  let process_location istate (l, (run_type, maybev)) =
    match location_info l with
    | None -> istate
    | Some (Loc_reg (tid, reg_name)) ->
       begin match maybev with
       | Constant.Symbolic (symb, _) ->
          { istate with
            symbolic_values = StringSet.add symb istate.symbolic_values;
            registers = (tid, (reg_name, RegisterValue symb)) :: istate.registers;
            symbolic_run_types = StringMap.add symb "uint32_t" istate.symbolic_run_types
          }
       | Constant.Concrete str ->
          { istate with registers = (tid, (reg_name, RegisterValue str)) :: istate.registers }
       | Constant.Label (l, str) ->
          { istate with registers = (tid, (reg_name, Label str)) :: istate.registers }
       end
    | Some (Loc_symbolic symb) ->
       let istate = match maybev with
       | Constant.Symbolic (str, _) ->
          { istate with
            symbolic_values = StringSet.add str istate.symbolic_values;
            symbolic_run_types = StringMap.add symb "uint32_t" istate.symbolic_run_types
          }
       | _ -> istate
       in
       begin match maybev with
       | Constant.Concrete str | Constant.Symbolic (str, _) ->
          { istate with
            symbolic_values = StringSet.add symb istate.symbolic_values;
            symbolic_locations = StringMap.add symb str istate.symbolic_locations;
            symbolic_run_types =
              let open MiscParser in
              match run_type with
              | TyDef -> StringMap.add symb "uint32_t" istate.symbolic_run_types
              | Ty type_name -> StringMap.add symb type_name istate.symbolic_run_types
              | _ ->
                 Output.fatal ("Concrete location has an unknown type: " ^ pp_run_type run_type)
          }
       | _ ->
          Output.fatal "Symbolic location with a label value not supported in initial state"
       end
  in
  List.fold_left process_location empty_initial_state init

(* Final state processing *)

type smt_result = Sat | Unsat

let string_of_smt_result = function
  | Sat -> "sat"
  | Unsat -> "unsat"

type sexpr = List of (sexpr list) | Atom of string

let flatten_and = function
  | List (Atom "and" :: xs) -> xs
  | sexpr -> [sexpr]

let flatten_or = function
  | List (Atom "or" :: xs) -> xs
  | sexpr -> [sexpr]

let rec flatten_sexpr = function
  | List (Atom "and" :: xs) ->
     let xs = List.map flatten_sexpr xs in
     List (Atom "and" :: List.concat (List.map flatten_and xs))
  | List (Atom "or" :: xs) ->
     let xs = List.map flatten_sexpr xs in
     List (Atom "or" :: List.concat (List.map flatten_or xs))
  | List xs ->
     List (List.map flatten_sexpr xs)
  | Atom x ->
     Atom x

let rec string_of_sexpr = function
  | List (Atom "and" :: xs) -> string_of_list " & " string_of_sexpr_bracket xs
  | List (Atom "or" :: xs) -> string_of_list " | " string_of_sexpr_bracket xs
  | List [Atom "not"; x] -> "~" ^ string_of_sexpr_bracket x
  | List [Atom "=>"; x; y] -> string_of_sexpr_bracket x ^ " -> " ^ string_of_sexpr_bracket y
  | List [Atom "="; List [Atom "register"; Atom reg_name; Atom tid]; x] ->
     tid ^ ":" ^ reg_name ^ " = " ^ string_of_sexpr_bracket x
  | List [Atom "="; List [Atom "last_write_to"; Atom name]; x] ->
     "*" ^ name ^ " = " ^ string_of_sexpr_bracket x
  | List sexprs -> "(" ^ string_of_list " " string_of_sexpr sexprs ^ ")"
  | Atom str -> str

and string_of_sexpr_bracket = function
  | List (Atom "and" :: _) as sexpr -> "(" ^ string_of_sexpr sexpr ^ ")"
  | List (Atom "or" :: _) as sexpr -> "(" ^ string_of_sexpr sexpr ^ ")"
  | List (Atom "=>" :: _) as sexpr -> "(" ^ string_of_sexpr sexpr ^ ")"
  | sexpr -> string_of_sexpr sexpr

type final_state = {
    locations : (int * (string * string)) list;
    assertion : sexpr;
    expect : smt_result
  }

let rec prop_locations =
  let open ConstrGen in
  function
  | Atom (LV (l, _)) -> [location_info l]
  | Atom (LL (l, l')) -> [location_info l; location_info l']
  | Not prop -> prop_locations prop
  | And props | Or props -> List.concat (List.map prop_locations props)
  | Implies (prop, prop') -> prop_locations prop @ prop_locations prop'

let lookup_location locs (tid, reg_name) =
  let find_out_id (tid', (out_id, _, reg_name', ctyp)) =
    if tid = tid' && reg_name = reg_name' then Some (out_id, ctyp) else None
  in
  match map_filter find_out_id locs with
  | out :: _ -> out
  | [] ->
     Output.fatal (sprintf "Could not find output id for register %d:%s" tid reg_name)

let rec compile_prop final_locations prop =
  let compile_loc l =
    match location_info l with
    | Some (Loc_reg (tid, reg_name)) ->
       List [Atom "register"; Atom reg_name; Atom (string_of_int tid)]
    | Some (Loc_symbolic name) ->
       List [Atom "last_write_to"; Atom name]
    | None ->
       Output.fatal "Invalid location in final state"
  in
  let compile_value = function
    | Constant.Concrete str | Constant.Symbolic (str, _) -> Atom str
    | _ -> Output.fatal "Failed to compile value to SMT in litmus assertion"
  in
  match prop with
  | ConstrGen.Atom (LV (l, v)) ->
     let l = compile_loc l in
     let v = compile_value v in
     List [Atom "="; l; v]
  | ConstrGen.Atom (LL (l, v)) ->
     Output.fatal "LL atom not yet supported"
  | ConstrGen.And [] ->
     Atom "true"
  | ConstrGen.And props ->
     List (Atom "and" :: List.map (compile_prop final_locations) props)
  | ConstrGen.Or [] ->
     Atom "false"
  | ConstrGen.Or props ->
     List (Atom "or" :: List.map (compile_prop final_locations) props)
  | ConstrGen.Not prop ->
     List [Atom "not"; compile_prop final_locations prop]
  | ConstrGen.Implies (prop, prop') ->
     List [Atom "=>"; compile_prop final_locations prop; compile_prop final_locations prop']

let process_final_state final =
  let default_state prop =
    let locs = option_these (prop_locations prop) in
    let final_locations =
      List.mapi (fun n -> function
        | Loc_reg (tid, reg_name) ->
           let output = "|output " ^ string_of_int n ^ "|" in
           Some (tid, (output, reg_name))
        | Loc_symbolic name -> None
        ) locs |> option_these in
    { locations = final_locations;
      assertion = compile_prop final_locations prop;
      expect = Sat
    }
  in
  match final with
  | ConstrGen.ExistsState prop -> default_state prop
  | ConstrGen.NotExistsState prop -> { (default_state prop) with expect = Unsat }
  | ConstrGen.ForallStates prop ->
     let s = default_state prop in
     { s with assertion = List [Atom "not"; s.assertion]; expect = Unsat }

let rec string_of_pseudo_list = function
  | GenericHGen.Instruction str :: rest -> "\t" ^ String.escaped str ^ "\n" ^ string_of_pseudo_list rest
  | GenericHGen.Nop :: rest -> string_of_pseudo_list rest
  | GenericHGen.Label (label, pseudo) :: rest -> label ^ ":\n" ^ string_of_pseudo_list (pseudo :: rest)
  | GenericHGen.Symbolic _ :: _ | GenericHGen.Macro _ :: _ -> Output.fatal "Macro or Symbolic instruction found in litmus file"
  | [] -> ""

let process (armv8_page_tables : bool) ((test_splitted, litmus_test) : Splitter.result * GenericHGen.pseudo MiscParser.t) =
  let open Buffer in
  let buf = create 256 in

  let add_pair key value =
    add_string buf (sprintf "%s = \"%s\"\n" key (String.escaped value))
  in

  add_pair "arch" (Archs.pp test_splitted.arch);
  add_pair "name" (test_splitted.name.name);

  List.iter (fun (k, v) ->
      add_string buf (sprintf "%s = \"%s\"\n" (String.lowercase_ascii k) (String.escaped v))
    ) litmus_test.info;
  let istate = process_initial_state (litmus_test.init) in

  (* Output the list of variables *)
  string_of_list ", " (fun x -> "\"" ^ String.escaped x ^ "\"") (StringSet.elements istate.symbolic_values)
  |> sprintf "symbolic = [%s]\n"
  |> add_string buf;

  if armv8_page_tables then (
    add_string buf "\npage_table_setup = \"\"\"\n";

    string_of_list " " (fun x -> "pa_" ^ String.escaped x) (StringSet.elements istate.symbolic_values)
    |> sprintf "  physical %s;\n"
    |> add_string buf;

    string_of_list ";\n" (fun x -> "  " ^ String.escaped x ^ " |-> pa_" ^ String.escaped x) (StringSet.elements istate.symbolic_values)
    |> sprintf "%s;\n"
    |> add_string buf;
    
    if not (StringMap.is_empty istate.symbolic_locations) then (
      string_of_list ";\n" (fun (x, v) -> sprintf "*%s = %s" (String.escaped x) v) (StringMap.bindings istate.symbolic_locations)
      |> sprintf "%s;\n"
      |> add_string buf;
    );
                          
    add_string buf "\"\"\"\n";
  ) else if not (StringMap.is_empty istate.symbolic_locations) then (
    add_string buf "\n[locations]\n";
    string_of_list "\n" (fun (x, v) -> "\"" ^ String.escaped x ^ "\" = \"" ^ v ^ "\"")
      (StringMap.bindings istate.symbolic_locations)
    |> add_string buf;
    add_string buf "\n"
  );

  if not (StringMap.is_empty istate.symbolic_run_types) then (
    add_string buf "\n[types]\n";
    string_of_list "\n" (fun (x, v) -> "\"" ^ String.escaped x ^ "\" = \"" ^ v ^ "\"")
      (StringMap.bindings istate.symbolic_run_types)
    |> add_string buf;
    add_string buf "\n"
  );

  List.iter (fun (tid, pseudo) ->
      add_string buf (sprintf "\n[thread.%d]\n" tid);
      let thread_init = List.filter (fun assignment -> fst assignment = tid) istate.registers |> List.map snd in
      add_string buf (sprintf "init = { %s }\n" (string_of_list ", " (fun (k, v) -> sprintf "%s = \"%s\"" k (string_of_register_value v)) thread_init));
      add_string buf (sprintf "code = \"\"\"\n%s\"\"\"\n" (string_of_pseudo_list pseudo));
    ) litmus_test.prog;

  let final_state = process_final_state litmus_test.condition in
  add_string buf "\n[final]\n";
  add_pair "expect" (string_of_smt_result final_state.expect);
  add_pair "assertion" (string_of_sexpr (flatten_sexpr final_state.assertion));

  output_buffer stdout buf;
  ()

