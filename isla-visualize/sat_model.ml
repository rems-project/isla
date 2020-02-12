
open Printf
open Sexpr

let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x::ls -> (string_of x) ^ sep ^ (string_of_list sep string_of ls)

let rec string_of_sexpr = function
  | List sexprs -> "(" ^ string_of_list " " string_of_sexpr sexprs ^ ")"
  | Atom str -> str

let sexpr_of_sat_model smt_output =
  let lexbuf = Lexing.from_string smt_output in
  Sat_model_parser.sexpr_list_eof Sat_model_lexer.token lexbuf

let rec dump_sexpr indent = function
  | List sexprs ->
     print_endline (indent ^ "(");
     List.iter (dump_sexpr ("  " ^ indent)) sexprs;
     print_endline (indent ^ ")")
  | Atom str -> print_endline (indent ^ str)

let interpret_var a ev1 ev2 =
  if a = ev1 then (fun x1 _ -> x1)
  else if a = ev2 then (fun _ x2 -> x2)
  else (fun _ _ -> a)

module StringMap = Map.Make(String)

let rec fold_sexpr f = function
  | Atom str -> f (Atom str)
  | List sexprs -> f (List (List.map (fold_sexpr f) sexprs))

let subst_lets bindings body =
  let substitutions =
    List.fold_left (fun m -> function
                     | List [Atom v; subst] -> StringMap.add v subst m
                     | _ -> Output.warn "Bad subst"; m
                   ) StringMap.empty bindings
  in
  let subst = function
    | Atom v ->
       begin match StringMap.find_opt v substitutions with
       | Some s -> s
       | None -> Atom v
       end
    | sexpr -> sexpr
  in
  fold_sexpr subst body

let rec interpret_body rels ev1 ev2 = function
  | List (Atom "or" :: disjunction) ->
     let fns = List.map (interpret_body rels ev1 ev2) disjunction in
     fun x1 x2 -> List.exists (fun f -> f x1 x2) fns
  | List (Atom "and" :: conjunction) ->
     let fns = List.map (interpret_body rels ev1 ev2) conjunction in
     fun x1 x2 -> List.for_all (fun f -> f x1 x2) fns
  | List (Atom "not" :: [sexpr]) ->
     let fn = interpret_body rels ev1 ev2 sexpr in
     fun x1 x2 -> not (fn x1 x2)
  | List (Atom "=" :: [Atom a1; Atom a2]) ->
     let fn1 = interpret_var a1 ev1 ev2 in
     let fn2 = interpret_var a2 ev1 ev2 in
     fun x1 x2 -> fn1 x1 x2 = fn2 x1 x2
  | List (Atom "ite" :: [cond_sexpr; then_sexpr; else_sexpr]) ->
     let cond_fn = interpret_body rels ev1 ev2 cond_sexpr in
     let then_fn = interpret_body rels ev1 ev2 then_sexpr in
     let else_fn = interpret_body rels ev1 ev2 else_sexpr in
     fun x1 x2 -> if cond_fn x1 x2 then then_fn x1 x2 else else_fn x1 x2
  | List (Atom "let" :: [List bindings; body]) ->
     let body = subst_lets bindings body in
     interpret_body rels ev1 ev2 body
  | List (Atom rel :: [Atom a1; Atom a2]) ->
     let fn1 = interpret_var a1 ev1 ev2 in
     let fn2 = interpret_var a2 ev1 ev2 in
     begin match List.assoc_opt rel rels with
     | Some rel_fn -> fun x1 x2 -> rel_fn (fn1 x1 x2) (fn2 x1 x2)
     | None -> Output.fatal (sprintf "Could not find relation %s" rel)
     end
  | List (Atom pred :: [Atom a]) ->
     let fn = interpret_var a ev1 ev2 in
     begin match List.assoc_opt pred rels with
     | Some rel_fn -> fun x1 x2 -> rel_fn (fn x1 x2) (fn x1 x2)
     | None -> Output.fatal (sprintf "Could not find predicate %s" pred)
     end
  | Atom "false" ->
     fun _ _ -> false
  | Atom "true" ->
     fun _ _ -> true
  | sexpr ->
     dump_sexpr "" sexpr;
     exit 1

let rec interpret_relations rels = function
  | List [Atom "define-fun"; Atom rel; List [List [Atom ev1; Atom "Event"]; List [Atom ev2; Atom "Event"]]; Atom "Bool"; body] :: rest ->
     Output.log 2 (lazy (sprintf "Interpreting relation %s" rel));
     let fn = interpret_body rels ev1 ev2 body in
     interpret_relations ((rel, fn) :: rels) rest
  | List [Atom "define-fun"; Atom pred; List [List [Atom ev; Atom "Event"]]; Atom "Bool"; body] :: rest ->
     Output.log 2 (lazy (sprintf "Interpreting predicate %s" pred));
     (* Interpret predicates as subsets of the identity relation *)
     let fn = interpret_body rels ev ev body in
     interpret_relations ((pred, (fun x1 x2 -> if x1 = x2 then fn x1 x2 else false)) :: rels) rest
  | _ :: rest -> interpret_relations rels rest
  | [] -> rels

let colors =
  Array.of_list [
      "forestgreen";
      "goldenrod";
      "cadetblue4";
      "blue4";
      "maroon4";
      "thistle";
      "chartreuse3";
      "red";
      "violet";
      "sienna";
      "deeppink1";
      "dodgerblue3";
      "firebrick1";
      "orangered";
      "magenta1";
      "darkslateblue";
      "darkslategray";
      "darkorange3";
      "crimson";
      "darkolivegreen4";
      "darkorchid4";
      "cornflowerblue";
      "red4";
      "olivedrab";
      "peru";
      "indigo";
      "limegreen";
      "indianred3";
      "lightslateblue";
      "lemonchiffon4";
      "orange2";
      "honeydew4"
    ]

let next_color = ref 0

let assign_color () =
  try
    let color = colors.(!next_color) in
    incr next_color;
    color
  with
  | Invalid_argument _ -> "black"

module EventEdge = struct
  type t = string * string
  let compare (ev1a, ev2a) (ev1b, ev2b) =
    let c = String.compare ev1a ev1b in
    if c = 0 then String.compare ev2a ev2b else c
end

let string_of_event event = event
let asm_of_event event = event

module EventGraph = Set.Make(EventEdge)

let transitive_reduction g =
  let events = List.map (fun (ev1, ev2) -> [ev1; ev2]) (EventGraph.elements g) |> List.concat |> List.sort_uniq String.compare in
  let g' = ref g in
  List.iter (fun x ->
      List.iter (fun y ->
          List.iter (fun z ->
              (* For visualisation, we only want to remove edges between distinct vertices, because we care about irreflexivity and cyclicity *)
              if not (String.compare x y = 0 || String.compare y z = 0 || String.compare x z = 0) then
                if EventGraph.mem (x, y) !g' && EventGraph.mem (y, z) !g' then
                  g' := EventGraph.remove (x, z) !g'
            ) events
        ) events
    ) events;
  !g'

let rec interpret_reads reads = function
  | List [Atom "define-fun"; Atom read; List []; _; Atom value] :: rest ->
     (try
        let pos = Str.search_backward (Str.regexp_string "_ret") read (String.length read - 1) in
        if pos = String.length read - 4 then
          let eid = String.sub read 0 (String.length read - 4) in
          Output.log 2 (lazy (sprintf "Found value %s = %s for event %s" read value eid));
          interpret_reads ((eid, value) :: reads) rest
        else
          interpret_reads reads rest
      with
      | Not_found -> interpret_reads reads rest)
  | _ :: rest -> interpret_reads reads rest
  | [] -> reads

let interpret_sat_output tids events = function
  | [Atom "sat"; List (Atom "model" :: model)] ->
     let reads = interpret_reads [] model in
     let rels = interpret_relations [] model in

     (* is_active ev1 ev2 = not (is_inactive ev1 ev2) in
     let preds = [("is_active", is_active); ("is_inactive", is_inactive)] in
     let rels = List.map (fun (rel_name, smtlib) -> rel_name, interpret_body preds "ev1" "ev2" smtlib) extras @ rels in

     (* Remove the is_(in)active predicate from the relations, so we can color inactive nodes separately *)
     let rels = List.filter (fun (rel_name, _) -> rel_name <> "is_inactive" && rel_name <> "is_active") rels in *)

     print_endline "digraph EXEC {";
     List.iter (fun tid ->
         let tid_name = string_of_int tid in
         print_endline (sprintf "  subgraph cluster%s {" tid_name);
         print_endline (sprintf "    label=\"Thread %d\"" tid);
         List.iter (fun ev ->
             let eid = string_of_event ev in
             let asm = asm_of_event ev in
             if (try let _ = Str.search_backward (Str.regexp ("_" ^ tid_name ^ "$")) eid (String.length eid - 1) in true with Not_found -> false) then
               let fill = "" in
               let value = match List.assoc_opt eid reads with Some value -> "\\l" ^ value | None -> "" in
               print_endline (sprintf "    %s [label=\"%s%s\\l%s\"%s]" eid asm value eid fill)
           ) events;
         print_endline "  }"
       ) tids;
     List.iter (fun ev ->
         let eid = string_of_event ev in
         if (try let _ = Str.search_forward (Str.regexp_string "IW") eid 0 in true with Not_found -> false) then
           print_endline (sprintf "  %s [label=\"%s\"]" eid eid)
       ) events;
     List.iter (fun (rel, fn) ->
         let g = ref EventGraph.empty in
         List.iter (fun ev1 ->
             List.iter (fun ev2 ->
                 let eid1, eid2 = string_of_event ev1, string_of_event ev2 in
                 if fn eid1 eid2 then
                   g := EventGraph.add (eid1, eid2) !g
               ) events
           ) events;
         let g = transitive_reduction !g in
         let color = assign_color () in
         List.iter (fun (eid1, eid2) ->
             print_endline (sprintf "  %s -> %s [color=%s,label=\"%s\"]" eid1 eid2 color rel)
           ) (EventGraph.elements g)
       ) rels;
     print_endline "}"
  | _ ->
     Output.fatal "Expected solver to return sat"

let interpret_unsat_output tids events = function
  | [Atom "unsat"] ->
     Output.log 1 (lazy "Got expected solver result: unsat")
  | [Atom "sat"; List (Atom "model" :: _)] as output ->
     interpret_sat_output tids events output;
     Output.fatal "Expected solver to return unsat"
  | _ ->
     Output.fatal "Expected solver to return unsat"
