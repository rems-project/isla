let big_num_of_string x =
  let rec of_hex_string x accum =
    if String.length x = 0 then accum else

    let short = 7 in
    let of_short_hex_string x =
      let int_value = int_of_string ("0x" ^ x) in
      Nat_big_num.of_int int_value
    in

    let l = min (String.length x) short in
    let v = of_short_hex_string (String.sub x 0 l) in
    let accum = Nat_big_num.shift_left accum (l * 4) in
    let accum = Nat_big_num.add accum v in
    of_hex_string (String.sub x l ((String.length x) - l)) accum
  in

  let pref' = try String.sub x 0 2 with Invalid_argument _ -> "" in
  if pref' = "0x" || pref' = "0X" then
    of_hex_string (String.sub x 2 ((String.length x) - 2)) Nat_big_num.zero
  else
    Nat_big_num.of_string x


let big_num_to_hex_string n =
  if Nat_big_num.less n Nat_big_num.zero then (* n < 0 *)
    failwith "(nat_big_num_to_hex_string) negative number";

  let max = Nat_big_num.pow_int_positive 2 16 in

  let rec pp n acc : string list =
    if Nat_big_num.less n max then (* n < 2^16 *)
      Printf.sprintf "%x" (Nat_big_num.to_int n) :: acc
    else
      let ls = Nat_big_num.extract_num n 0 16 in
      let ls_string = Printf.sprintf "%04x" (Nat_big_num.to_int ls) in
      let n' = Nat_big_num.shift_right n 16 in
      pp n' (ls_string :: acc)
  in
  pp n []
  |> String.concat ""

let map_constrgen_atom (f : 'b -> 'c) : ('a, 'b) ConstrGen.atom -> ('a, 'c) ConstrGen.atom =
   function
  | LV (a, b) -> LV (a, f b)
  | LL (a, b) -> LL (a, b)

let rec map_constrgen_prop (f : 'b -> 'c) : ('a, 'b) ConstrGen.prop -> ('a, 'c) ConstrGen.prop =
   function
  | Atom a         -> Atom (map_constrgen_atom f a)
  | Not p          -> Not (map_constrgen_prop f p)
  | And ps         -> And (List.map (map_constrgen_prop f) ps)
  | Or ps          -> Or (List.map (map_constrgen_prop f) ps)
  | Implies (p, q) -> Implies (map_constrgen_prop f p, map_constrgen_prop f q)

let map_constrgen_constr (f : 'a -> 'b) : 'a ConstrGen.constr -> 'b ConstrGen.constr =
   function
  | ForallStates p   -> ForallStates (f p)
  | ExistsState p    -> ExistsState (f p)
  | NotExistsState p -> NotExistsState (f p)
