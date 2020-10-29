default Order dec

$include <prelude.sail>

val "string_take" : (string, nat) -> string
val "string_drop" : (string, nat) -> string
val "string_length" : string -> nat
val "eq_string" : (string, string) -> bool

overload operator == = {eq_string}

function prop() -> bool = {
  let s = "sail";
  assert(string_take(s, 2) == "sa");
  assert(string_drop(s, 2) == "il");
  assert(string_drop(s, 4) == "");
  assert(string_drop(s, 5) == "");
  assert(string_take(s, 0) == "");
  assert(string_take(s, 4) == "sail");
  assert(string_take(s, 5) == "sail");
  assert(string_length("") == 0);
  assert(string_length(s) == 4);
  true
}
