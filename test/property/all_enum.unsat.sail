default Order dec

$include <prelude.sail>

val "eq_anything" : forall ('a : Type). ('a, 'a) -> bool

overload operator == = {eq_anything}

enum E = A | B | C | D | F

function prop(x: E) -> bool = {
  x == A | x == B | x == C | x == D | x == F
}
