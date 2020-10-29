default Order dec

$include <prelude.sail>

val "eq_anything" : forall ('a : Type). ('a, 'a) -> bool
overload operator == = {eq_anything}

register R: bool

function lin() -> (bits(1), bits(1)) = {
  if R then {
    (0b0, 0b1)
  } else {
    (0b1, 0b0)
  }
}

function f() -> (bits(1), bits(1)) = {
  if R then {
    (0b0, 0b1)
  } else {
    (0b1, 0b0)
  }
}

function prop() -> bool = {
  f() == lin()
}
