default Order dec

$include <prelude.sail>

let A = 0b00
let B = 0b01
let C = 0b10
let D = 0b11

register RC: bool
register RD: bool

function lin(x: bits(2)) -> bool = {
  if x == A | x == B then {
    true
  } else if x == C then {
    RC
  } else {
    RD
  }
}

function f(x: bits(2)) -> bool = {
  if x == A | x == B then {
    true
  } else if x == C then {
    RC
  } else {
    RD
  }
}

function prop(x: bits(2)) -> bool = {
  f(x) == lin(x)
}
