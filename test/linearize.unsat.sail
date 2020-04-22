default Order dec

$include <prelude.sail>

register R: bool

function lin() -> bits(1) = {
  if R then {
    0b0
  } else {
    0b1
  }
}

function f() -> bits(1) = {
  if R then {
    0b0
  } else {
    0b1
  }
}

function prop() -> bool = {
  f() == lin()
}
