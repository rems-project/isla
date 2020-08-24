default Order dec

$include <prelude.sail>

// Linearizing this function produces an out-of-range slice operation, which we
// only allow symbolically for now

function lin(i : range(0,15), v: bits(16)) -> bits(8) = {
  if i >= 8 then {
    v[i, 8]
  } else {
    v[i+7, 8]
  }
}

function f(i : range(0,15), v: bits(16)) -> bits(8) = {
  if i >= 8 then {
    v[i, 8]
  } else {
    v[i+7, 8]
  }
}

function prop(i: range(0,15), v: bits(16)) -> bool = {
  f(i, v) == lin(i, v)
  & f(5, 0x1234) == lin(5, 0x1234) & f(10, 0x5678) == lin(10, 0x5678)
}
