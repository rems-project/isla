default Order dec

$include <prelude.sail>

// This example has enough control flow that it revealed a bug in our SSA construction.

function lin(a: bits(4), b: bits(4), c: bool, d: bool) -> (bits(4), bits(4)) = {
  A: bits(4) = 0x0;
  B: bits(4) = 0x0;
  if c then {
    A = a;
    B = b;
    if d then {
      B = B + 1
    }
  };
  (A, B)
}

function f(a: bits(4), b: bits(4), c: bool, d: bool) -> (bits(4), bits(4)) = {
  A: bits(4) = 0x0;
  B: bits(4) = 0x0;
  if c then {
    A = a;
    B = b;
    if d then {
      B = B + 1
    }
  };
  (A, B)
}

function prop(a: bits(4), b: bits(4), c: bool, d: bool) -> bool = {
  let (fa, fb) = f(a, b, c, d);
  let (la, lb) = lin(a, b, c, d);
  fa == la & fb == lb
}
