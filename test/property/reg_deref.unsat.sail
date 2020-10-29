
default Order dec

$include <prelude.sail>

register R1 : bool

struct S = {
  f1: bool,
  f2: int
}

register R2 : S

function prop() -> bool = {
  (*ref R1) = true;
  let x = *ref R1;
  (*ref R2).f1 = true;
  let y = (*ref R2).f1;
  x & y
}
