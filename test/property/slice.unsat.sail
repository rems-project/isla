default Order dec

$include <prelude.sail>

infix 4 >>
overload operator >> = {sail_shiftright}

function prop(xs: bits(32), y: range(0, 16)) -> bool = {
  let len: range(0, 16) = 16;
  assert(slice(xs, 16, len) == slice(xs >> 16, 0, len));
  assert(slice(xs, 16, len) == slice(xs >> len, 0, len));
  assert(slice(xs, y, 16) == slice(xs, y, 16));
  true
}
