default Order dec

$include <prelude.sail>

function prop(xs: bits(16)) -> bool = {
  assert((xs & xs) == xs);
  assert((xs & 0x0000) == 0x0000);
  let ys: bits(120) = undefined;
  assert((ys & ys) == ys);
  let all_zeros = sail_zero_extend(0b0, 120);
  assert((ys & all_zeros) == all_zeros);
  true
}
