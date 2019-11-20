default Order dec

$include <prelude.sail>

function prop(xs: bits(16)) -> bool = {
  assert((xs | xs) == xs);
  assert((xs | 0xFFFF) == 0xFFFF);
  let ys: bits(120) = undefined;
  assert((ys | ys) == ys);
  let all_ones = sail_sign_extend(0b1, 120);
  assert((ys | all_ones) == all_ones);
  true
}
