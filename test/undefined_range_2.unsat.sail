default Order dec

$include <prelude.sail>

$property
function prop() -> bool = {
  let x: range(-3, -1) = undefined;
  assert(x >= -3 & x <= -1);
  true
}
