default Order dec

$include <prelude.sail>

$property
function prop() -> bool = {
  let x: range(0, 3) = undefined;
  assert(x >= 0 & x <= 3);
  true
}
