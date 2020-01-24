default Order dec

$include <prelude.sail>

function prop() -> bool = {
  let xs: vector(4, dec, int) = undefined;
  let xs = [xs with 0 = 3];
  xs[1] == 3
}
