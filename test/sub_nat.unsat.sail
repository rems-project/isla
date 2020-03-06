default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

function prop() -> bool = {
  let x: nat = undefined;
  let y: nat = undefined;
  assert(sub_nat(x, y) >= 0 & sub_nat(x, x) == 0);
  assume(y >= x);
  assert(sub_nat(x, y) >= 0);
  true
}