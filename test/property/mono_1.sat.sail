default Order dec

$include <prelude.sail>

val "monomorphize" : forall 'n, 'n >= 0. bits('n) -> bits('n)

function prop() -> bool = {
  let xs: bits(1) = undefined;
  let ys: bits(1) = monomorphize(xs);
  ys == 0b1
}
