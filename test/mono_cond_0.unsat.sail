default Order dec

$include <prelude.sail>

val "monomorphize" : forall 'n, 0 < 'n <= 64. bits('n) -> bits('n)

register R : bool

function prop() -> bool = {
  R = false;
  var zs: bits(1) = undefined;
  if R then {
    let xs: bits(1) = undefined;
    let ys: bits(1) = monomorphize(monomorphize(monomorphize(xs)));
    zs = ys;
    assert(false)
  } else {
    zs = 0b0
  };
  zs == 0b0
}
