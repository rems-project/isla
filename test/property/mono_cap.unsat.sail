default Order dec

$include <prelude.sail>

val "monomorphize" : forall 'n, 'n > 0. bits('n) -> bits('n)

let HI = 6
let LO = 1

function get6(bv: bits(129)) -> range(0, 63) = {
  unsigned(bv[HI..LO])
}

function get6mono(bv: bits(129)) -> range(0, 63) = {
  unsigned(monomorphize(bv[HI..LO]))
}

function prop(bv: bits(129)) -> bool = {
  let 'n = get6mono(bv);
  if get6(bv) > 50 then {
    return true
  };
  assert(constraint(0 <= 'n <= 50));
  return true
}
