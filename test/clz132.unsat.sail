default Order dec

$include <prelude.sail>

val "count_leading_zeros" : forall 'n, 'n > 0. bits('n) -> {'zeros, 0 <= 'zeros <= 'n. int('zeros)}

val "assume" : bool -> unit

function prop1() -> bool = {
  let xs: bits(132) = undefined;
  assume(xs == 0x0_0000_0000_0000_0000_0000_0000_0000_0000);
  count_leading_zeros(xs) == 132
}

function prop2() -> bool = {
  let xs: bits(132) = undefined;
  assume(xs == 0x0_0000_0070_0000_0001_00E0_0000_0000_0000);
  count_leading_zeros(xs) == 29
}

function prop() -> bool = prop1() & prop2()
