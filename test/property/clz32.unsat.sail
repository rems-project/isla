default Order dec

$include <prelude.sail>

val "count_leading_zeros" : forall 'n, 'n > 0. bits('n) -> {'zeros, 0 <= 'zeros <= 'n. int('zeros)}

val "assume" : bool -> unit

function prop1() -> bool = {
  let xs: bits(32) = undefined;
  assume(xs == 0x0000_0000);
  count_leading_zeros(xs) == 32
}

function prop2() -> bool = {
  let xs: bits(32) = undefined;
  assume(xs == 0xF000_0000);
  count_leading_zeros(xs) == 0
}

function prop3() -> bool = {
  let xs: bits(32) = undefined;
  assume(xs == 0x0000_0F00);
  count_leading_zeros(xs) == 20
}

function prop4() -> bool = {
  let xs: bits(32) = undefined;
  assume(xs == 0x0000_0700);
  count_leading_zeros(xs) == 21
}

function prop5() -> bool = {
  let xs: bits(32) = undefined;
  assume(xs == 0x0001_0000);
  count_leading_zeros(xs) == 15
}

function prop6() -> bool = {
  let xs: bits(32) = undefined;
  assume(xs == 0x0000_8000);
  count_leading_zeros(xs) == 16
}

function prop() -> bool = prop1() & prop2() & prop3() & prop4() & prop5() & prop6()
