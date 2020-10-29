default Order dec

$include <prelude.sail>

val "count_leading_zeros" : forall 'n, 'n > 0. bits('n) -> {'zeros, 0 <= 'zeros <= 'n. int('zeros)}

val "assume" : bool -> unit

function prop1() -> bool = {
  let xs: bits(5) = undefined;
  assume(xs == 0b00000);
  count_leading_zeros(xs) == 5
}

function prop2() -> bool = {
  let xs: bits(5) = undefined;
  assume(xs == 0b11111);
  count_leading_zeros(xs) == 0
}

function prop3() -> bool = {
  let xs: bits(5) = undefined;
  assume(xs == 0b00010);
  count_leading_zeros(xs) == 3
}

function prop4() -> bool = {
  let xs: bits(5) = undefined;
  assume(xs == 0b01010);
  count_leading_zeros(xs) == 1
}

function prop() -> bool = prop1() & prop2() & prop3() & prop4()
