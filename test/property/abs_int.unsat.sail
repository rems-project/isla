default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

function prop() -> bool = {
  let x: int = undefined;
  assume(x < 0 & x > -1000);
  abs_int(x) > 0 & abs_int(-5) == 5
}
