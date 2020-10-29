default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

struct my_struct = {
  field1: int,
  field2: bits(64),
}

function prop() -> bool = {
  let x: int = undefined;
  assume(x >= 0 & x < 64);
  let y: bits(64) = undefined;
  var z: my_struct = undefined;
  z.field1 = x;
  z.field2 = y;
  z.field1 == x & z.field2 == y
}
