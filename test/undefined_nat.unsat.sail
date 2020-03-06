default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

function prop() -> bool = {
  let x: nat = undefined;
  x >= 0
}
