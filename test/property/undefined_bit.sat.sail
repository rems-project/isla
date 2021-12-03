default Order dec

$include <prelude.sail>

function prop() -> bool = {
  let x: bit = undefined;
  x == bitzero
}
