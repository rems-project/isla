default Order dec

$include <prelude.sail>

function f((): unit) -> bool = false

$property
function prop((): unit) -> bool = {
  f()
}