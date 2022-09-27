default Order dec
$include <prelude.sail>

union exception = {
  Fail : unit,
}

val f : forall 'n, 'n >= 1. (int('n)) -> (int, bits(8 * 'n))
val g : unit -> (int, bits(8))
val prop : unit -> bool

function f(n) = (1,sail_sign_extend(0x2, 8*n))
function g() = f(1)
function prop() = {
  let (x,y) = g();
  x == 1 & y == 0x02
}