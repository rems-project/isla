default Order dec

$include <prelude.sail>
$include <float.sail>

register X : float32
register Y : float32

val prop : unit -> bool

function prop() = {
    if fp32_lteq(X, Y) then fp32_eq(Y, fp32_max(X, Y)) else true
}
