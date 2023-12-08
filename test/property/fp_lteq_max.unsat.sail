default Order dec

$include <prelude.sail>
$include <float.sail>

val prop : unit -> bool

function prop() = {
    let X : float32 = undefined_float32();
    let Y : float32 = undefined_float32();
    if fp32_lteq(X, Y) then fp32_eq(Y, fp32_max(X, Y)) else true
}
