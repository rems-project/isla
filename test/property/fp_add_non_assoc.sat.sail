default Order dec

$include <prelude.sail>
$include <float.sail>


function fp32_add_with_rm(x : float32, y : float32) -> float32 = fp32_add(round_toward_zero(), x, y)

overload operator + = {fp32_add_with_rm}

val prop : unit -> bool

function prop() = {
    var X : float32 = undefined_float32();
    var Y : float32 = undefined_float32();
    var Z : float32 = undefined_float32();
    fp32_eq((X + Y) + Z, X + (Y + Z))
}
