default Order dec

$include <prelude.sail>
$include <float.sail>

register X : float32
register Y : float32
register Z : float32

function fp32_add_with_rm(x : float32, y : float32) -> float32 = fp32_add(round_toward_zero(), x, y)

overload operator + = {fp32_add_with_rm}

val prop : unit -> bool

function prop() = {
    fp32_eq((X + Y) + Z, X + (Y + Z))
}
