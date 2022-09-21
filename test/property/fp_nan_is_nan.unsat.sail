default Order dec

$include <prelude.sail>
$include <float.sail>

val prop : unit -> bool

function prop() -> bool = {
    fp16_is_nan(fp16_nan()) & fp32_is_nan(fp32_nan()) & fp64_is_nan(fp64_nan()) & fp128_is_nan(fp128_nan())
}
