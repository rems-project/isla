default Order dec

$include <prelude.sail>

register R0 : bits(64)
register R1 : bits(64)
register R2 : bits(64)
register R3 : bits(64)

let GPRS : vector(4, dec, register(bits(64))) = [ref R3, ref R2, ref R1, ref R0]

val read_gpr = monadic "read_register_from_vector" : (bits(2), vector(4, dec, register(bits(64)))) -> bits(64)

$property
val prop : bits(2) -> bool

function prop(n) = {
    R0 = 0xABCD_ABCD_ABCD_ABCD;
    if n == 0b00 then {
        read_gpr(n, GPRS) == 0xABCD_ABCD_ABCD_ABCD
    } else {
        true
    }
}
