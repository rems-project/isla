default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>
$include "memory.sail"

val cycle = monadic "cycle_count" : unit -> unit

val thread_init : unit -> unit

function thread_init() = {
    cycle()
}

val end_instr : unit -> unit

function end_instr() = {
    cycle()
}

val to_bits : forall 'w, 'w > 0. (int('w), int) -> bits('w)

function to_bits(width, i) = get_slice_int(width, i, 0)

register PC : bits(64)

register X0 : bits(64)
register X1 : bits(64)
register X2 : bits(64)
register X3 : bits(64)
register X4 : bits(64)
register X5 : bits(64)
register X6 : bits(64)
register X7 : bits(64)

val get_X : bits(3) -> bits(64)

function get_X(i) = {
    match i {
        0b000 => X0,
        0b001 => X1,
        0b010 => X2,
        0b011 => X3,
        0b100 => X4,
        0b101 => X5,
        0b110 => X6,
        0b111 => X7,
    }
}

val set_X : (bits(3), bits(64)) -> unit

function set_X(i, v) = {
    match i {
        0b000 => X0 = v,
        0b001 => X1 = v,
        0b010 => X2 = v,
        0b011 => X3 = v,
        0b100 => X4 = v,
        0b101 => X5 = v,
        0b110 => X6 = v,
        0b111 => X7 = v,
    }
}

overload X = {set_X, get_X}
