default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

union exception = {
    Abort : unit
}

val cycle = monadic "cycle_count" : unit -> unit

val thread_init : unit -> unit

function thread_init() = {
    cycle()
}

val start_instr : bits(32) -> unit

function start_instr(opcode) = sail_instr_announce(opcode)

val end_instr : unit -> unit

function end_instr() = {
    cycle()
}

val to_bits : forall 'w, 'w > 0. (int('w), int) -> bits('w)

function to_bits(width, i) = get_slice_int(width, i, 0)

val bits64_identity : bits(64) -> bits(64)
function bits64_identity(bv) = bv

instantiation sail_mem_read with
    'pa = bits(64),
    'translation_summary = unit,
    'arch_ak = unit,
    'abort = unit,
    pa_bits = bits64_identity

val plain_read_request : forall 'n, 'n > 0. (bits(64), int('n)) -> Mem_read_request('n, 64, bits(64), unit, unit)

function plain_read_request(pa, size) = struct {
    access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
    va = None(),
    pa = pa,
    translation = (),
    size = size,
    tag = false
}

val throw_abort : forall 'n, 'n > 0. result((bits('n), option(bool)), unit) -> bits('n)

function throw_abort(r) = match r {
    Ok((bv, _)) => bv,
    Err(_) => throw Abort(),
}

instantiation sail_mem_write with
    'pa = bits(64),
    'translation_summary = unit,
    'arch_ak = unit,
    'abort = unit,
    pa_bits = bits64_identity

enum Barrier = Barrier1 | Barrier2

instantiation sail_barrier with
    'barrier = option(Barrier)

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

val main : unit -> unit

function main() = ()

val decode : bits(32) -> unit

val run_instr : bits(32) -> unit

function run_instr(opcode) = {
    start_instr(opcode);
    decode(opcode);
    end_instr();
}

val isla_footprint : bits(32) -> bool

function isla_footprint(opcode) = {
   thread_init();
   start_instr(opcode);
   decode(opcode);
   true
}
