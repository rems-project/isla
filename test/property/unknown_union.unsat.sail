default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

union Option_bits = {
  Bits : bits(32),
  NoBits : unit
}

register R : Option_bits

function prop() -> bool = {
    let x: Option_bits = R;
    match x {
        Bits(x) => assume(x == 0xFFFF_FFFF),
        NoBits() => (),
    };
    match x {
        Bits(x) => x == 0xFFFF_FFFF,
        NoBits() => true,
    }
}
