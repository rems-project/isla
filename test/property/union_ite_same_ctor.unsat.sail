default Order dec

$include <prelude.sail>

val "ite" : forall ('a: Type). (bool, 'a, 'a) -> 'a

function prop() -> bool = {
    let x: option(bits(32)) = ite(undefined: bool, Some(0xFFFF_FFFF), Some(0x0000_0000));
    match x {
        Some(x) => x == 0xFFFF_FFFF | x == 0x0000_0000,
        None() => true,
    }
}
