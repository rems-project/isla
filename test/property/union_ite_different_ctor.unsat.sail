default Order dec

$include <prelude.sail>

val "ite" : forall ('a: Type). (bool, 'a, 'a) -> 'a

function prop() -> bool = {
    let x: option(bits(32)) = ite(undefined: bool, Some(0xFFFF_FFFF), None());
    match x {
        Some(x) => x == 0xFFFF_FFFF,
        None() => true,
    }
}
