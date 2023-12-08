default Order dec

$include <prelude.sail>

function prop() -> bool = {
    let x: option(bits(4)) = if undefined then None() else Some(undefined);
    match x {
        Some(x) => x == 0xF,
        _ => true
    }
}
