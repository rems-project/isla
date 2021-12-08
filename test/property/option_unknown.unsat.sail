default Order dec

$include <prelude.sail>

function prop() -> bool = {
    let x: option(bits(4)) = undefined;
    match x {
        Some(x) if x == 0xF => x == 0xF,
        _ => true
    }
}
