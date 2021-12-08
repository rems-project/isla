default Order dec

$include <prelude.sail>

union U = {
   A : bits(4),
   B : bits(8),
   C : bits(16),
}

val "ite" : forall ('a: Type). (bool, 'a, 'a) -> 'a

val one_of_3 : forall ('a: Type). ('a, 'a, 'a) -> 'a

function one_of_3(x, y, z) = {
    ite(undefined: bool, x, ite(undefined: bool, y, z))
}

function prop() -> bool = {
    let x: U = one_of_3(A(0xF), B(0xFF), C(0xFFFF));
    match x {
        A(x) => x == 0xF,
        B(x) => x == 0xFF,
        C(x) => x == 0x0000,
    }
}
