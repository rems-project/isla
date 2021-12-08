default Order dec

$include <prelude.sail>

union U = {
   A : bits(4),
   B : bits(8),
   C : bits(16),
   D : bits(32),
}

val "ite" : forall ('a: Type). (bool, 'a, 'a) -> 'a

val ite_wrapper : (bool, U, U) -> U

function ite_wrapper(b, x, y) = ite(b, x, y)

val one_of_4 : (U, U, U, U) -> U

function one_of_4(w, x, y, z) = {
    ite_wrapper(undefined: bool, ite_wrapper(undefined: bool, w, x), ite_wrapper(undefined: bool, y, z))
}

function prop() -> bool = {
    let x: U = one_of_4(A(0xF), B(0xFF), C(0xFFFF), D(0xFFFF_FFFF));
    match x {
        A(x) => x == 0xF,
        B(x) => x == 0xFF,
        C(x) => x == 0xFFFF,
        D(x) => x == 0xFFFF_FFFF,
    }
}
