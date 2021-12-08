default Order dec

$include <prelude.sail>

struct S = {
    field1: bits(32),
    field2: bits(32),
}

val "ite" : forall ('a: Type). (bool, 'a, 'a) -> 'a

function prop() -> bool = {
    let s1: S = undefined;
    let s2: S = undefined;
    let s3 = ite(undefined: bool, s1, s2);
    s3.field1 == s3.field2
}
