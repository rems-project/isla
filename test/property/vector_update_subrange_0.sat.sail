default Order dec

$include <prelude.sail>

register R: bits(8)

function prop(u: bits(4)) -> bool = {
    R = [R with 3 .. 0 = 0xF];
    assert(R[3 .. 0] == 0xF);
    assert(R[0] == bitone);
    R = [R with 4 .. 1 = u];
    assert(R[0] == bitone);
    assert(R[3 .. 0] == u[2 .. 0] @ 0b0);
    true
}
