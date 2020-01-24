default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

function prop(x: int) -> bool = {
    assert(set_slice_int(2, 15, 1, 0b00) == 9);
    assume(x >= 0);
    assert(set_slice_int(1, x, 0, 0b1) >= 1);
    assert(set_slice_int(1, x, 1, 0b1) >= 2);
    assert(set_slice_int(1, x, 2, 0b1) >= 4);
    assert(set_slice_int(3, x, 0, 0b101) >= 5);
    assert(set_slice_int(3, x, 2, 0b101) >= 20);
    assert(set_slice_int(3, x, 4, 0b101) >= 80);
    true
}
