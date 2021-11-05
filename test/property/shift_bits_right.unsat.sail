default Order dec

$include <prelude.sail>

val "shift_bits_right" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)

register R : bits(32)

$property
function prop() -> bool = {
  let x = R | 0xFFFF_0000;
  let y = shift_bits_right(x, 0x10);
  let z = shift_bits_right(x, 0x0000_0010);
  let w = shift_bits_right(x, 0x0000_0000_0000_0010);
  y == 0x0000_FFFF & y == z & y == w
}
