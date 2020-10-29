default Order dec

$include <prelude.sail>

val "shift_bits_left" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)

register R : bits(32)

$property
function prop() -> bool = {
  let x = R | 0x0000_FFFF;
  let y = shift_bits_left(x, 0x10);
  let z = shift_bits_left(x, 0x0000_0010);
  let w = shift_bits_left(x, 0x0000_0000_0000_0010);
  y == 0xFFFF_0000 & y == z & y == w
}
