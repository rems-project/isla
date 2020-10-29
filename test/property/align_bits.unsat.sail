default Order dec

$include <prelude.sail>

val __monomorphize = "monomorphize" : forall 'n, 'n >= 0. bits('n) -> bits('n)

val "assume" : bool -> unit

val arm_align_int : forall ('x : Int) ('y : Int). (int('x), int('y)) -> int
val arm_align_bits : forall ('N : Int) ('y : Int). (bits('N), int('y)) -> bits('N)

function arm_align_int(x, y) = y * tdiv_int(x, y)
function arm_align_bits(x, y) = get_slice_int('N, arm_align_int(unsigned(x), y), 0)

val "align_bits" : forall 'n 'm, 'n >= 0 & 'm >= 1. (bits('n), int('m)) -> bits('n)

val prop : forall 'n, 'n >= 0. bits(64) -> bool

function prop(xs) = {
  let alignment: bits(4) = undefined;
  let alignment = unsigned(__monomorphize(alignment));
  if alignment > 0 then {
    align_bits(xs, alignment) == arm_align_bits(xs, alignment)
  } else {
    true
  }
}
