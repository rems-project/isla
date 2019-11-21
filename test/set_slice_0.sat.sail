default Order dec

$include <prelude.sail>

function set_slice_64() -> bool = {
  let xs: bits(64) = undefined;
  let ys: bits(32) = undefined;
  assert(set_slice_bits(64, 32, xs, 0, ys)[31 .. 0] == ys);
  assert(set_slice_bits(64, 32, xs, 16, ys)[31 + 16 .. 16] == ys);
  true
}

function set_slice_128() -> bool = {
  let xs: bits(128) = undefined;
  let ys: bits(32) = undefined;
  assert(set_slice_bits(128, 32, xs, 0, ys)[31 .. 0] == ys);
  assert(set_slice_bits(128, 32, xs, 16, ys)[31 + 15 .. 15] == ys);
  true
}

function set_slice_256() -> bool = {
  let xs: bits(256) = undefined;
  let ys: bits(32) = undefined;
  assert(set_slice_bits(256, 32, xs, 0, ys)[31 .. 0] == ys);
  assert(set_slice_bits(256, 32, xs, 16, ys)[31 + 16 .. 16] == ys);
  true
}

function prop() -> bool =
  set_slice_64() & set_slice_128() & set_slice_256()
