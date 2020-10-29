default Order dec

$include <prelude.sail>

struct T = {
 z: bits(8),
 w: bits(8)
}

struct S = {
  x: T,
  y: bits(8)
}

function prop() -> bool = {
  var s: S = struct { x = struct { z = 0xAB, w = 0xCD }, y = 0xEF };
  assert(s.x.z == 0xAB);
  s.x.z = 0xBA;
  assert(s.x.z == 0xAB);
  true
}
