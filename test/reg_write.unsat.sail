default Order dec

$include <prelude.sail>

register R : bits(8)

function f() -> unit = {
  R = 0xFF;
  ()
}

function prop() -> bool = {
  R = 0x00;
  f();
  R == 0xFF
}
