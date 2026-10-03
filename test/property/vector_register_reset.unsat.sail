default Order dec
$include <prelude.sail>
$include <isla.sail>

register R: vector(16, bool)

function prop() -> bool = {
  isla_reset_registers();
  R[3]
}
