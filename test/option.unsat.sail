default Order dec

$include <prelude.sail>
$include <option.sail>

function prop() -> bool = {
  let x: option(bits(16)) = Some(0xFFFF);
  match x {
    Some(y) => y == 0xFFFF,
    None() => false
  }
}