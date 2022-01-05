default Order dec

$include <prelude.sail>
$include <option.sail>

val always_some : unit -> option(bits(8))

function always_some() = {
  Some(0xFF)
}

val always_some_prop : (unit, option(bits(8))) -> bool

function always_some_prop(_, opt) = {
  match opt {
    Some(_) => true,
    None() => false,
  }
}

val prop : unit -> bool

function prop() = {
  match always_some() {
    Some(0xFF) => true,
    None() => false,
  }
}
