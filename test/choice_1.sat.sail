default Order dec

$include <prelude.sail>

overload ~ = {not_bool}

function prop(x: bool, y: bool) -> bool = {
  if x then {
    if y then {
      x
    } else {
      ~(y)
    }
  } else if y then {
    false
  } else {
    ~(x) & ~(y)
  }
}
