default Order dec

$include <prelude.sail>

function lin(n: int, m: int) -> int = {
  if n < 0 & m > 0 then {
    tdiv_int(n + 1, m) - 1
  } else if n > 0 & m < 0 then {
    tdiv_int(n - 1, m) - 1
  } else {
    tdiv_int(n, m)
  }
}

function prop(n: int, m: int) -> bool = {
  fdiv_int(n,m) == lin(n,m) & fdiv_int(32,8) == lin(32,8)
}
