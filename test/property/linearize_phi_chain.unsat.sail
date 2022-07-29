default Order dec

$include <prelude.sail>

function lin(b1: bool, b2: bool) -> int = {
  var x : int = 1;
  var y : int = 0;
  if b1 then {
    if b2 then {
      x = 2;
    };
    y = 10;
  };
  x + y
}

function f(b1: bool, b2: bool) -> int = {
  var x : int = 1;
  var y : int = 0;
  if b1 then {
    if b2 then {
      x = 2;
    };
    y = 10;
  };
  x + y
}

function prop(b1: bool, b2: bool) -> bool = {
  f(b1, b2) == lin(b1, b2) & f(true, true) == lin(true, true)
}
