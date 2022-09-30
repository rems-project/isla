default Order dec

$include <prelude.sail>

enum E = {
  A,
  B,
  C,
  D
}

val unreachable : unit -> unit effect {escape}

function unreachable() = assert(false)

val branches : E -> bits(32) effect {escape, undef}

function branches(e) = {
  var result: bits(32) = undefined;
  match e {
    A => result = 0x0000_0000,
    B => result = 0x0000_0001,
    C => result = 0x0000_0002,
    D => unreachable(),
  };
  result
}

val prop : unit -> bool effect {escape, undef}

function prop() = {
  let e: E = undefined;
  match e {
    D => true,
    _ => {
      let x = branches(e);
      x[1..0] != 0b11
    }
  }
}
