default Order dec

$include <prelude.sail>

function prop() -> bool = {
  let x: list(int) = [|1, 2, 3|];
  match x {
    hd :: tl => {
      hd == 1
    },
    [||] => false
  }
}