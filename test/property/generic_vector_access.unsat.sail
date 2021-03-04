default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

register foo : vector(10, dec, int)

val prop : forall 'n, 'n >= 0 & 'n < 10. int('n) -> bool

function prop(n) = {
  assume('n >= 0 & 'n < 10);
  assert('n >= 0 & 'n < 10);
  foo[n] = n;
  return foo[n] == n
}

