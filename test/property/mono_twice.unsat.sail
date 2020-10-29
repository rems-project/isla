default Order dec

$include <prelude.sail>

$ifdef SYMBOLIC
val "monomorphize" : forall 'n, 'n > 0. bits('n) -> bits('n)
$else
function monomorphize forall 'n, 'n > 0. (bv: bits('n)) -> bits('n) = bv
$endif

val foo : bits(129) -> range(0, 1)

function foo c = {
    let nexp : bits(1) = c[0..0];
    unsigned(monomorphize(nexp))
}

val prop : bits(129) -> bool

function prop xs = {
    let exp1 = foo(xs);
    let exp2 = foo(xs);
    exp1 == exp2
}
