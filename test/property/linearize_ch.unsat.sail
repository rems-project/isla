default Order dec

$include <prelude.sail>

overload ~ = {not_bool}

// This tests linearizing a function with roughly the same shape as the
// ConditionHolds function in ARMv8.5

val f : bool -> bool effect {rreg, undef}

register R : bool

function f cond = {
    result : bool = undefined : bool;
    result = R;
    if cond then {
        result = ~(result)
    };
    result
}

val lin : bool -> bool effect {rreg, undef}

function lin cond = {
    result : bool = undefined : bool;
    result = R;
    if cond then {
        result = ~(result)
    };
    result
}

function prop(cond: bool) -> bool = {
  f(cond) == lin(cond)
}
