default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

// Test various permutations of vector_access where both arguments are symbolic
function va_ss() -> bool = {
  let n: int = undefined;
  assume(0 <= n & n < 64);
  assert(0 <= n & n < 64);
  let xs: bits(64) = undefined;
  let test1: bool = if xs == 0xFFFF_FFFF_FFFF_FFFF then {
    xs[n] == bitone
  } else {
    true
  };
  let ys: bits(512) = undefined;
  let test2: bool = if ys == sail_sign_extend(0b1, 512) then {
    ys[n] == bitone
  } else {
    true
  };
  let zs: bits(128) = undefined;
  let test3: bool = if zs == sail_sign_extend(0b1, 128) then {
    zs[n] == bitone
  } else {
    true
  };
  test1 & test2 & test3
}

function va_sc() -> bool = {
  let n: int = 32;
  assert(0 <= n & n < 64);
  let xs: bits(64) = undefined;
  let test1: bool = if xs == 0xFFFF_FFFF_FFFF_FFFF then {
    xs[n] == bitone
  } else {
    true
  };
  let ys: bits(512) = undefined;
  let test2: bool = if ys == sail_sign_extend(0b1, 512) then {
    ys[n] == bitone
  } else {
    true
  };
  let zs: bits(128) = undefined;
  let test3: bool = if zs == sail_sign_extend(0b0, 128) then {
    zs[n] == bitone
  } else {
    true
  };
  test1 & test2 & test3
}

function va_cs() -> bool = {
  let n: int = undefined;
  assume(0 <= n & n < 32);
  assert(0 <= n & n < 32);
  let xs: bits(32) = 0xFFFF_FFFF;
  xs[n] == bitone
}

function va_cc() -> bool = {
  assert(0xF[0] == bitone);
  true
}

function prop() -> bool = va_ss() & va_sc() & va_cs() & va_cc()
