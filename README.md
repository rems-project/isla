# Isla

Isla is a *symbolic execution engine* for Sail, as well as an anagram.

## Build

Currently tested with (stable) Rust 1.39:
```
cargo build --release
```
We require that [z3](https://github.com/Z3Prover/z3) is available as a
shared library, however note that the version of z3 that is avaiable
in certain Ubuntu LTS versions is quite old, so you may experience
link errors in that case. The build.rs script is configured so it can
use a `libz3.so` in the root directory of this repository. If this is
done then LD_LIBRARY_PATH will also be required when executing to use
the more recend z3 library.
