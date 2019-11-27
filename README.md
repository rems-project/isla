# Isla

Isla is a symbolic execution engine for Sail, as well as an anagram.

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
the more recent z3 library.

Isla interprets IR produced by Sail. To generate this IR in the
correct format a tool is available in the isla-sail
directory. Building this requires various arcane OCaml incantations,
but mostly one can follow the Sail install guide
[here](https://github.com/rems-project/sail/blob/sail2/INSTALL.md),
followed by the instructions [here](isla-sail/README.md).
