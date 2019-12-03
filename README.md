# Isla

Isla is a symbolic execution engine for Sail, as well as an anagram.

## Build

Currently tested with (stable) Rust 1.39:
```
cargo build --release
```

By default we require that [z3](https://github.com/Z3Prover/z3) is available as a shared library,
however note that the version of z3 that is available in certain Ubuntu LTS versions (and likely
other linux distros) is quite old, so you may experience link errors in that case. The build.rs
script is configured so it can use a `libz3.so` placed in the root directory of this repository. If
this is done then LD_LIBRARY_PATH must also be set when executing so that the more recent z3 version
is used.

Alternatively, you can run
```
ISLA_STATIC_Z3=y cargo build --release
```
and it will build an executable with z3 statically linked, by checking out and building an
appropriate version of z3 as a static library. See the `vendor.sh` and `build.rs` scripts for how
this is done.

Isla interprets IR produced by Sail. To generate this IR in the correct format a tool is available
in the isla-sail directory. Building this requires various arcane OCaml incantations, but mostly one
can follow the Sail install guide
[here](https://github.com/rems-project/sail/blob/sail2/INSTALL.md), followed by the instructions
[here](isla-sail/README.md).

## Project structure

* __isla-smt__ Is a Rust library which wraps the low-level `z3-sys` crate that provides one-to-one
  access to the Z3 C API. It provides a SMTLIB like interface to the underlying solver (and could in
  theory be adapted to use other solvers as sub-processes, rather than the Z3 C library). This is
  separate because it contains all the unsafe code that wraps the C interface. It additionally logs
  the interactions with the SMT solver, so that we can replay Z3 states in other threads, and
  analyze runs.

* __isla-lib__ Is a Rust library which contains the core symbolic execution engine and an API to
  interact with it.

* __isla-litmus__ Is an (optional) OCaml utility that maps the `.litmus` files that herdtools uses
  into a format we can read.

* __isla-sail__ Is an (optional) OCaml utility that maps Sail specifications into the IR we can
  symbolically execute.
