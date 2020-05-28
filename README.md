# Isla

Isla is a symbolic execution engine for Sail, as well as an anagram.

## Build

Currently tested with (stable) Rust 1.39:
```
cargo build --release
```

By default we require that [z3](https://github.com/Z3Prover/z3) is
available as a shared library. On Ubuntu 20.04 LTS and above this
should be available by just running `apt install z3`. However the
version of z3 that is available in older Ubuntu LTS versions (and
likely other linux distros) is quite old, so you may experience link
errors in that case. The build.rs script is configured so it can use a
`libz3.so` shared library placed in the root directory of this
repository. If this is done then `LD_LIBRARY_PATH` must also be set when
executing so that the more recent z3 library is used.

Alternatively, you can run
```
ISLA_STATIC_Z3=y cargo build --release
```
and it will build an executable with z3 statically linked, by checking
out and building an appropriate version of z3 as a static library. See
the `vendor.sh` and `build.rs` scripts for how this is done. This will
take a long time however!

Isla interprets IR produced by Sail. To generate this IR in the
correct format a tool is available in the isla-sail
directory. Building this requires various arcane OCaml incantations,
but mostly one can follow the Sail install guide
[here](https://github.com/rems-project/sail/blob/sail2/INSTALL.md),
followed by the instructions [here](isla-sail/README.md). It will only
work with the latest HEAD of the `sail2`branch in the Sail repository.

For litmus tests in the `.litmus` format used by
[herd7](https://github.com/herd/herdtools7) there is another OCaml
tool based on parsing code from herd7 itself in the isla-litmus
directory, which translates that format into a simple
[TOML](https://github.com/toml-lang/toml) representation. This OCaml
program is standalone and does not depend on any libraries, and should
build with dune >= 1.2.

## Project structure

* __isla-lib__ Is a Rust library which contains the core symbolic
  execution engine and an API to interact with it.

* __isla-axiomatic__ Contains rust code to handle various aspects
  which are specific to checking axiomatic concurrency models on top
  of isla-lib, such as parsing litmus tests, analysing instruction
  footprints, and defining a high-level interface to run litmus tests.

* __isla-cat__ Is a translator from (a fragment of) the cat memory
  models used by herdtools into SMTLIB definitions. It has its own
  README [here](isla-cat/README.md).

* __isla-litmus__ Is an (optional) OCaml utility that maps the
  `.litmus` files that herdtools uses into a format we can read.

* __isla-sail__ Is an (optional) OCaml utility that maps Sail
  specifications into the IR we can symbolically execute.

* __web__ Contains a server and client for a web interface to the
  axiomatic concurrency tool

* __src__ Defines multiple small executable utilities based on
  isla-lib
