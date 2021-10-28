# Isla

![Ubuntu-20.04](https://github.com/rems-project/isla/workflows/Ubuntu-20.04/badge.svg)

Isla is a symbolic execution engine for
[Sail](https://github.com/rems-project/sail), as well as an anagram.

It can be used to evaluate the relaxed-memory behavior of instruction
set architectures specified in Sail, using an axiomatic memory model
specified in a subset of the cat language used by the
[herd7](http://diy.inria.fr/doc/herd.html) tools. For example:

![Message passing example](doc/MP.png?raw=true)

There is an online web interface here:

[https://isla-axiomatic.cl.cam.ac.uk](https://isla-axiomatic.cl.cam.ac.uk)

It can also be used for test generation, generating simplified
semantics (summaries) for concrete opcodes, as well as many other
possible use cases.

## Build

Currently tested with (stable) Rust 1.39:
```
cargo build --release
```

By default we require that [z3](https://github.com/Z3Prover/z3) is
available as a shared library. On Ubuntu 20.04 LTS and above this
should be available by just running `apt install libz3-dev`. However the
version of z3 that is available in older Ubuntu LTS versions (and
likely other linux distros) is quite old, so you may experience link
errors in that case. The build.rs script is configured so it can use a
`libz3.so` shared library placed in the root directory of this
repository. If this is done then `LD_LIBRARY_PATH` must also be set when
executing so that the more recent z3 library is used.

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

## Model snapshots

Isla executes IR produced by Sail. To avoid having to generate this IR,
there are pre-compiled snapshots of our ISA models available in the
following repository:

[https://github.com/rems-project/isla-snapshots](https://github.com/rems-project/isla-snapshots)

## Example

After compiling Isla, to compute the footprint of an add instruction
using the aarch64 snapshot above, the following command can be used:

```
target/release/isla-footprint -A aarch64.ir -C configs/aarch64.toml -i "add x0, x1, #3" -s
```

The arguments are the compiled Sail model, a configuration file
controlling the initial state and other options, and the instruction
we want to run. The `-s` flag performs some basic dead-code
elimination to simplify the generated footprint.

## Manual

There is a guide to the various command line options and features
[here](https://github.com/rems-project/isla/blob/master/doc/manual.adoc).

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


## Funding

This software was developed by the University of Cambridge Computer
Laboratory (Department of Computer Science and Technology), in part
under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), in part funded by
EPSRC Programme Grant EP/K008528/1 "REMS: Rigorous Engineering for
Mainstream Systems", in part funded from the European Research Council
(ERC) under the European Union’s Horizon 2020 research and innovation
programme (grant agreement No 789108, "ELVER"), in part supported by
the UK Government Industrial Strategy Challenge Fund (ISCF) under the
Digital Security by Design (DSbD) Programme, to deliver a DSbDtech
enabled digital platform (grant 105694), and in part funded by Google.

