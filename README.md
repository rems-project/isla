# Isla

![Ubuntu-20.04](https://github.com/rems-project/isla/actions/workflows/ubuntu_22_04.yml/badge.svg)

Isla is a symbolic execution engine for
[Sail](https://github.com/rems-project/sail), 
and a tool (sometimes known more specifically as `isla-axiomatic`) 
that uses that to evaluate the relaxed-memory behavior of instruction
set architectures (ISAs) specified in Sail, including Armv8-A and RISC-V, with respect to arbitrary axiomatic memory models
specified in a subset of the cat language used by the
[herd7](http://diy.inria.fr/doc/herd.html) tools. For example, for a classic message-passing test on Armv8-A, Isla finds the following candidate execution satisfying the final condition of the test, with the instruction behaviour taken from symbolic evaluation of the full Armv8-A ISA definition.


![Message passing example](doc/MP.png?raw=true)

There is an online web interface for `isla-axiomatic` here:

[https://isla-axiomatic.cl.cam.ac.uk](https://isla-axiomatic.cl.cam.ac.uk)

Isla has also been used for test generation, generating simplified
semantics (summaries) for concrete opcodes, and there are many other
possible use cases.

## Build

Get Rust and its dependencies, probably the easiest is with [rustup](https://rustup.rs/).

Then build isla and friends, currently tested with (stable) Rust 1.70:
```
cargo build --release
```

### Z3

By default we require that [z3](https://github.com/Z3Prover/z3)
is available as a shared library.

If running isla-axiomatic, `z3` must also be available on the `PATH`.

It should be available in the usual places, currently tested with Z3 4.12.6:
```
apt install libz3-dev  # on Ubuntu 20.04 LTS and later
opam install z3 # alterantively, opam usually has an up-to-date version
```

However the version of z3 that is available in older Ubuntu LTS versions
(and likely other linux distros) is quite old,
so you may experience link errors in that case.
The build.rs script is configured so it can use a `libz3.so` shared library
placed in the root directory of this repository.
If this is done then `LD_LIBRARY_PATH` must also be set when
executing so that the more recent z3 library is used.
In those cases a version of z3 can be obtained from the sources
[https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3).

## Model snapshots

Isla executes IR produced by Sail. To avoid having to generate this IR,
there are pre-compiled snapshots of our ISA models available in the
following repository:

[https://github.com/rems-project/isla-snapshots](https://github.com/rems-project/isla-snapshots)

To generate this IR in the correct format a tool is available in the
isla-sail directory. Building this requires various arcane OCaml
incantations, but mostly one can follow the Sail install guide
[here](https://github.com/rems-project/sail/blob/sail2/INSTALL.md),
followed by the instructions [here](isla-sail/README.md). It will only
work with the latest HEAD of the `sail2`branch in the Sail repository.

## Litmus test format conversion

For litmus tests in the `.litmus` format used by
[herd7](https://github.com/herd/herdtools7) and [rmem](http://www.cl.cam.ac.uk/users/pes20/rmem) there is another OCaml
tool based on parsing code from herd7 in the isla-litmus
directory, which translates that format into a simple
[TOML](https://github.com/toml-lang/toml) representation. This OCaml
program is standalone and does not depend on any libraries, and should
build with dune >= 1.2.


## Example

After compiling Isla, to compute the footprint of an add instruction
using the ARM 9.4 snapshot above, the following command can be used:

```
target/release/isla-footprint -A armv9p4.ir -C configs/armv9p4.toml -i "add x0, x1, #3" -s
```

The arguments are the compiled Sail model, a configuration file
controlling the initial state and other options, and the instruction
we want to run. The `-s` flag performs some basic dead-code
elimination to simplify the generated footprint. We get a trace
of the instruction as a mix of SMTLIB definitions of the semantics,
interspersed with statements describing the input and outputs of the
instruction, here `read-reg` and `write-reg`.

```
  (declare-const v3371 (_ BitVec 64))
  (read-reg |R1| nil v3371)
  (define-const v3457 (bvadd ((_ extract 63 0) ((_ zero_extend 64) v3371)) #x0000000000000003))
  (write-reg |R0| nil v3457))
```

## Example: Running isla-axiomatic

To run a relaxed litmus test,
first ensure an up-to-date snapshot is obtained from [isla-snapshots](https://github.com/rems-project/isla-snapshots)

A quick and simple test is just to run the Arm `MP+dmb.sy+ctrl` litmus test,
against the same model the web interface uses:

```
target/release/isla-axiomatic -A /path/to/isla-snapshots/armv8p5.ir -C configs/armv8p5.toml -m web/client/dist/aarch64.cat web/client/dist/aarch64/MP+dmb.sy+ctrl.toml
```

For more information, see the full [documentation](https://github.com/rems-project/isla/blob/master/doc/axiomatic.adoc).

## Manual

There is a guide to the various Isla command line options and features
[here](https://github.com/rems-project/isla/blob/master/doc/manual.adoc).

The `isla-axiomatic` tool has a seperate manual
[here](https://github.com/rems-project/isla/blob/master/doc/axiomatic.adoc),
and a guide to its support for virtual memory and address translation
[here](https://github.com/rems-project/isla/blob/master/doc/translation.adoc).

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


## People

- [Alasdair Armstrong](http://alasdair.io/") (University of Cambridge)
- [Brian Campbell](http://homepages.inf.ed.ac.uk/bcampbe2/) (University of Edinburgh)
- [Ben Simner](https://www.cl.cam.ac.uk/~bs630/) (University of Cambridge)
- [Thibaut Perami](https://www.cst.cam.ac.uk/people/tp496) (University of Cambridge)
- [Peter Sewell](https://www.cl.cam.ac.uk/~pes20/) (University of Cambridge)

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
enabled digital platform (grant 105694), in part funded by an Arm
iCASE doctoral studentship (18000005, Simner), and in part funded by
Google.
