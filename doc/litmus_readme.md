# Running litmus tests

## Sail

Follow the instructions
[here](https://github.com/rems-project/sail/blob/sail2/INSTALL.md) to
install Sail. Currently you will need the latest development version
of Sail, so follow the instructions at the bottom of the file.

## Isla

While the main core of isla is written in Rust and can be built simply by using
```
cargo build --release
```
with stable rust 1.39 or greater, there are also two components that use OCaml.

The first is `isla-sail` which uses Sail as an OCaml library to build
sail specifications into the intermediate representation (IR) we use
for symbolic evaluation. Installing Sail via the opam pin based method
above should have set this up correctly.

The only other dependency for this is dune, which is the most commonly
used build system for OCaml projects (Sail itself still uses the older
ocamlbuild). Type
```
make isla-sail
```
To build this

The second is `isla-litmus`, which is a wrapper around the herdtools
OCaml code used to parse litmus files. It reads the litmus files and
outputs them in a simpler format that can be used by other tools
without custom parsing, by using a common configuration file format,
[TOML](https://github.com/toml-lang/toml), which is somewhat similar
to JSON but designed to be read and written by humans.

This should also only require dune itself to build. Once it has been
built the `isla-litmus` executable (which will be built in
`isla/isla-litmus`) should be placed somewhere in $PATH so it can be
found later by the script that runs litmus tests.

## Sail-ARM

Next the Sail-arm repository need to be compiled into the IR
representation described above.

https://github.com/rems-project/sail-arm

First we need to switch to the `symbolic` branch of the repository,
then run `make aarch64.ir` from within the `arm-v8.5-a`
subdirectory. This currently assumes that the isla and sail-arm
repositories are checked out next to each other in the same directory.

## Running litmus tests

There is a script in the root of the isla repostory
[test_litmus.sh](../test_litmus.sh) which runs the tests in the
litmus-tests-armv8a-private repository and compares the results with
the model references for RMEM in the
litmus-tests-regression-machinery. Currently this assumes that those
litmus repositories and this repository are also checked out next to
each other in the same repository.

Currently this script is configured for our 72-thread server, running
36 tests in parallel with two threads each. It will likely need to be
configured for other hardware.

Isla will cache footprint results in the $TMPDIR directory, as well as
other intermediate files. For performance, this directory should be
mounted as tmpfs (so it resides in memory).

