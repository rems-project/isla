# isla-sail

This is a small plugin for Sail that builds instruction set
architecture specifications into a form suitable for Isla.

## Install

To build you will need the latest `sail2` from Github (not the opam
release), and then run:
```
make install
```
To build Sail and install it as an OCaml (OPAM) library. In this repostitory
one can then type:
```
make
```
Note that Sail doesn't have any kind of stable external API, so this tool is
quite liable to breakage.

## Usage

The command:
```
isla-sail <file1.sail> ... <filen.sail> -o <out>
```
will compile the provided Sail files into an `<out>.ir` file.

