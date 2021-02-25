
# Overview

# Rust API documentation

API documentation for the latest version published on
[crates.io](https://crates.io/crates/isla-lib) is available on
[docs.rs](https://docs.rs/).

Local documentation can be generated and viewed via:

```
cargo doc --open
```

# Tool options

## Shared options

All the Isla executables share some common options, which are described below:

- `-A <file.ir>` specify a Sail architecture as a `.ir` file. See
  [here](https://github.com/rems-project/isla-snapshots) for
  pre-compiled versions of our various Sail architectures.

- `-C <file.toml>` specify a configuration file for an architecture. The `configs`
  sub-directory of this repository contains various example
  configurations.
  
- `-T <n>` use this many worker threads. Defaults to the number of
  available CPU cores.
  
- `-I <register = value>` set the initial value of a register at the beginning of time,
  before any Sail initialisation code occurs

- `-R <register = value>` set a register value after Sail initialisation occurs.

- `-D <flags>` set debugging flags. For example, `-D f` will print information
  about forks (places where control flow diverges) in the symbolic
  execution. The various options are:
  
  - `f` Print information about control flow forks
  
  - `m` Print information about memory accesses
  
  - `l` Print information while compiling litmus tests (isla-axiomatic specific)
  
  - `p` Print probe information (see `--probe` flag)
  
  The above options can be passed together, e.g. `-D fmp`
  
- `--probe <function id>` Will print information when calling or
  returning from the specified function, provided the `-D p` flag is
  set.
  
- `--debug-id` Sometimes the `--probe` flag will display identifiers as
  interned symbols (which are just unsigned 32-bit numbers). This
  option takes such a symbol number and prints it's original Sail
  name, before exiting immediately.
  
- `--help` Print usage information for the command
  
- `--verbose` Print extra information during execution

- `-L` Linearise a function. See the function linearisation section of this document.

- `--test-linearize` After linearising a function, using the SMT
  solver to check the linearised version is equivalent to the
  original.

## isla-footprint

`isla-footprint` prints simplified instruction opcode summaries and dependency information, e.g.

```
$ target/release/isla-footprint -A aarch64.ir -C configs/aarch64.toml -i "add x0, x1, #3" -s
opcode: #x91000c20
Execution took: 80ms
(trace
  (declare-const v7 (_ BitVec 32))
  (assert (= (bvor #b0 ((_ extract 0 0) (bvlshr (bvor (bvand v7 #xfffffffe) #x00000001) #x00000000))) #b1))
  (branch-address #x0000000010300000)
  (declare-const v3370 (_ BitVec 64))
  (define-const v3371 v3370)
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1066 128))
  (write-reg |__unconditional| nil true)
  (read-reg |__v85_implemented| nil false)
  (read-reg |R1| nil v3371)
  (define-const v3457 (bvadd ((_ extract 63 0) ((_ zero_extend 64) v3371)) #x0000000000000003))
  (write-reg |R0| nil v3457))
```

The `-i` option specifies an instruction which is compiled to a single
concrete opcode using the assembler specified in the configuration
file. The `-x` option can be used to pass a hexadecimal opcode
directly rather than relying on an assembler. This hexadecimal opcode
can either be little or big endian, which is controlled by the `-e`
option.

The `-s` flag tells the tool to apply some basic simplification rules
to the output, without which it can be extremely verbose.

This tool prints the instruction summary in a S-expression format
based on [SMTLIB](http://smtlib.cs.uiowa.edu/), which contains an
ordinary SMT formula built from `declare-const`, `define-const`, and
`assert` commands, as well as _effects_ such as `read-reg` and
`write-reg` above that denote which parts of the SMT formula
correspond to various actions taken by the Sail model.

The various effects are:

- `branch <counter> <variable> <sail location>` denotes a symbolic
  execution control flow split. The arguments are a counter that is
  incremented every control flow fork, the symbolic (boolean) variable
  that caused control flow to split, and the location of the control
  flow construct in the original Sail source code.

- `read-reg <name> <accessors> <value>` a register read, arguments are
  the name of the register, any accessors e.g. `.EL` in `PSTATE.EL`,
  and the value read.
  
- `write-reg <name> <accessors> <value>` a register write. Arguments
  are the same as for read, except `<value>` is the value written.

- `read-mem <return value> <read kind> <address> <bytes> <tag value>`
  is a memory read. Arguments are the value read from memory, the read
  kind which is a member of the sail `read_kind` enumeration, the
  address, the number of bytes read, and a tag value (for CHERI tagged
  memory).

- `write-mem <return value> <write kind> <address> <data> <bytes> <tag
  value>`. Arguments are the same as for memory read except there is
  an extra `<data>` argument specifiying the data written. The return
  value is a boolean specifying if the write succeeded. The write kind
  is a member of the Sail `write_kind` enumeration.

- `branch-address <address>` An event announcing the address of a branch
  instruction. Used when computing control dependencies in the
  concurrency model.
  
- `barrier <barrier kind>` A barrier event. The barrier kind is a
  member of the Sail `barrier_kind` enumeration.
  
- `cache-op <cache op kind> <address>` A cache maintenance
  operation. The cache op kind is a member of the Sail `cache_op_kind`
  enumeration.
  
- `mark-reg <registers> <string>` An event that can be used to tag
  some registers with additional instrumentation. In Sail this would
  be generated by a function call of the form:
  
  ```
  __mark_register(ref R0, "mark")
  ```
  
  which would create an event marking R0 with the string
  `"mark"`. There are other Sail functions that allow marking multiple
  registers simultaneously if needed. Currently this information is
  used to provide extra hints to the footprint dependency analysis
  stage in the concurrency model.
  
- `cycle` Denotes the start and end of a fetch-decode-execute
  cycle. The first cycle is reserved for initialisation.
  
- `instr <opcode>` Announces each fetched opcode.

If the configuration file enables the MMU, then we need valid page
tables in memory. The `--identity-map <virtual address>` flag creates
a valid identity mapping and page tables for ARMv8. It can be passed
multiple times to create mappings for multiple virtual addresses.

The `-d` option changes the behaviour of the command to instead print
dependency information rather than trace summaries. For example:

```
$ target/release/isla-footprint -A aarch64.ir -C configs/aarch64.toml -i "add x0, x1, #3" -d
opcode: #x91000c20
Execution took: 71ms
Footprint:
  Memory write:
  Memory read:
  Memory address:
  Branch address:
  Register reads: R1
  Register writes: R0
  Register writes (ignore):
  Is store: false
  Is load: false
  Is exclusive: false
  Is branch: false
```

## isla-axiomatic

`isla-axiomatic` allows running concurrency litmus tests w.r.t. an
axiomatic memory model specified in the cat language used by
[herdtools](https://github.com/herd/herdtools7).

For example, the following command will test whether the LB test is
allowed by the aarch64.cat memory model (both of which are included in
our web interface, hence the filepaths in the command).

```
target/release/isla-axiomatic -A aarch64.ir -C configs/aarch64.toml -m web/client/dist/aarch64.cat -t web/client/dist/aarch64/LB.toml
```

The `--view` flag will cause the output to be displayed as a graphviz
generated graph using `xdg-open` to open an image viewer. The flag
`--dot <path>` will instead generate the dot files used by graphviz in
the directory specified by `<path>`.

For the above example this will generate a picture

![LB test output](LB.png?raw=true)

isla-axiomatic allows comparing against the output from RMEM or Herd
using the `--refs` flag which allows supplying reference results.

The `-e` flag forces isla-axiomatic to generate all possible executions.

A separate configuration can be passed for dependency analysis using
the `--footprint-config` flag.

### Instruction-fetch and page tables support

The `--ifetch` flag causes isla-axiomatic to generate instruction
fetch events, as per our [ESOP2020
paper](https://link.springer.com/chapter/10.1007%2F978-3-030-44914-8_23).

The `--armv8-page-tables` causes ARMv8 pages tables to be created and
maps the code from the litmus tests into the page tables.

### Batch use

The executable has various options that allow batch use, allowing
setups where we run a certain number of tests concurrently with each
test having access to a certain number of cores. There are scripts in
the root of this repository such as `test_litmus_aarch64.sh` which
demonstrate how this is used.

### Web Interface

Rather than running isla-axiomatic locally, an online version is
available [here](https://isla-axiomatic.cl.cam.ac.uk/). The web
interface can also be run using a local web server, see the Makefile
in the `web` sub-directory for how this is done. Note that while we try
to support MacOS for the rust library and associated executable tools
the web interface only works under Linux.

## Function linearisation

Isla always creates a new task when we hit a branch, and does not ever
merge these tasks at join points. This is a good strategy for
instruction semantics, as it simplifies the symbolic execution engine
significantly, but it does mean some code can cause unnecessary
branching. To avoid this there is a static rewrite that can take a
function with if statements and rewrite it into a _linear_ form, for
example:

```
var x = 2;
if undefined {
  x = x + 1
} else {
  x = x + 2
};
return x
```

would become:

```
let x0 = 2;
let b = undefined;
let x1 = x0 + 1;
let x2 = x0 + 2;
let x3 = ite(b, x1, x2);
return x3
```

Ordinarily the `if` statement (with a symbolic argument generated by
the `undefined`) in the original Sail would cause the control flow to
split and two symbolic execution tasks would be created for each
branch. In the second version, both branches of the if are evaluated
and we will have a single SMT problem with an internal `ite` SMT
expression.

Some caveats: This rewrite causes both branches of any if statement to
be executed, so this rewrite can change the observable side effects of
a function when applied to non-pure functions. More subtly, Sail has
flow-sensitive typing so the types in one branch may be unsound in the
case where the other branch is taken - this sounds bad, but is
actually ok, provided we make sure we define each primitive to return
dummy values when it is called on values which would ordinarily be
forbidden by its type (if this is not the case, then we just get an
error rather than any kind of unsoundness). Finally, this rewrite does
not support functions with loops.
