# isla-cat 🐱

isla-cat is a Rust library for converting the cat files used by
(herd)[https://github.com/herd/herdtools7] to describe hardware
relaxed memory models into a form suitable for use with SMT solvers
such as Z3 and CVC4.

It also contains a small binary `cat2smt` which translates such cat
files on the command line.

Documentation for the cat language can be found
(here)[http://diy.inria.fr/doc/herd.html].

# Limitations

cat has some features which are not easily translatable into
SMT. Roughly-speaking, this supports the fragment of cat that defines
sets and relations over events. More formally the fragment of cat we
support is defined by the grammar:

```
expr ::= 0
       | id
       | expr^+ | expr^* | expr? | expr^-1
       | ~expr
       | [expr]
       | expr | expr
       | expr ; expr | expr \ expr | expr & expr | expr * expr
       | expr expr
       | let id = expr in expr
       | ( expr )

binding ::= id = expr

id ::= [a-zA-Z_][0-9a-z_.-]*

def ::= let [rec] binding { and binding }
      | let funbinding
      | include string
      | show expr as id
      | show id {, id }
      | unshow id {, id }
      | [ flag ] check expr [ as id ]

funbinding ::= id ( id ) = expr

check ::= checkname | ~checkname

checkname ::= acyclic | irreflexive | empty
```
