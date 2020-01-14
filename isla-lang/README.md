# isla-lang

This constructs an OCaml datatype, parser, and pretty printer for the SMT instruction-semantics description output by isla.  It uses [ott](https://github.com/ott-lang/ott) to generate those from:
```
isla_lang.ott
```
At present this needs the git HEAD of ott, assumed checked out as a sibling of isla, not the ott opam package.
