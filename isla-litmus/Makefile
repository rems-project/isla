.PHONY: main.native clean

all: main.native

main.native:
	ocamlbuild -plugin-tag "package(str)" -use-ocamlfind main.native

clean:
	-rm -r build_isa_models
	-ocamlbuild -clean
