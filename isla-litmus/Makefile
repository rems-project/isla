.PHONY: main.native clean

all: isla-litmus

isla-litmus:
	ocamlbuild -use-ocamlfind main.native
	cp main.native isla-litmus

clean:
	-ocamlbuild -clean
