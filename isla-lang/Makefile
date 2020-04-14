.PHONY: all main lib opam pdf clean realclean install uninstall


all: main lib opam

main:
	@dune build main.exe

lib:
	@dune build isla_lang.a

opam:
	@dune build @install

pdf: isla_lang_quotiented.pdf isla_lang_unquotiented.pdf

isla_lang_quotiented.pdf: isla_lang.ott
	@dune build $@

isla_lang_unquotiented.pdf: isla_lang.ott
	@dune build $@

clean:
	@dune clean

realclean: clean
	@rm -rf *.pdf

install: opam
	@dune install

uninstall: opam
	@dune uninstall

format:
	@dune build @fmt
