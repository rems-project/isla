.PHONY: isla-litmus clean

all: isla-litmus

isla-litmus:
	dune build main.exe
	cp _build/default/main.exe isla-litmus

clean:
	-dune clean
