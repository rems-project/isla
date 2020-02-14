.PHONY: isla-viz clean

all: isla-viz

isla-viz:
	dune build main.exe
	cp _build/default/main.exe isla-viz

clean:
	-dune clean
