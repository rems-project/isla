.PHONY: isla-sail clean

all: isla-sail

isla-sail:
	dune build --release
	cp _build/default/sail_plugin_isla.cmxs plugin.cmxs
	chmod +rwx plugin.cmxs

clean:
	-dune clean
