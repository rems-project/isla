.PHONY: libisla doc fmt

libisla:
	cargo build --release

fmt:
	cargo fmt

test/test: libisla
	LD_LIBRARY_PATH=.. $(CC) -o test/test test/test.c -I src/ -L. -l:target/release/libisla.so

doc:
	doxygen
	$(MAKE) -C latex
