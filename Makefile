.PHONY: all isla-sail isla-litmus isla test clean

all: isla isla-litmus isla-sail

isla-sail:
	make -C isla-sail isla-sail

isla-litmus:
	make -C isla-litmus isla-litmus

isla:
	cargo build --release

test:
	test/run_tests.rb
	make -C isla-smt test
	make -C isla-lib test

clean:
	-make -C isla-sail clean
	-make -C isla-litmus clean
	-cargo clean
