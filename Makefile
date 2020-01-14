.PHONY: all isla-sail isla-litmus isla test fmt clean

all: isla isla-litmus isla-sail

isla-sail:
	$(MAKE) -C isla-sail isla-sail

isla-litmus:
	make -C isla-litmus isla-litmus

isla:
	cargo build --release

test:
	test/run_tests.rb
	make -C isla-lib test

fmt:
	make -C isla-lib fmt
	make -C isla-c fmt
	cargo fmt

clean:
	-make -C isla-sail clean
	-make -C isla-litmus clean
	-cargo clean
