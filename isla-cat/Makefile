.PHONY: test fmt clean

all: cat2smt

test:
	cargo test

fmt:
	cargo fmt

clean:
	-cargo clean
	-rm -f cat2smt

cat2smt:
	cargo build --release
	cp target/release/cat2smt .
