.PHONY: build build-sandboxed fmt clean

all: build

build:
	cargo build --release

build-sandboxed:
	cargo build --release --features "sandbox https"

fmt:
	cargo fmt

clean:
	-cargo clean
