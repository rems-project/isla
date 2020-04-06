.PHONY: build build-sandboxed fmt clean

all: build

build:
	cargo build --release

build-sandboxed:
	cargo build --release --features "sandbox tls"

fmt:
	cargo fmt

clean:
	-cargo clean
