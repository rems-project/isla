.PHONY: all clean

all: isla

isla: src/*.rs Cargo.toml build.rs
	cargo build --release
	cp target/release/isla .

clean:
	-cargo clean
	-rm -f isla
