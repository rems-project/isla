.PHONY: all isla-sail isla clean

all: isla-sail isla

isla-sail:
	make -C isla-sail isla-sail

isla:
	cargo build --release

clean:
	-make -C isla-sail clean
	-cargo clean
