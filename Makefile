.PHONY: all isla-sail isla-litmus isla test fmt clean install uninstall update

all: isla isla-litmus isla-sail

isla-sail:
	$(MAKE) -C isla-sail isla-sail

isla-litmus:
	$(MAKE) -C isla-litmus isla-litmus

isla:
	cargo build --release

test:
	test/run_tests.rb
	$(MAKE) -C isla-lib test
	$(MAKE) -C isla-cat test

fmt:
	$(MAKE) -C isla-lib fmt
	$(MAKE) -C isla-cat fmt
	cargo fmt

clean:
	-$(MAKE) -C isla-sail clean
	-$(MAKE) -C isla-litmus clean
	-cargo clean

install: all
	@cargo install --path .

uninstall:
	@cargo uninstall isla

update: uninstall install
