.PHONY: all isla-sail isla-litmus isla-viz isla web test fmt clean install uninstall update

all: isla isla-litmus isla-sail isla-viz

isla-sail:
	$(MAKE) -C isla-sail isla-sail

isla-litmus:
	$(MAKE) -C isla-litmus isla-litmus

isla-viz:
	$(MAKE) -C isla-visualize isla-viz

isla:
	cargo build --release

web:
	$(MAKE) -C web all

test:
	test/run_tests.rb
	$(MAKE) -C isla-lib test
	$(MAKE) -C isla-cat test

fmt:
	$(MAKE) -C isla-lib fmt
	$(MAKE) -C isla-cat fmt
	$(MAKE) -C web fmt
	cargo fmt

clean:
	-$(MAKE) -C isla-sail clean
	-$(MAKE) -C isla-litmus clean
	-$(MAKE) -C isla-cat clean
	-$(MAKE) -C isla-visualize clean
	-$(MAKE) -C web clean
	-cargo clean

install: all
	@cargo install --path .

uninstall:
	@cargo uninstall isla

update: uninstall install
