.PHONY: all isla-sail isla-litmus isla web test fmt clean install uninstall update

all: isla

isla:
	cargo build --release

check:
	cargo check --release

isla-sail:
	$(MAKE) -C isla-sail isla-sail

isla-litmus:
	$(MAKE) -C isla-litmus isla-litmus

web:
	$(MAKE) -C web all

test:
	test/run_tests.rb --config configs/riscv64.toml
	$(MAKE) -C isla-lib test
	$(MAKE) -C isla-cat test
	$(MAKE) -C isla-elf test
	$(MAKE) -C isla-axiomatic test

test-github:
	test/run_tests.rb --config configs/riscv64_ubuntu.toml
	$(MAKE) -C isla-lib test
	$(MAKE) -C isla-cat test
	$(MAKE) -C isla-axiomatic test

fmt:
	$(MAKE) -C isla-lib fmt
	$(MAKE) -C isla-cat fmt
	$(MAKE) -C isla-axiomatic fmt
	$(MAKE) -C isla-mml fmt
	$(MAKE) -C isla-elf fmt
	$(MAKE) -C web fmt
	cargo fmt

clean:
	-$(MAKE) -C isla-sail clean
	-$(MAKE) -C isla-litmus clean
	-$(MAKE) -C isla-cat clean
	-$(MAKE) -C isla-elf clean
	-$(MAKE) -C web clean
	-cargo clean

install: all
	@cargo install --locked --path .

uninstall:
	@cargo uninstall isla

update: uninstall install
