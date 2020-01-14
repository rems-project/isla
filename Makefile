.PHONY: all isla-sail isla-litmus isla test fmt clean

all: isla isla-litmus isla-sail

static: 
	ISLA_STATIC_Z3=y $(MAKE) 

isla-sail:
	$(MAKE) -C isla-sail isla-sail

isla-litmus:
	$(MAKE) -C isla-litmus isla-litmus

isla:
	cargo build --release

test:
	test/run_tests.rb
	$(MAKE) -C isla-lib test

fmt:
	$(MAKE) -C isla-lib fmt
	$(MAKE) -C isla-c fmt
	cargo fmt

clean:
	-$(MAKE) -C isla-sail clean
	-$(MAKE) -C isla-litmus clean
	-cargo clean
