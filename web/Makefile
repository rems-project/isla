.PHONY: server client fmt clean

all: server client

client:
	$(MAKE) -C client

server:
	$(MAKE) -C server

fmt:
	$(MAKE) -C server fmt

clean:
	-$(MAKE) -C server clean
