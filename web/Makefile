.PHONY: server client fmt clean run

all: server client

client:
	$(MAKE) -C client

server:
	$(MAKE) -C server

fmt:
	$(MAKE) -C server fmt

clean:
	-$(MAKE) -C server clean

run: server client
ifneq (, $(shell which xdg-open))
	(sleep 0.5; xdg-open http://localhost:3030)&
else
	@echo "Could not launch default browser with xdg-open: server is running @ localhost:3030"
endif
	server/target/release/islaweb-server --worker server/target/release/islaweb-worker --dist client/dist --resources .. --cache /tmp
