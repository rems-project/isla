.PHONY: server server-sandboxed client client-deploy fmt clean run run-deploy serve aarch64_tests

all: server client

AARCH64_TESTS=$(LITMUS_DIR)/litmus-tests-armv8a-private/tests/non-mixed-size

aarch64_tests:
	./gather_tests.sh $(AARCH64_TESTS)/TUTORIAL/@uni client/dist/aarch64 "Tutorial" "aarch64.cat" > client/dist/aarch64.json

client:
	$(MAKE) -C client

client-deploy:
	$(MAKE) -C client deploy

server:
	$(MAKE) -C server

server-sandboxed:
	$(MAKE) -C server build-sandboxed

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
	server/target/release/islaweb-server --address "127.0.0.1:3030" --worker server/target/release/islaweb-worker --litmus-convert ../isla-litmus/isla-litmus --dist client/dist --resources .. --cache /tmp --logs /tmp

run-deploy: server client-deploy
ifneq (, $(shell which xdg-open))
	(sleep 0.5; xdg-open http://localhost:3030)&
else
	@echo "Could not launch default browser with xdg-open: server is running @ localhost:3030"
endif
	server/target/release/islaweb-server --address "127.0.0.1:3030" --worker server/target/release/islaweb-worker --litmus-convert ../isla-litmus/isla-litmus --dist client/dist --resources .. --cache /tmp --logs /tmp

serve: server
	server/target/release/islaweb-server --address "127.0.0.1:3030" --worker server/target/release/islaweb-worker --litmus-convert ../isla-litmus/isla-litmus --dist client/dist --resources .. --cache /tmp --logs /tmp
