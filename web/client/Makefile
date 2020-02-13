ifeq (, $(shell which npm))
$(error "npm is required to build the web UI for Isla")
endif

.PHONY: build

all: build

build: node_modules
	npm run build

depoly: node_modules
	npm run build

node_modules:
	npm install
