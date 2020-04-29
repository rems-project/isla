ifeq (, $(shell which npm))
$(error "npm is required to build the web UI for Isla")
endif

.PHONY: build deploy

all: build

build: node_modules
	npm run build

deploy: node_modules
	npm run deploy

node_modules:
	npm install
