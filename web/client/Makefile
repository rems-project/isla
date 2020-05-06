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

dist/help_standalone.html: dist/help.md
	pandoc dist/help.md -f markdown -t html -s -o dist/help_standalone.html --metadata title="Isla Help"

dist/help.html: dist/help.md
	pandoc dist/help.md -f markdown -t html -o dist/help.html

help: dist/help_standalone.html dist/help.html
