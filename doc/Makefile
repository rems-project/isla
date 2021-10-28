.PHONY: all

all: axiomatic.html artifact.html translation.html

axiomatic.html: axiomatic.adoc
	asciidoctor axiomatic.adoc

translation.html: translation.adoc
	asciidoctor translation.adoc

artifact.html: artifact.adoc
	asciidoctor artifact.adoc

clean:
	rm artifact.html
	rm axiomatic.html
	rm translation.html

