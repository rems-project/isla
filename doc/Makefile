.PHONY: all copy_docs

all: manual.html axiomatic.html artifact.html translation.html

copy_docs:
	cp manual.html built_doc/manual.html
	cp axiomatic.html built_doc/axiomatic.html
	cp translation.html built_doc/translation.html

manual.html: manual.adoc
	asciidoctor manual.adoc

axiomatic.html: axiomatic.adoc
	asciidoctor axiomatic.adoc

translation.html: translation.adoc
	asciidoctor translation.adoc

artifact.html: artifact.adoc
	asciidoctor artifact.adoc

clean:
	rm manual.html
	rm artifact.html
	rm axiomatic.html
	rm translation.html
