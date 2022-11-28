.PHONY: all copy_docs

all: manual.html axiomatic.html artifact.html translation.html memory_model_language.html

copy_docs:
	cp manual.html built_doc/manual.html
	cp axiomatic.html built_doc/axiomatic.html
	cp translation.html built_doc/translation.html
	cp memory_model_language.html built_doc/memory_model_language.html

manual.html: manual.adoc
	asciidoctor manual.adoc

axiomatic.html: axiomatic.adoc
	asciidoctor axiomatic.adoc

translation.html: translation.adoc
	asciidoctor translation.adoc

artifact.html: artifact.adoc
	asciidoctor artifact.adoc

memory_model_language.html: memory_model_language.adoc
	asciidoctor memory_model_language.adoc

clean:
	rm manual.html
	rm artifact.html
	rm axiomatic.html
	rm translation.html
	rm memory_model_language.html
