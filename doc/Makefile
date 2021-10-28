.PHONY: all

all: axiomatic.html index.html translation.html

axiomatic.html: axiomatic.adoc
	asciidoctor axiomatic.adoc

translation.html: translation.adoc
	asciidoctor translation.adoc

index.html: artifact.adoc axiomatic.adoc
	cat artifact.adoc axiomatic.adoc > index.adoc
	asciidoctor index.adoc

clean:
	rm index.adoc
	rm index.html
	rm axiomatic.html
	rm translation.html

