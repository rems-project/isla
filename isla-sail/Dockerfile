FROM sail:nightly

RUN opam install -y dune

WORKDIR /isla-sail
COPY . /isla-sail

RUN eval `opam env` && make

ENTRYPOINT [ "/isla-sail/isla-sail" ]
