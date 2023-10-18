.PHONY: clean install uninstall test doc

all:
	dune build --profile=release

clean:
	dune clean

install:
	dune install

uninstall:
	dune uninstall

test:
	dune test

doc:
	dune build @doc
