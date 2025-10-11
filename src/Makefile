.PHONY: clean install uninstall test doc deps bap-deps

BAP_DEPS = \
	bitvec \
	bitvec-binprot \
	bitvec-order \
	bitvec-sexp \
	graphlib \
	monads \
	regular

BAP_REPO := git+https://github.com/BinaryAnalysisPlatform/opam-repository\#testing

all:
	dune build --profile=release

clean:
	dune clean

install:
	dune install

uninstall:
	dune uninstall

test:
	dune test --profile=release

doc:
	dune build @doc

deps: bap-deps
	opam install . --deps-only

bap-deps:
	for dep in $(BAP_DEPS); do \
		opam repository add $$dep $(BAP_REPO); \
	done
