.PHONY: clean install uninstall test doc deps bap-deps

BAP_DEPS = \
	bitvec \
	bitvec-binprot \
	bitvec-order \
	bitvec-sexp \
	graphlib \
	monads \
	regular

BAP_REPO := git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing
REPOADD := opam repository --all-switches --set-default add

all:
	dune build

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

deps: bap-deps
	opam install . --deps-only

bap-deps:
	for dep in $(BAP_DEPS); do \
		$(REPOADD) $$dep $(BAP_REPO); \
	done
