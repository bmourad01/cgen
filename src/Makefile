.PHONY: clean install uninstall test doc deps

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

deps:
	opam repository --all-switches --set-default add bitvec "git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing"
	opam repository --all-switches --set-default add bitvec-binprot "git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing"
	opam repository --all-switches --set-default add bitvec-order "git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing"
	opam repository --all-switches --set-default add bitvec-sexp "git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing"
	opam repository --all-switches --set-default add graphlib "git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing"
	opam repository --all-switches --set-default add monads "git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing"
	opam repository --all-switches --set-default add regular "git+https://github.com/BinaryAnalysisPlatform/opam-repository#testing"
	opam install . --deps-only
