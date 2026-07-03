.PHONY: clean install uninstall test doc check-docs deps bap-deps

UPDATE_EXPECT ?= 0

PROFILE = release
ifeq ($(DEBUG),1)
	PROFILE = dev
endif

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
	dune build --profile=$(PROFILE)

clean:
	dune clean

install:
	dune install

uninstall:
	dune uninstall

test:
	UPDATE_EXPECT=$(UPDATE_EXPECT) dune test --profile=$(PROFILE)

# XXX: workaround for incremental doc builds becoming stale
doc:
	-find _build -name '*.odoc' -delete
	-find _build -name '*.odocl' -delete
	rm -rf _build/default/_doc
	dune build @doc --profile=$(PROFILE)

check-docs: doc
	sh ../tools/check-docs.sh _build/default/_doc/_html

deps: bap-deps
	opam install . --deps-only

bap-deps:
	for dep in $(BAP_DEPS); do \
		opam repository add $$dep $(BAP_REPO); \
	done

compile_commands.json:
	dune rules | dune-compiledb
