.PHONY: clean install uninstall test doc check-docs deps

UPDATE_EXPECT ?= 0

PROFILE = release
ifeq ($(DEBUG),1)
	PROFILE = dev
endif

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

doc:
	dune build @doc --profile=$(PROFILE)

check-docs: doc
	sh ../tools/check-docs.sh _build/default/_doc/_html

deps:
	opam install . --deps-only

compile_commands.json:
	dune rules | dune-compiledb
