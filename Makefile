SRC := ./src/

.PHONY: build	clean	install uninstall test doc deps
.PHONY: ocaml-indent clang-indent indent status-clean check-style

all: install

export UPDATE_EXPECT

build:
	$(MAKE) -C $(SRC)

clean:
	$(MAKE) clean -C $(SRC)

install: build
	$(MAKE) install -C $(SRC)

uninstall:
	$(MAKE) uninstall -C $(SRC)

test:
	$(MAKE) test -C $(SRC)

doc:
	$(MAKE) doc -C $(SRC)

deps:
	$(MAKE) deps -C $(SRC)

ocaml-indent:
	sh tools/ocp-indent-all.sh

clang-indent:
	sh tools/clang-format-all.sh

indent: ocaml-indent clang-indent

status-clean:
	git diff --quiet --exit-code

check-style: status-clean indent
	git diff --exit-code
