SRC := ./src/

.PHONY: build clean install uninstall test doc deps indent status-clean check-style

all: install

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

indent:
	sh tools/ocp-indent-all.sh

status-clean:
	git diff --quiet --exit-code

check-style: status-clean indent
	git diff --exit-code
