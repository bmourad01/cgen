SRC := ./src/

.PHONY: build clean install uninstall test doc indent

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

indent:
	sh tools/ocp-indent-all.sh
