
BINDIR ?= /usr/bin/
INTERFACE_FILES = $(wildcard src/*.mli)
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml)
LIBS = nums,str,unix
TARGETS = src/tstp_check.native src/tstp_check.docdir/index.html

all:
	ocamlbuild -libs $(LIBS) -tag debug $(TARGETS)

profile:
	ocamlbuild -libs $(LIBS) -tags debug,profile $(TARGETS)

clean:
	ocamlbuild -clean

tags:
	ctags $(IMPLEMENTATION_FILES) $(INTERFACE_FILES)

install: all
	cp _build/src/tstp_check.native $(BINDIR)/tstp_check

.PHONY: all profile clean tags install
