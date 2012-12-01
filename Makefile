
INTERFACE_FILES = $(wildcard src/*.mli)
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml)
LIBS = nums,str,unix

all:
	ocamlbuild -libs $(LIBS) -tag debug src/tstp_check.native

profile:
	ocamlbuild -libs $(LIBS) -tags debug,profile src/tstp_check.native

tests: all
	ocamlbuild -libs $(LIBS) -I src tests/tstp_check.native

doc:
	ocamlbuild src/main.docdir/index.html

clean:
	ocamlbuild -clean

tags:
	ctags $(IMPLEMENTATION_FILES) $(INTERFACE_FILES)

.PHONY: all profile clean tags doc tests
