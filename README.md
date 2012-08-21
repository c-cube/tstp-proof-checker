tstp-proof-checker
==================

a simple OCaml proof-checker for TSTP cnf/fof derivations. It calls external provers to check every proof step. It does not check the reduction to CNF or the correlation between
axioms declared in the derivation, and actual axioms from a problem file, only the
structure of the proof and the correctness of the proof steps.

## License
Since the TPTP parser/lexer are from
[Darwin](http://combination.cs.uiowa.edu/Darwin/) which is under GPL, the
present software is also under GPLv2.

A copy of the GPLv2 is attached to the project, in the file LICENSE.

## Build
You will need ocaml (3.12 or higher works; 3.11 or lower may work, I did not test). Type

    make

It should build files (using ocamlbuild).


## Use

Typical usage:

    ./checker.sh derivation
