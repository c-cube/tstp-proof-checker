tstp-proof-checker
==================

A simple OCaml proof-checker for TSTP cnf/fof derivations. It calls external
provers to check every proof step that is annotated with `thm` (other handled annotations
are `esa`, `cth` and the `file()` sources). It does not check the reduction to CNF or
the correlation between axioms declared in the derivation, and actual axioms
from a problem file, only the structure of the proof and the correctness of the
proof steps.

The derivation is accepted if it contains a step with `$false` as formula, and
if the set of steps that eventually yield this formula -- the correctness of
    which can be established using external, trusted theorem provers -- have a
[DAG](http://en.wikipedia.org/wiki/Directed_acyclic_graph) structure.

## License
Since the TPTP parser/lexer are from
[Darwin](http://combination.cs.uiowa.edu/Darwin/) which is under GPL, the
present software is also under GPLv2.
A copy of the GPLv2 is attached to the project, in the file LICENSE.

## Build
You will need ocaml (3.12 or higher works; 3.11 or lower may work, I did not test). Type

    make

It should build files (using ocamlbuild). Other dependencies are the provers used
to check proof steps by default:

- the [E](http://eprover.org) prover
- the [SPASS](http://www.spass-prover.org/) prover

## Use

Typical usage (pass `-help` as an option to get more details):

    ./tstp_check.native [options] derivation

