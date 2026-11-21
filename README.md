# OddPerfectNumber

A Lean 4 project on odd perfect numbers.

## Status

The existence of an odd perfect number is an open problem. This repository does not contain a proof that none exists. It contains kernel-checked necessary conditions on a hypothetical odd perfect number, and it isolates the remaining gap as an explicit statement.

Every theorem in the library compiles without `sorry`, and depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The toolchain is Lean 4.33.1. Mathlib is pinned to commit `0df444a360eaa60ab8c11dca51a86af692955474`.

## Layout

| Path | Content |
| --- | --- |
| `OddPerfect/Basic.lean` | The predicate `OddPerfect` and the open conjecture, stated as a definition and never assumed. |
| `OddPerfect/Seed/` | The project's earlier starter modules: exact component forcing, valuation balance, coprime cuts, exponent pattern exclusions, third cyclotomic collisions, numeric checks. |
| `OddPerfect/*.lean` | The main library, one topic per module. |
| `OddPerfect.lean` | The root file that imports every module. |
| `AxiomGate.lean` | A check over every constant of the library: axioms, unsafe or opaque declarations, and the statement of the conjecture. Run with `lake env lean AxiomGate.lean` after the build. |
| `scripts/` | The search and generator programs that found the certificates, trees and tables checked in the library. Nothing there is trusted; see `scripts/README.md`. |

The module list changes often. The project site lists every module and every public theorem at a stated commit: <https://adamrsophie.github.io/OddPerfectNumber/>.

## License

GNU General Public License, version 3. See `LICENSE`.
