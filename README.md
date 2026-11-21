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

Memory: the modules with large kernel checked tables (for example the `OmegaSevenRoots` files and the `CommonOneFifteen` files) each need 8 to 10 GB while they compile, and Lake compiles several modules at once. A full build fits on a machine with 24 GB with some swapping; with less memory it may be killed. Mathlib itself comes from the cache and is not rebuilt.

## Layout

| Path | Content |
| --- | --- |
| `OddPerfect/Basic.lean` | The predicate `OddPerfect` and the open conjecture, stated as a definition and never assumed. |
| `OddPerfect/Seed/` | The project's earlier starter modules: exact component forcing, valuation balance, coprime cuts, exponent pattern exclusions, third cyclotomic collisions, numeric checks. |
| `OddPerfect/*.lean` | The main library, one topic per module. |
| `OddPerfect.lean` | The root file that imports every module. |
| `AxiomGate.lean` | A check over every constant of the library: axioms, unsafe or opaque declarations, the statement of the conjecture, and coverage of every library module and tracked source file. Run with `lake env lean AxiomGate.lean` after the build. |
| `GateControls/` | Control files for the gate: one clean file that it must accept and four that it must reject, each for a stated reason. They are not part of the library and are never imported. Run with `sh GateControls/run.sh` after the build. |
| `CheckerControls/` | Regression controls for the Boolean certificate checkers: small examples that fix the value of each checker on well formed and malformed inputs. They are not part of the library and are never imported. Run with `sh CheckerControls/run.sh` after the build. |
| `scripts/` | The search and generator programs that found the certificates, trees and tables checked in the library. Nothing there is trusted; see `scripts/README.md`. |

The module list changes often. The project site lists every module and every public theorem at a stated commit: <https://adamrsophie.github.io/OddPerfectNumber/>.

## License

GNU General Public License, version 3. See `LICENSE`.
