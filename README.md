# OddPerfectNumber

A Lean 4 project on odd perfect numbers.

## Status

The existence of an odd perfect number is an open problem. This repository does not contain a proof that none exists. It contains kernel-checked necessary conditions on a hypothetical odd perfect number, and it isolates the remaining gap as an explicit statement.

Every theorem in the library compiles without `sorry`, and depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Contributing

Anyone can prove one of the posted steps in `OddPerfect/Steps.lean` and submit it as one Lean file. The nine steps posted so far are all proved; their proofs are in `Contributions/`. See [CONTRIBUTING.md](CONTRIBUTING.md) and <https://adamrsophie.github.io/OddPerfectNumber/join.html>. No step settles the conjecture.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The toolchain is Lean 4.36.0. Mathlib is pinned to commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (its tag `v4.36.0`).

Memory: the modules with large kernel checked tables (for example the `OmegaSevenRoots` files and the `CommonOneFifteen` files) each need 8 to 10 GB while they compile, and Lake compiles several modules at once. A full build fits on a machine with 24 GB with some swapping; with less memory it may be killed. Mathlib itself comes from the cache and is not rebuilt.

## Layout

| Path | Content |
| --- | --- |
| `OddPerfect/Basic.lean` | The predicate `OddPerfect` and the open conjecture, stated as a definition and never assumed. |
| `OddPerfect/Seed/` | The project's earlier starter modules: exact component forcing, valuation balance, coprime cuts, exponent pattern exclusions, third cyclotomic collisions, numeric checks. |
| `OddPerfect/*.lean` | The main library, one topic per module. |
| `OddPerfect.lean` | The root file that imports every module. |
| `AxiomGate.lean` | A check over every constant of the library: axioms, unsafe or opaque declarations, the statement of the conjecture, and coverage of every library module and tracked source file. Run with `lake env lean AxiomGate.lean` after the build. |
| `StatementGate.lean` | The headline theorems restated with the definitions of mathlib and the predicate `OddPerfect`, each proved by reference to the library theorem, and a check that no restatement mentions another project definition outside a short allowed list. Run with `lake env lean StatementGate.lean` after the build. |
| `GateControls/` | Control files for the gates: clean files that they must accept and files that they must reject, each for a stated reason, a control for the source scan `scripts/Controls/source_scan.py`, and a declaration that the kernel never checked, which the replay with `leanchecker` must reject. They are not part of the library and are never imported. Run with `sh GateControls/run.sh` after the build. |
| `CheckerControls/` | Regression controls for the Boolean certificate checkers: small examples that fix the value of each checker on well formed and malformed inputs, checked against the inventory `manifest.txt`, and the five generated checks of the largest prime factor search. They are not part of the library and are never imported. Run with `sh CheckerControls/run.sh` after the build: it checks the inventory and compiles `Controls.lean`, and only counts the five generated checks; `sh CheckerControls/run.sh full` also compiles them, which needs about 15 GB of memory. |
| `OddPerfect/Steps.lean` | Statements posted for contribution, as definitions of type `Prop`. Nothing in the library uses one except as an explicit hypothesis. |
| `Contributions/` | One file per proved step, compiled outside the library. `Example.lean` shows the format. |
| `ContributionGate.lean` | The check of the contributed proofs: each proves exactly its step, with the three standard axioms only. Run by `scripts/Controls/contribution_gate.sh`. |
| `scripts/` | The search and generator programs that found the certificates, trees and tables checked in the library. Nothing there is trusted; see `scripts/README.md`. |

The module list changes often. The project site lists every module and every public theorem at a stated commit: <https://adamrsophie.github.io/OddPerfectNumber/>.

## Direct import changes

Code that imported a module for one of these declarations must now import the new place:

* `exists_two_primeFactors_gt` (two distinct prime factors above `58`) is now in
  `OddPerfect.SecondLargestPrimeTwo`, derived from `exists_two_primeFactors_gt_72`; it is no
  longer in `OddPerfect.SecondLargestPrime`.
* The nine modules `SecondLargestPrimeData1 .. 9` were replaced by
  `SecondLargestPrimeFastData1 .. 9`, checked with `SLP.runF`
  (`OddPerfect.SecondLargestPrimeFast`).
* `FamInst.hrows115` moved from `OddPerfect.CommonOneFifteenData` to the final module
  `OddPerfect.CommonOneFifteen`.
* `exists_primeFactor_gt_100000` was replaced by `exists_primeFactor_gt_200000`
  (`OddPerfect.LargestPrimeFactorThreeFinal`); the modules `LargestPrimeFactorTwoData`,
  `LargestPrimeFactorTwoRows1 .. 9` and `LargestPrimeFactorTwoFinal` were removed.
  `OddPerfect.LargestPrimeFactorTwo` (the checker `LPF2`) remains.

## License

GNU General Public License, version 3. See `LICENSE`.
