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
| `OddPerfect/Seed/` | Starting modules: exact-component forcing, valuation balance, coprime cuts, exponent-pattern exclusions, third cyclotomic collisions, numeric checks. |
| `OddPerfect/Basic.lean` | The predicate `OddPerfect` and the open conjecture as a definition. |
