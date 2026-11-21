# Proof standards

These rules apply to every Lean file in this repository.

## Trust

1. No `sorry`, `admit`, `axiom`, `native_decide`, `decide +native`, `unsafe`, `implemented_by`, or `opaque`.
2. Every public theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. Each file ends with one `#print axioms <name>` line for each public theorem.
3. The open conjecture is the definition `OddPerfectConjecture` in `OddPerfect/Basic.lean`. It is never assumed, and no theorem may be stated with it as a hidden hypothesis.
4. A conditional theorem must name its hypotheses in its statement. A hypothesis must be something that is true of a real odd perfect number or is clearly marked as an unproved assumption in the docstring. Never assume something false or something equivalent to the conclusion.
5. If a target statement is false or cannot be proved, leave it out and report it. Do not weaken a statement or add hypotheses silently.

## Working in a shared checkout

1. Each contributor edits exactly one assigned file.
2. Check a file with `lake env lean OddPerfect/<File>.lean` from the repository root. Do not run `lake build`, `lake update`, `lake exe cache`, or any command that writes under `.lake`.
3. Do not run git commands. The maintainer builds, reviews, and commits.
4. Verify every mathlib lemma name by searching `.lake/packages/mathlib/Mathlib/`. Names quoted in notes or papers are leads only.
5. Import only modules that are listed as available in the task. Prefer narrow Mathlib imports; `import Mathlib` is acceptable when tactics are missing.

## Conventions

1. Use `Nat.Perfect` and the predicate `OddPerfect` from `OddPerfect/Basic.lean`. Divisor sums are written `σ 1 n` after `open ArithmeticFunction` and `open scoped ArithmeticFunction.sigma`.
2. `n.factorization p` is the exact exponent of `p` in `n`. A deduction from a component divisor sum needs the exact exponent, not just divisibility by a prime power.
3. Use exact integers and rationals. No floating point and no real number approximations.
4. Put results in `namespace OddPerfect` unless the task says otherwise. Give each public declaration a docstring.
5. American English spelling. Never use an em dash, an en dash, or a spaced hyphen as punctuation in comments or docstrings; use a period, colon, or semicolon.
6. Sanity check each statement on small cases, including edge cases such as zero, one, the prime two, and exponent zero, before proving it.
