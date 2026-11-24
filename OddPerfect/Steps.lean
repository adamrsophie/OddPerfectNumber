import OddPerfect.Basic
import OddPerfect.ClassicalInputs

/-!
# Steps open for contribution

Each definition below is a proposition, kept as a statement only: nothing in the library may
use one of them except as an explicit hypothesis. A contribution is one file
`Contributions/<Name>.lean` that proves `OddPerfect.Steps.<Name>` exactly as stated here (see
`CONTRIBUTING.md`).

Status. Proved, each in `Contributions/<Name>.lean`: `Example`, `PureRowBase`,
`TwicePrimePowerRow`, `NagellPrimePower`, `LjunggrenThreePrimePower`, `SpecialBelowRoot`.
Without a proof here: `SpecialFifthPower`, `AllRowsPrimePower`, `RowValuationTransfer`.

None of these steps settles the odd perfect number conjecture, which is open. The steps marked
"published" restate a theorem from the literature; the page reference was read, and the
statement was tested on small cases, but a restatement can still be wrong: a counterexample
is as welcome as a proof.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.Steps

/-- Format example; proved in `Contributions/Example.lean`. An odd perfect number is not
even. -/
def Example : Prop :=
  ∀ N : ℕ, OddPerfect N → ¬ 2 ∣ N

/-- Starter (published). If `σ(q ^ k)` is a power of an odd prime `p`, then `p ∤ q - 1`.
Zhao and Chen, Front. Math. 20 (2025), Lemma 2.2, third assertion. The other two assertions
are in the library (`OddPerfect/PureRows.lean`). Proved in `Contributions/PureRowBase.lean`. -/
def PureRowBase : Prop :=
  ∀ p q k s : ℕ, p.Prime → p ≠ 2 → q.Prime → 1 ≤ k → 1 ≤ s →
    σ 1 (q ^ k) = p ^ s → ¬ p ∣ q - 1

/-- Starter (published). In Euler's form `N = q ^ k * m ^ 2` with `q ∤ m`, a special exponent
other than `1` forces `q ^ 5 < 2 * m ^ 2`. Zelinsky, INTEGERS 25 (2025), A59, Proposition 11.
The library has the weaker `q < m` (`special_lt_of_exponent_ne_one`). -/
def SpecialFifthPower : Prop :=
  ∀ N q k m : ℕ, OddPerfect N → q.Prime → N = q ^ k * m ^ 2 → ¬ q ∣ m → k ≠ 1 →
    q ^ 5 < 2 * m ^ 2

/-- Medium (published). If `σ(q ^ k) = 2 * p ^ s` with `p` an odd prime, then `k = 1` and
`q ≥ 2 * p - 1`. Zhao and Chen, Front. Math. 20 (2025), Lemma 3.1. The conclusion `k = 1`
also follows from Lemma 2 of R. J. Levit, Bull. Amer. Math. Soc. 53 (1947), 392 to 396. Proved in
`Contributions/TwicePrimePowerRow.lean`. -/
def TwicePrimePowerRow : Prop :=
  ∀ p q k s : ℕ, p.Prime → p ≠ 2 → q.Prime → 1 ≤ k →
    σ 1 (q ^ k) = 2 * p ^ s → k = 1 ∧ 2 * p ≤ q + 1

/-- Starter (published). An odd perfect number `N` with special prime `q` cannot have every
divisor sum `σ(p ^ v_p(N))`, `p ≠ q`, a power of a prime while `σ(q ^ v_q(N)) / 2` is a power of
a prime too. R. J. Levit, Bull. Amer. Math. Soc. 53 (1947), 392 to 396, Theorem. The library has
a counting inequality for the case that every ordinary row is a prime power
(`card_add_inDegree_le_of_all_pure` in `OddPerfect/PureRows.lean`); with
`seven_le_card_primeFactors` (`OddPerfect/OmegaSevenFinal.lean`) it should give a short proof. -/
def AllRowsPrimePower : Prop :=
  ∀ N q : ℕ, OddPerfect N → q.Prime → Odd (N.factorization q) →
    (∀ p ∈ N.primeFactors, p ≠ q → ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) →
    ¬ ∃ r w, r.Prime ∧ σ 1 (q ^ N.factorization q) = 2 * r ^ w

/-- Medium (published). Let `p` and `q` be primes with `q` odd, `σ(q ^ x)` a power of `p` for
some `x ≥ 1`, and `q ∣ σ(p ^ c)`. Then `v_q(σ(p ^ c)) = v_q(c + 1)` when `p ≡ 1 (mod q)`, and
`v_q(σ(p ^ c)) = v_q(c + 1) + 1` otherwise. Dandapat, Hunsucker and Pomerance, Pacific J. Math.
57 (1975), 359 to 364, Lemma 2 (its two valuation statements). -/
def RowValuationTransfer : Prop :=
  ∀ p q x y c : ℕ, p.Prime → q.Prime → q ≠ 2 → 1 ≤ x → σ 1 (q ^ x) = p ^ y →
    q ∣ σ 1 (p ^ c) →
      (p % q = 1 → padicValNat q (σ 1 (p ^ c)) = padicValNat q (c + 1)) ∧
      (p % q ≠ 1 → padicValNat q (σ 1 (p ^ c)) = padicValNat q (c + 1) + 1)

/-- Hard (published, classical). The statement `OddPerfect.NagellPrimePower`: for primes
`p`, `r`, the equation `p ^ 2 + p + 1 = r ^ a` forces `a = 1`. Nagell (1921). This is one of the
two hypotheses of the theorems named `conditional_…` in `OddPerfect/ConditionalSupport.lean`.
Proved in `Contributions/NagellPrimePower.lean` (the proof is `OddPerfect/NagellPrime.lean`). -/
def NagellPrimePower : Prop :=
  OddPerfect.NagellPrimePower

/-- Hard (published, classical). The statement `OddPerfect.LjunggrenThreePrimePower`: for
primes `p`, `r`, the equation `p ^ 2 + p + 1 = 3 * r ^ a` forces `a ≤ 2`. Nagell (1921), as
quoted by Bennett, Patel and Siksek (Mathematika 63 (2017), Section 3); the name of the
definition is historical. A proof removes the other hypothesis of the theorems named
`conditional_…`. Proved in `Contributions/LjunggrenThreePrimePower.lean` (the proof is
`OddPerfect/ThreeRowPrime.lean`). -/
def LjunggrenThreePrimePower : Prop :=
  OddPerfect.LjunggrenThreePrimePower

/-- In Euler's form with special exponent `1`, `N = q * m ^ 2` and `q ∤ m`, the special prime
is below `m`. Proved in `Contributions/SpecialBelowRoot.lean` (the proof is
`OddPerfect/SpecialBelowAll.lean`, which excludes the one shape left by `special_lt_or_shape`).
The inequality is stated as proved in the literature; the header of
`OddPerfect/SpecialBelowAll.lean` lists the sources and our reading of them. -/
def SpecialBelowRoot : Prop :=
  ∀ N q m : ℕ, OddPerfect N → q.Prime → N = q * m ^ 2 → ¬ q ∣ m → q < m

end OddPerfect.Steps
