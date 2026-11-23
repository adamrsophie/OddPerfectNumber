import Mathlib.Data.Nat.Prime.Basic

/-!
# Two classical statements on `x ^ 2 + x + 1`, as named hypotheses

The two propositions below are consequences, for prime arguments, of classical theorems on the
equations `x ^ 2 + x + 1 = y ^ n` (Nagell 1921) and `x ^ 2 + x + 1 = 3 * y ^ n`
(Ljunggren 1943). Modern statements: M. A. Bennett and A. Levin, The Nagell and Ljunggren
equation via Runge's method, Monatsh. Math. 177 (2015), Proposition 1; M. A. Bennett, V. Patel
and S. Siksek, Mathematika 63 (2017), Section 3.

They are NOT proved in this library. They are definitions of propositions, so that a theorem can
take them as explicit hypotheses and be read as conditional on them. Nothing here is an axiom.
The second statement cannot be sharpened to exponent `1`: `313 ^ 2 + 313 + 1 = 3 * 181 ^ 2`.
-/

namespace OddPerfect

/-- For primes `p`, `r` and `a ≥ 1`: `p ^ 2 + p + 1 = r ^ a` forces `a = 1`. A consequence of
the classical theorem that `x ^ 2 + x + 1 = y ^ n` with `n > 1` has only the solution
`18 ^ 2 + 18 + 1 = 7 ^ 3` in positive integers. Not proved in this library. -/
def NagellPrimePower : Prop :=
  ∀ p r a : ℕ, p.Prime → r.Prime → 1 ≤ a → p ^ 2 + p + 1 = r ^ a → a = 1

/-- For primes `p`, `r` and `a ≥ 1`: `p ^ 2 + p + 1 = 3 * r ^ a` forces `a ≤ 2`. A consequence
of the classical theorem that `x ^ 2 + x + 1 = 3 * y ^ n` has no solution with `x > 1` and
`n > 2`. Not proved in this library. -/
def LjunggrenThreePrimePower : Prop :=
  ∀ p r a : ℕ, p.Prime → r.Prime → 1 ≤ a → p ^ 2 + p + 1 = 3 * r ^ a → a ≤ 2

end OddPerfect
