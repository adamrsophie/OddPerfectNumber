import Mathlib.Data.Nat.Prime.Basic

/-!
# Two classical statements on `x ^ 2 + x + 1`, as named hypotheses

The two propositions below are consequences, for prime arguments, of classical theorems on the
equations `x ^ 2 + x + 1 = y ^ n` and `x ^ 2 + x + 1 = 3 * y ^ n`. M. A. Bennett, V. Patel and
S. Siksek (Mathematika 63 (2017), Section 3) credit both to T. Nagell (Norsk Mat. Forenings
Skr. 1(2) (1921), 1 to 14): the first for exponents `n` that are not a power of 3, the second
for `n > 2`. The first equation with `n` a power of 3 (where `18 ^ 2 + 18 + 1 = 7 ^ 3`) is not
covered by that quotation; it is usually credited to Ljunggren (1943), which was not checked on
the source. A modern statement of both: M. A. Bennett and A. Levin, The Nagell and Ljunggren
equation via Runge's method, Monatsh. Math. 177 (2015), Proposition 1. The name
`LjunggrenThreePrimePower` below is kept for compatibility; by the quotation above the theorem
behind it is Nagell's.

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
`n > 2` (Nagell 1921, as quoted by Bennett, Patel and Siksek; see the module header). Not proved
in this library. -/
def LjunggrenThreePrimePower : Prop :=
  ∀ p r a : ℕ, p.Prime → r.Prime → 1 ≤ a → p ^ 2 + p + 1 = 3 * r ^ a → a ≤ 2

end OddPerfect
