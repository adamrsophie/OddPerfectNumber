import OddPerfect.SquareCycleDigit
import OddPerfect.RepunitSize
import OddPerfect.SpecialBelowCycle

/-!
# The special prime is below the root of the square part

For an odd perfect number `N = q ^ k * m ^ 2` in Euler's form (`q` prime, `q ∤ m`) the theorem
`special_lt_root` shows `q < m`, with no further hypothesis.

The proof joins three modules. `OddPerfect/SpecialBelow.lean` proves `q < m` outside one shape:
`k = 1`, `σ(p ^ e) = q` and `2 * t ^ 2 = q + 1` with `σ(t ^ 2) = p ^ e`.
`OddPerfect/SquareCycleDigit.lean` compares `(2 * t ^ 2) ^ (p - 1)` modulo `p ^ 2` in two ways and
obtains a number `J` divisible by `p`. `OddPerfect/RepunitSize.lean` shows `0 < J < p` when `J`
is not `-1`. So the shape does not occur (`noSquareCycle`).

A 2016 preprint (P. A. Brown, arXiv:1602.01591v1) states `q < m`. For `k = 1` its argument
asserts, without proof, that some component divisor sum `σ(r ^ (2 * β))` has a prime factor
other than `p`; when none has, one is in the shape excluded here. Whether a complete proof was
published elsewhere was not verified, and no claim of novelty is made. Nothing here decides the
odd perfect number conjecture, which is open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- No prime `p`, exponent `e ≥ 1` and odd `t` have `σ(t ^ 2) = p ^ e` and
`2 * t ^ 2 = 1 + σ(p ^ e)`. -/
theorem noSquareCycle : NoSquareCycle :=
  fun _ _ _ hp he ht hσ hc => square_cycle_false_of_size repunit_rows_size hp he ht hσ hc

/-- Every odd perfect number `N = q ^ k * m ^ 2` in Euler's form has `q < m`. -/
theorem special_lt_root {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : q < m :=
  special_lt_of_noSquareCycle noSquareCycle h hq hN hqm

end OddPerfect

#print axioms OddPerfect.noSquareCycle
#print axioms OddPerfect.special_lt_root
