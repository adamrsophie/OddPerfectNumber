import OddPerfect.Seed.Starter

/-!
# Odd perfect numbers: shared definitions

`OddPerfect N` says that `N` is odd and perfect, using mathlib's `Nat.Perfect`.
`OddPerfectConjecture` is the open statement that no such number exists. It is a
definition, never an axiom, and nothing in this project assumes it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- An odd perfect number. -/
def OddPerfect (N : ℕ) : Prop := Odd N ∧ N.Perfect

/-- The open conjecture that no odd perfect number exists. A statement only. -/
def OddPerfectConjecture : Prop := ∀ N : ℕ, ¬ OddPerfect N

namespace OddPerfect

variable {N : ℕ}

theorem odd (h : OddPerfect N) : Odd N := h.1

theorem perfect (h : OddPerfect N) : N.Perfect := h.2

theorem pos (h : OddPerfect N) : 0 < N := h.2.2

theorem ne_zero (h : OddPerfect N) : N ≠ 0 := h.pos.ne'

theorem sigma_eq (h : OddPerfect N) : σ 1 N = 2 * N := OPNStarter.sigma_eq_two_mul h.2

theorem not_two_dvd (h : OddPerfect N) : ¬ 2 ∣ N := h.odd.not_two_dvd_nat

end OddPerfect

#print axioms OddPerfect.odd
#print axioms OddPerfect.perfect
#print axioms OddPerfect.pos
#print axioms OddPerfect.ne_zero
#print axioms OddPerfect.sigma_eq
#print axioms OddPerfect.not_two_dvd
