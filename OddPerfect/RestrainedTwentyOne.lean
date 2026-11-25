import OddPerfect.RestrainedNineteen
import OddPerfect.RestrainedTwenty

/-!
# The restrained family: the light row counts with the residue wheel bound

The restrained family is the family of odd perfect numbers in which every prime factor other
than the special prime `q` and one further prime `r` has exponent exactly 2 (then `r = 3`).

This module joins two results. `RestrainedNineteen` proves `2 ω(N) ≤ 3 v_3(N) + 2 v_q(N) + 4`
and `8 n ≤ 3 Ω(N) + 15` for every `n ≤ ω(N)`. `RestrainedTwenty` proves `1338852 ≤ ω(N)`.
Together they give `3570267 ≤ Ω(N)`, and `892566 ≤ v_3(N)` when `v_q(N) = 1`.

These are lower bounds in a restricted family only. The family is not excluded, and the
statement that no odd perfect number exists is not proved. Ochem and Zelinsky (2026 preprint,
arXiv 2607.19746) state the far larger bound `v_3(N) ≥ 23,000,000,000` in this family; it is not
proved here. Novelty was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

/-- **Restrained family: `Ω(N) ≥ 3570267`.** From `8 n ≤ 3 Ω(N) + 15` with `n = 1338852`, the
bound of `restrained_omega_ge_wheel_res`. A bound in a restricted family only; the family is
not excluded. Novelty was not verified. -/
theorem restrained_bigOmega_ge_wheel_res {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    3570267 ≤ Ω N := by
  have hw := restrained_omega_ge_wheel_res h hq hodd hr hrq hsq
  have h8 := restrained_eight_mul_le_of_le_omega h hq hodd hr hrq hsq hw
  omega

/-- **Restrained family with special exponent 1: `v_3(N) ≥ 892566`.** From
`2 ω(N) ≤ 3 v_3(N) + 2 v_q(N) + 4` and `1338852 ≤ ω(N)`. A bound in a restricted family only;
the family is not excluded. Novelty was not verified. -/
theorem restrained_three_ge_wheel_res_of_exponent_one {N q r : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ha : N.factorization q = 1) : 892566 ≤ N.factorization 3 := by
  have hw := restrained_omega_ge_wheel_res h hq hodd hr hrq hsq
  have h2 := restrained_two_mul_omega_le h hq hodd hr hrq hsq
  omega

end OddPerfect

#print axioms OddPerfect.restrained_bigOmega_ge_wheel_res
#print axioms OddPerfect.restrained_three_ge_wheel_res_of_exponent_one
