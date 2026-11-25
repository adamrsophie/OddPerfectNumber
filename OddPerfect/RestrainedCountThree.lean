import OddPerfect.RestrainedNineteen
import OddPerfect.RestrainedTwenty

/-!
# The restrained family: the light row count that keeps the 3 adic term

The restrained family is the family of odd perfect numbers in which every prime factor other
than the special prime `q` and one further prime `r` has exponent exactly 2 (then `r = 3`).
Write `a = v_q(N)`, `E = v_3(N)`, `R = ordPrimes N q` for the prime factors other than 3 and
`q`, `O1` for the members of `R` that are 1 modulo 3, and `c3 = padicValNat 3 (a + 1)`.

`RestrainedNineteen.counts` proves `2 #R ≤ 3 #O1 + 2 a` and then uses `#O1 ≤ E`. By
`restrained_three_eq`, `E = #O1 + c3`, so the term `c3` can be kept:
`2 ω(N) + 3 c3 ≤ 3 E + 2 a + 4` and `8 ω(N) + a + 3 c3 ≤ 3 Ω(N) + 16`. With `1338852 ≤ ω(N)`
(`restrained_omega_ge_wheel_res`) this gives `10710800 + a + 3 c3 ≤ 3 Ω(N)` and
`2677700 + 3 c3 ≤ 3 E + 2 a`.

These are bounds in a restricted family only; the family is not excluded, and the odd perfect
number conjecture is open. Novelty was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

namespace RestrainedCountThree

open RestrainedSeven RestrainedFourteen RestrainedNineteen

/-- **The light row count before the last step of `counts`.** `2 #R ≤ 3 #O1 + 2 v_q(N)`, from
`#L ≤ #O1`, `#L + 2 #H ≤ 2 #O1` and `#Z ≤ v_q(N)` for the partition `R = L ∪ Z ∪ H`. A bound in
a restricted family only; the family is not excluded. -/
theorem rct_two_mul_card_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    2 * (ordPrimes N q).card ≤ 3 * (ordOne N q).card + 2 * N.factorization q := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hP1 : (lightRows N q).card + (heavyRows N q).card = (ordPrimes N q).card :=
    Finset.card_filter_add_card_filter_not (s := ordPrimes N q) (fun s => rowCount N q s ≤ 1)
  have hP2 : (qRows N q).card + (qFreeRows N q).card = (lightRows N q).card :=
    Finset.card_filter_add_card_filter_not (s := lightRows N q) (fun s => q ∣ phi3 s)
  have hL := card_free_le h hq hodd hr hrq hsq
  have hLH := free_add_two_heavy_le h hq hodd hr hrq hsq
  have hZ := card_qRows_le F
  omega

/-- `v_3(N) = #O1 + padicValNat 3 (v_q(N) + 1)`, the form of `restrained_three_eq` with `O1`
written as `ordOne N q`. -/
theorem rct_three_eq {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    N.factorization 3 = (ordOne N q).card + padicValNat 3 (N.factorization q + 1) := by
  have hO : ordOne N q = {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 3 = 1} := by
    ext p
    simp only [ordOne, ordPrimes, Finset.mem_filter, and_assoc]
  rw [hO]
  exact restrained_three_eq h hq hodd hr hrq hsq

end RestrainedCountThree

open RestrainedCountThree

/-- **Restrained family: `2 ω(N) + 3 c3 ≤ 3 v_3(N) + 2 v_q(N) + 4`**, where
`c3 = padicValNat 3 (v_q(N) + 1)`. This sharpens `restrained_two_mul_omega_le` by the term
`3 c3`. A bound in a restricted family only; the family is not excluded. Novelty was not
verified. -/
theorem restrained_two_mul_omega_add_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    2 * ω N + 3 * padicValNat 3 (N.factorization q + 1)
      ≤ 3 * N.factorization 3 + 2 * N.factorization q + 4 := by
  obtain ⟨h1, -, -⟩ := RestrainedNineteen.counts h hq hodd hr hrq hsq
  have h2 := rct_two_mul_card_le h hq hodd hr hrq hsq
  have h3 := rct_three_eq h hq hodd hr hrq hsq
  omega

/-- **Restrained family: `8 ω(N) + v_q(N) + 3 c3 ≤ 3 Ω(N) + 16`**, where
`c3 = padicValNat 3 (v_q(N) + 1)`. With `v_q(N) ≥ 1` and `c3 ≥ 0` this gives
`restrained_eight_mul_omega_le`. A bound in a restricted family only; the family is not
excluded. Novelty was not verified. -/
theorem restrained_eight_mul_omega_add_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    8 * ω N + N.factorization q + 3 * padicValNat 3 (N.factorization q + 1) ≤ 3 * Ω N + 16 := by
  obtain ⟨h1, h2, -⟩ := RestrainedNineteen.counts h hq hodd hr hrq hsq
  have h3 := rct_two_mul_card_le h hq hodd hr hrq hsq
  have h4 := rct_three_eq h hq hodd hr hrq hsq
  omega

/-- **Restrained family: `10710800 + v_q(N) + 3 c3 ≤ 3 Ω(N)`**, where
`c3 = padicValNat 3 (v_q(N) + 1)`. From `restrained_eight_mul_omega_add_le` and
`1338852 ≤ ω(N)` (`restrained_omega_ge_wheel_res`). At `v_q(N) = 1` this is the landed
`3570267 ≤ Ω(N)`; the terms in `v_q(N)` and `c3` are the gain. A lower bound in a restricted
family only; the family is not excluded. Novelty was not verified. -/
theorem restrained_three_mul_bigOmega_ge {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    10710800 + N.factorization q + 3 * padicValNat 3 (N.factorization q + 1) ≤ 3 * Ω N := by
  have hw := restrained_omega_ge_wheel_res h hq hodd hr hrq hsq
  have h8 := restrained_eight_mul_omega_add_le h hq hodd hr hrq hsq
  omega

/-- **Restrained family: `2677700 + 3 c3 ≤ 3 v_3(N) + 2 v_q(N)`**, where
`c3 = padicValNat 3 (v_q(N) + 1)`. From `restrained_two_mul_omega_add_le` and
`1338852 ≤ ω(N)` (`restrained_omega_ge_wheel_res`). At `v_q(N) = 1` (then `c3 = 0`) this is the
landed `892566 ≤ v_3(N)`; the term `3 c3` is the gain. A lower bound in a restricted family
only; the family is not excluded. Novelty was not verified. -/
theorem restrained_three_mul_three_ge {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    2677700 + 3 * padicValNat 3 (N.factorization q + 1)
      ≤ 3 * N.factorization 3 + 2 * N.factorization q := by
  have hw := restrained_omega_ge_wheel_res h hq hodd hr hrq hsq
  have h2 := restrained_two_mul_omega_add_le h hq hodd hr hrq hsq
  omega

end OddPerfect

#print axioms OddPerfect.RestrainedCountThree.rct_two_mul_card_le
#print axioms OddPerfect.RestrainedCountThree.rct_three_eq
#print axioms OddPerfect.restrained_two_mul_omega_add_le
#print axioms OddPerfect.restrained_eight_mul_omega_add_le
#print axioms OddPerfect.restrained_three_mul_bigOmega_ge
#print axioms OddPerfect.restrained_three_mul_three_ge
