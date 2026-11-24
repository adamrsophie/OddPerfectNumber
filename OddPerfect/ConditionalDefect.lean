import OddPerfect.ZeroDefect

/-!
# The conditional bound with the positive defect: `5 * T + 5`

Let `N` be an odd perfect number with special prime `q` of exponent `a`, and let `T` be the total
excess. `ConditionalSupport` proves `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 6` under the hypotheses
`NagellPrimePower` and `LjunggrenThreePrimePower`, from at most one escape row. `ZeroDefect`
proves that the support defect is positive for `q ≡ 1 (mod 3)`. Together they give `5 * T + 5`
under the same two hypotheses, for every special prime.

The two hypotheses are hypotheses of the theorems, not axioms. Since this module was written
the bound `5 * T + 5` was proved without them (`OddPerfect/EscapeRowUnique.lean`), and both
hypotheses became theorems (`OddPerfect/NagellPrime.lean`, `OddPerfect/ThreeRowPrime.lean`).
The theorems here are kept for reference. Published bounds that carry the special
exponent are stronger for small exponents. The total excess is not bounded, and the odd perfect
number conjecture is open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (proved in later
modules): for every special prime `q`, `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5`. -/
theorem conditional_card_primeFactors_add_two_mul_le_five_excess_add_five
    (hN : NagellPrimePower) (hL : LjunggrenThreePrimePower) {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 := by
  have hq4 := (special_mod_four h hq hodd).1
  have hq0 : q % 3 ≠ 0 := fun h0 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with hq3 | hq3
  · have hI := card_primeFactors_add_two_mul_add_defect_eq h hq hodd
    have hZ := one_le_supportDefect h hq hodd hq3
    have hH := conditional_card_escapeRows_le_one hN hL (N := N) hq
    omega
  · exact card_primeFactors_add_two_mul_le_five_excess_add_five h hq hodd hq3

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (proved in later
modules): for every special prime, `ω(N) ≤ 5 * T + 5`. -/
theorem conditional_card_primeFactors_le_five_excess_add_five (hN : NagellPrimePower)
    (hL : LjunggrenThreePrimePower) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.primeFactors.card ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 := by
  have := conditional_card_primeFactors_add_two_mul_le_five_excess_add_five hN hL h hq hodd
  omega

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (proved in later
modules): for every special prime, `N < 2 ^ 4 ^ (5 * T + 5)`. -/
theorem conditional_lt_two_pow_four_pow_excess_add_five (hN : NagellPrimePower)
    (hL : LjunggrenThreePrimePower) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N < 2 ^ 4 ^ (5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5) :=
  (lt_two_pow_four_pow h).trans_le (Nat.pow_le_pow_right two_pos
    (Nat.pow_le_pow_right (by norm_num)
      (conditional_card_primeFactors_le_five_excess_add_five hN hL h hq hodd)))

end OddPerfect

#print axioms OddPerfect.conditional_card_primeFactors_add_two_mul_le_five_excess_add_five
#print axioms OddPerfect.conditional_card_primeFactors_le_five_excess_add_five
#print axioms OddPerfect.conditional_lt_two_pow_four_pow_excess_add_five
