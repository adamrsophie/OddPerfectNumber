import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# When half of `σ(p ^ 2) + 1` or `σ(p ^ 4) + 1` is a square

For an odd prime `p` this module solves `σ(p ^ k) + 1 = 2 z ^ 2` for `k = 2` and `k = 4`.

* `eq_five_of_sigma_prime_sq_succ_eq_two_mul_sq`: `p ^ 2 + p + 2 = 2 z ^ 2` forces `p = 5`
  (and indeed `25 + 5 + 2 = 2 * 16`).
* `sigma_prime_fourth_succ_ne_two_mul_sq`: `p ^ 4 + p ^ 3 + p ^ 2 + p + 2 = 2 z ^ 2` has no
  solution.

Both proofs reduce modulo `p`: `2 z ^ 2 ≡ 2`, so `z ≡ ±1 (mod p)`, and after replacing `z` by
`-z` we may write `z = k p + 1`. Dividing the equation by `p` leaves an equation in `k` and `p`
that is settled by sign arguments; in the quartic case one more reduction modulo `p` gives
`4 k = i p + 1` with `i` odd, and then
`(8 - i ^ 2) p ^ 2 + (8 - 2 i) p + (7 - 8 i) = 0`, which has no solution with `p ≥ 3`.

These statements concern `(σ(p ^ k) + 1) / 2`; they are not the statements of the module
`HalfPowerNotSquare`. Their novelty has not been verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace HalfSigmaSquare

/-- If `2 z ^ 2 = 2 + p c` for an odd prime `p`, then `z ≡ 1` or `z ≡ -1 (mod p)`. -/
private lemma dvd_sub_or_add {p : ℕ} {z c : ℤ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 2 * z ^ 2 = 2 + p * c) : (p : ℤ) ∣ z - 1 ∨ (p : ℤ) ∣ z + 1 := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hd : (p : ℤ) ∣ 2 * ((z - 1) * (z + 1)) := ⟨c, by linear_combination h⟩
  rcases hpi.dvd_or_dvd hd with h2 | h2
  · exfalso
    have : p ∣ 2 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  · exact hpi.dvd_or_dvd h2

/-- The quadratic case for `z ≡ 1 (mod p)`. -/
private lemma quad_core {p : ℕ} {z : ℤ} (hp3 : 3 ≤ p) (hz : (p : ℤ) ∣ z - 1)
    (h : (p : ℤ) ^ 2 + p + 2 = 2 * z ^ 2) : p = 5 := by
  obtain ⟨k, hk⟩ := hz
  have hz' : z = p * k + 1 := by linarith
  subst hz'
  have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hp0 : (p : ℤ) ≠ 0 := by omega
  have hE : (p : ℤ) + 1 = 2 * p * k ^ 2 + 4 * k := by
    have h0 : (p : ℤ) * ((p + 1) - (2 * p * k ^ 2 + 4 * k)) = 0 := by linear_combination h
    have := (mul_eq_zero.mp h0).resolve_left hp0
    linarith
  rcases lt_trichotomy k (-1) with hk1 | rfl | hk1
  · have ha : (0 : ℤ) ≤ 2 * k ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ p - 3 by linarith) ha,
      mul_nonneg_of_nonpos_of_nonpos (show k + 2 ≤ 0 by omega) (show k ≤ 0 by omega)]
  · have : (p : ℤ) = 5 := by linarith
    exact_mod_cast this
  · rcases (show k = 0 ∨ 1 ≤ k by omega) with rfl | hk1
    · linarith
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ p by linarith)
        (show (0 : ℤ) ≤ k ^ 2 - 1 by nlinarith)]

/-- The quartic case for `z ≡ 1 (mod p)`. -/
private lemma quart_core {p : ℕ} {z : ℤ} (hp3 : 3 ≤ p) (hz : (p : ℤ) ∣ z - 1)
    (h : (p : ℤ) ^ 4 + p ^ 3 + p ^ 2 + p + 2 = 2 * z ^ 2) : False := by
  obtain ⟨k, hk⟩ := hz
  have hz' : z = p * k + 1 := by linarith
  subst hz'
  have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hp0 : (p : ℤ) ≠ 0 := by omega
  have hE : (p : ℤ) ^ 3 + p ^ 2 + p + 1 = 2 * p * k ^ 2 + 4 * k := by
    have h0 : (p : ℤ) * ((p ^ 3 + p ^ 2 + p + 1) - (2 * p * k ^ 2 + 4 * k)) = 0 := by
      linear_combination h
    have := (mul_eq_zero.mp h0).resolve_left hp0
    linarith
  obtain ⟨i, hki⟩ : ∃ i : ℤ, 4 * k = p * i + 1 :=
    ⟨p ^ 2 + p + 1 - 2 * k ^ 2, by linear_combination (-1 : ℤ) * hE⟩
  have hQ : (8 - i ^ 2) * p ^ 2 + (8 - 2 * i) * p + (7 - 8 * i) = 0 := by
    have h0 : (p : ℤ) * ((8 - i ^ 2) * p ^ 2 + (8 - 2 * i) * p + (7 - 8 * i)) = 0 := by
      linear_combination (8 : ℤ) * hE + ((4 * k + p * i + 1) * p + 8) * hki
    exact (mul_eq_zero.mp h0).resolve_left hp0
  rcases Int.even_or_odd i with ⟨c, hc⟩ | ⟨c, hc⟩
  · have h2 : 4 * k = 2 * (p * c) + 1 := by rw [hki, hc]; ring
    generalize (p : ℤ) * c = w at h2
    omega
  rcases (show c ≤ -3 ∨ 2 ≤ c ∨ (-3 < c ∧ c < 2) by omega) with hc3 | hc3 | ⟨hc1, hc2⟩
  · have hi : i ≤ -5 := by omega
    have hA : (0 : ℤ) ≤ (i ^ 2 - 8) * p * (p - 3) :=
      mul_nonneg (mul_nonneg (by nlinarith) (by linarith)) (by linarith)
    have hB : (0 : ℤ) ≤ (3 * i ^ 2 + 2 * i - 32) * (p - 3) :=
      mul_nonneg (by nlinarith) (by linarith)
    have hC : (0 : ℤ) ≤ (-i - 5) * (-9 * i + 31) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hi : 5 ≤ i := by omega
    have hA : (0 : ℤ) ≤ (i ^ 2 - 8) * p ^ 2 := mul_nonneg (by nlinarith) (sq_nonneg _)
    have hB : (0 : ℤ) ≤ (2 * i - 8) * p := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · subst hc
    interval_cases c
    · -- `i = -3`: `p ^ 2 = 14 p + 31`
      norm_num at hQ
      have h1 : (p : ℤ) ≤ 16 := by nlinarith
      have h2 : (16 : ℤ) ≤ p := by nlinarith
      have h3 : (p : ℤ) = 16 := le_antisymm h1 h2
      rw [h3] at hQ
      norm_num at hQ
    · norm_num at hQ; nlinarith
    · norm_num at hQ; nlinarith
    · norm_num at hQ; nlinarith [sq_nonneg ((p : ℤ) - 1)]

end HalfSigmaSquare

open HalfSigmaSquare

/-- **Half of `σ(p ^ 2) + 1` a square.** For an odd prime `p`, if `σ(p ^ 2) + 1 = 2 z ^ 2`, that
is `p ^ 2 + p + 2 = 2 z ^ 2`, then `p = 5`. Elementary; its novelty has not been verified. -/
theorem eq_five_of_sigma_prime_sq_succ_eq_two_mul_sq {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hz : σ 1 (p ^ 2) + 1 = 2 * z ^ 2) : p = 5 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hs : σ 1 (p ^ 2) = p ^ 2 + p + 1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    ring
  have h : (p : ℤ) ^ 2 + p + 2 = 2 * (z : ℤ) ^ 2 := by
    rw [hs] at hz
    have := congrArg (fun n : ℕ => (n : ℤ)) hz
    push_cast at this
    linarith
  rcases dvd_sub_or_add hp hp2 (z := z) (c := p + 1) (by linear_combination (-1 : ℤ) * h)
    with hd | hd
  · exact quad_core hp3 hd h
  · obtain ⟨c, hc⟩ := hd
    exact quad_core hp3 (z := -z) ⟨-c, by linear_combination (-1 : ℤ) * hc⟩
      (by rw [neg_sq]; exact h)

/-- **Half of `σ(p ^ 4) + 1` never a square.** For an odd prime `p`, `σ(p ^ 4) + 1`, that is
`p ^ 4 + p ^ 3 + p ^ 2 + p + 2`, is never of the form `2 z ^ 2`. Elementary; its novelty has
not been verified. -/
theorem sigma_prime_fourth_succ_ne_two_mul_sq {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    σ 1 (p ^ 4) + 1 ≠ 2 * z ^ 2 := by
  intro hz
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hs : σ 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    ring
  have h : (p : ℤ) ^ 4 + p ^ 3 + p ^ 2 + p + 2 = 2 * (z : ℤ) ^ 2 := by
    rw [hs] at hz
    have := congrArg (fun n : ℕ => (n : ℤ)) hz
    push_cast at this
    linarith
  rcases dvd_sub_or_add hp hp2 (z := z) (c := p ^ 3 + p ^ 2 + p + 1)
    (by linear_combination (-1 : ℤ) * h) with hd | hd
  · exact quart_core hp3 hd h
  · obtain ⟨c, hc⟩ := hd
    exact quart_core hp3 (z := -z) ⟨-c, by linear_combination (-1 : ℤ) * hc⟩
      (by rw [neg_sq]; exact h)

end OddPerfect

#print axioms OddPerfect.eq_five_of_sigma_prime_sq_succ_eq_two_mul_sq
#print axioms OddPerfect.sigma_prime_fourth_succ_ne_two_mul_sq
