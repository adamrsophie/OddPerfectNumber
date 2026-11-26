import OddPerfect.LargestPrimeFour
import OddPerfect.OmegaSevenFinal

/-!
# The largest prime factor is never `4 R + 1` with `R` prime

Restricted result; no published source was checked; novelty not verified.

Let `N` be an odd perfect number with largest prime factor `P`.

* `geom_sum_mod_three_of_mod_six`: if `R ≡ 1 (mod 6)`, then `∑ i < R, u ^ i ≡ 1 (mod 3)` for
  every `u`, since each block of six consecutive powers sums to a multiple of 3.
* `largest_primeFactor_ne_four_mul_prime_add_one`: `P ≠ 4 R + 1` for every prime `R`. For
  `R > 3` the landed `largest_four_special` gives an odd `j` and a prime `u` with
  `∑ i < R, u ^ i = P ^ j`; here `R ≡ 1 (mod 6)` and `P ≡ 2 (mod 3)`, so the left side is
  `1` and the right side is `2` modulo 3. For `R = 2`, `P = 9` is not prime. For `R = 3`,
  every prime factor of `N` lies in `{3, 5, 7, 11, 13}`, against `seven_le_card_primeFactors`.

This is one restricted case; it neither proves nor disproves the odd perfect number
conjecture, which remains open.
-/

namespace OddPerfect

namespace LargestPrimeFourNone

/-- A residue modulo 3 times the sum of its first six powers is zero. -/
private theorem geom_six_zmod (x : ZMod 3) : x * ∑ i ∈ Finset.range 6, x ^ i = 0 := by
  revert x; decide

/-- A geometric sum of length `6 m + 1` is `1` in `ZMod 3`. -/
private theorem geom_zmod (x : ZMod 3) (m : ℕ) :
    ∑ i ∈ Finset.range (6 * m + 1), x ^ i = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 6 * (m + 1) + 1 = 6 * m + 1 + 6 by ring, Finset.sum_range_add, ih]
    have hb : ∑ i ∈ Finset.range 6, x ^ (6 * m + 1 + i) =
        x ^ (6 * m) * (x * ∑ i ∈ Finset.range 6, x ^ i) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hb, geom_six_zmod, mul_zero, add_zero]

/-- If `R > 3` is prime and `4 R + 1` is prime, then `R ≡ 1 (mod 3)`. -/
private theorem mod_three {R : ℕ} (hR : R.Prime) (hR3 : 3 < R) (hP : (4 * R + 1).Prime) :
    R % 3 = 1 := by
  have h0 : R % 3 ≠ 0 := by
    intro h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hR).mp (by omega)
    omega
  have h2 : R % 3 ≠ 2 := by
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hP).mp (by omega)
    omega
  omega

end LargestPrimeFourNone

open LargestPrimeFourNone

/-- **Geometric sums of length `1 (mod 6)` modulo 3.** If `R ≡ 1 (mod 6)`, then
`∑ i < R, u ^ i ≡ 1 (mod 3)` for every `u`. -/
theorem geom_sum_mod_three_of_mod_six (u : ℕ) {R : ℕ} (hR : R % 6 = 1) :
    (∑ i ∈ Finset.range R, u ^ i) % 3 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, R = 6 * m + 1 := ⟨R / 6, by omega⟩
  have h := (ZMod.natCast_eq_natCast_iff' (∑ i ∈ Finset.range (6 * m + 1), u ^ i) 1 3).mp
    (by push_cast; exact geom_zmod (u : ZMod 3) m)
  simpa using h

/-- **The largest prime factor is never `4 R + 1` with `R` prime.** If `N` is an odd perfect
number with largest prime factor `P` and `R` is prime, then `P ≠ 4 R + 1`. -/
theorem largest_primeFactor_ne_four_mul_prime_add_one {N P R : ℕ} (h : OddPerfect N)
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) :
    P ≠ 4 * R + 1 := by
  intro hPR
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hR2 := hR.two_le
  by_cases h2 : R = 2
  · subst h2; rw [hPR] at hPp; norm_num at hPp
  by_cases h3 : R = 3
  · subst h3
    have hsub : N.primeFactors ⊆ {3, 5, 7, 11, 13} := by
      intro r hr
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hr13 : r ≤ 13 := by have := hmax r hr; omega
      have hr2 : r ≠ 2 := fun e => h.not_two_dvd (e ▸ Nat.dvd_of_mem_primeFactors hr)
      have := hrp.two_le
      simp only [Finset.mem_insert, Finset.mem_singleton]
      interval_cases r <;> first | (simp; done) | exact absurd rfl hr2 | norm_num at hrp
    have := Finset.card_le_card hsub
    have h7 := seven_le_card_primeFactors h
    have : ({3, 5, 7, 11, 13} : Finset ℕ).card = 5 := by decide
    omega
  have hR3 : 3 < R := by omega
  have hR1 := mod_three hR hR3 (hPR ▸ hPp)
  have hRo := Nat.odd_iff.mp (hR.odd_of_ne_two h2)
  obtain ⟨hj, -, -, -, u, -, -, -, hrow⟩ := largest_four_special h hP hmax hR hR3 hPR
  have hl := geom_sum_mod_three_of_mod_six u (R := R) (by omega)
  rw [hrow] at hl
  have hP3 : P % 3 = 2 := by omega
  have hc : ((P ^ N.factorization P : ℕ) : ZMod 3) = ((1 : ℕ) : ZMod 3) :=
    (ZMod.natCast_eq_natCast_iff' _ _ 3).mpr hl
  rw [Nat.cast_pow, ← ZMod.natCast_mod, hP3, show ((2 : ℕ) : ZMod 3) = -1 by decide,
    hj.neg_one_pow] at hc
  exact absurd hc (by decide)

end OddPerfect

#print axioms OddPerfect.geom_sum_mod_three_of_mod_six
#print axioms OddPerfect.largest_primeFactor_ne_four_mul_prime_add_one
