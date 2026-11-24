import OddPerfect.SpecialRank
import OddPerfect.LargestPrimeCap

/-!
# The special exponent in the palette of exponents 2 and 4

Restricted family result; whether it is in the literature was not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`,
let every other prime factor have exponent `2` or `4`, and let `q` be the second largest
prime factor: some prime factor `P > q` exists and every prime factor other than `P` is at
most `q`.

* `sum_sigmaWeight_below_special_le_nine`: the rows of the prime factors below `q` carry at
  most `9` at `q` (the capacity bounds `sum_factorization_phi3_le_two` and
  `sum_factorization_phi5_le_seven` applied with receiver `q`).
* `special_exponent_le_palette`: if those rows carry at most `β` at `q`, then
  `a ≤ max (β + 15) (5 β + 3)` (from `special_exponent_le_rank_two` with `D = 4`, `e ≤ 4`).
* `special_exponent_le_45`: `a ≤ 45`, and `special_exponent_le_41_of_le_eight`: `a ≤ 41`
  when the rows carry at most `8` (both use `a ≡ 1 (mod 4)`).
* `not_three_dvd_succ_special_exponent`: if `3 ∤ N` then `3 ∤ a + 1`, for every odd perfect
  number. Hence, under the explicit hypothesis `3 ∤ N`, the palette family has
  `a ∉ {5, 17, 29, 41}` (`special_exponent_palette_of_not_three_dvd`), and `a ≤ 37` when
  the rows carry at most `8`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem sigma_prime_four' {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  ring

/-- Palette capacity at the special prime. Let `N` be an odd perfect number with special prime
`q` such that every other prime factor has exponent `2` or `4`. Then the rows of the prime
factors below `q` carry at most `9` at `q`. -/
theorem sum_sigmaWeight_below_special_le_nine {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ 9 := by
  set U := N.primeFactors.filter (· < q) with hU
  have hUlt : ∀ s : Finset ℕ, s ⊆ U → ∀ u ∈ s, u < q := fun s hs u hu =>
    (Finset.mem_filter.mp (hs hu)).2
  have hpt : ∀ p ∈ U, sigmaWeight N p q ≤
      (if N.factorization p = 2 then (phi3 p).factorization q else 0) +
      (if N.factorization p = 4 then (p ^ 4 + p ^ 3 + p ^ 2 + p + 1).factorization q
        else 0) := by
    intro p hp
    obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hp'
    rcases hexp p hp' (by omega) with hf | hf
    · rw [if_pos hf, if_neg (by omega), add_zero]
      unfold sigmaWeight
      rw [hf, sigma_prime_sq hpp]
    · rw [if_neg (by omega), if_pos hf, zero_add]
      unfold sigmaWeight
      rw [hf, sigma_prime_four' hpp]
  have hle := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hle
  have h2 := sum_factorization_phi3_le_two hq (U.filter (fun p => N.factorization p = 2))
    (hUlt _ (Finset.filter_subset _ _))
  have h4 : ∑ p ∈ U.filter (fun p => N.factorization p = 4),
      (p ^ 4 + p ^ 3 + p ^ 2 + p + 1).factorization q ≤ 7 := by
    by_cases hq5 : q = 5
    · have hz : ∀ u ∈ U.filter (fun p => N.factorization p = 4),
          (u ^ 4 + u ^ 3 + u ^ 2 + u + 1).factorization q = 0 := by
        intro u hu
        obtain ⟨huU, -⟩ := Finset.mem_filter.mp hu
        obtain ⟨hu', huq⟩ := Finset.mem_filter.mp huU
        have hup := Nat.prime_of_mem_primeFactors hu'
        have hu2 : u ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hu')
        subst hq5
        have hu3 : u = 3 := by
          have := hup.two_le
          interval_cases u
          · exact absurd rfl hu2
          · rfl
          · exact absurd hup (by norm_num)
        subst hu3
        exact Nat.factorization_eq_zero_of_not_dvd (by norm_num)
      rw [Finset.sum_eq_zero hz]
      norm_num
    · exact sum_factorization_phi5_le_seven hq hq5 _ (hUlt _ (Finset.filter_subset _ _))
  omega

/-- Palette bound with a capacity parameter. Let `N` be an odd perfect number with special
prime `q`, let every other prime factor have exponent `2` or `4`, let `P > q` be a prime factor
such that every other prime factor is at most `q`, and let the rows of the prime factors below
`q` carry at most `β` at `q`. Then `v_q(N) ≤ max (β + 15) (5 β + 3)`. -/
theorem special_exponent_le_palette {N q P β : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4)
    (hβ : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ β) :
    N.factorization q ≤ max (β + 15) (5 * β + 3) := by
  have hD : ∀ p ∈ N.primeFactors, p < q → N.factorization p ≤ 4 := by
    intro p hp hpq
    rcases hexp p hp (by omega) with hf | hf <;> omega
  have := special_exponent_le_rank_two h hq hodd hP hqP hsecond hD hβ
  rcases hexp P hP (by omega) with he | he
  · rw [he] at this
    omega
  · rw [he] at this
    omega

/-- Palette bound. Let `N` be an odd perfect number with special prime `q`, let every other
prime factor have exponent `2` or `4`, and let `q` be the second largest prime factor (some
prime factor `P > q`, every prime factor other than `P` at most `q`). Then `v_q(N) ≤ 45`.
Restricted family result; novelty not verified. -/
theorem special_exponent_le_45 {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q ≤ 45 := by
  have h1 := special_exponent_le_palette h hq hodd hP hqP hsecond hexp
    (sum_sigmaWeight_below_special_le_nine h hq hexp)
  have h2 := (special_mod_four h hq hodd).2
  omega

/-- Palette bound when the rows below the special prime carry at most `8` at it: in the
setting of `special_exponent_le_45`, `v_q(N) ≤ 41`. -/
theorem special_exponent_le_41_of_le_eight {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4)
    (h8 : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ 8) :
    N.factorization q ≤ 41 := by
  have h1 := special_exponent_le_palette h hq hodd hP hqP hsecond hexp h8
  have h2 := (special_mod_four h hq hodd).2
  omega

/-- For an odd perfect number `N` with special prime `q` and `3 ∤ N`, the special exponent
satisfies `3 ∤ v_q(N) + 1`; otherwise `3` would divide `σ(q ^ v_q(N))`. -/
theorem not_three_dvd_succ_special_exponent {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N) :
    ¬ 3 ∣ N.factorization q + 1 := by
  intro h3a
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  have hq3 : q ≠ 3 := fun hq3 => h3 (hq3 ▸ Nat.dvd_of_mem_primeFactors hqmem)
  set a := N.factorization q with ha
  have hσ : 3 ∣ σ 1 (q ^ a) := by
    have hmod : q % 3 = 1 ∨ q % 3 = 2 := by
      rcases (by omega : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2) with h0 | h1 | h2
      · exfalso
        have hd : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
        exact hq3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hd).symm
      · exact Or.inl h1
      · exact Or.inr h2
    rcases hmod with h1 | h2
    · rw [← ZMod.natCast_eq_zero_iff, sigma_one_apply_prime_pow hq]
      push_cast
      have hq1 : (q : ZMod 3) = 1 := by
        rw [← ZMod.natCast_mod, h1, Nat.cast_one]
      rw [hq1]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr h3a
    · exact (Nat.dvd_of_mod_eq_zero (by omega : (q + 1) % 3 = 0)).trans
        (succ_dvd_sigma_special hq hodd)
  have hw : sigmaWeight N q 3 ≠ 0 := by
    unfold sigmaWeight
    exact (Nat.prime_three.factorization_pos_of_dvd
      (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne' hσ).ne'
  exact h3 (Nat.dvd_of_mem_primeFactors
    (mem_primeFactors_of_sigmaWeight_ne_zero h.2 hqmem (by norm_num) hw))

/-- Palette family without the prime `3`. In the setting of `special_exponent_le_45`, under
the explicit hypothesis `3 ∤ N`, the special exponent `a = v_q(N)` satisfies `a ≤ 45`,
`a ≡ 1 (mod 4)`, and `a ∉ {5, 17, 29, 41}`. -/
theorem special_exponent_palette_of_not_three_dvd {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) :
    N.factorization q ≤ 45 ∧ N.factorization q % 4 = 1 ∧ N.factorization q ≠ 5 ∧
      N.factorization q ≠ 17 ∧ N.factorization q ≠ 29 ∧ N.factorization q ≠ 41 := by
  have h1 := special_exponent_le_45 h hq hodd hP hqP hsecond hexp
  have h2 := (special_mod_four h hq hodd).2
  have h4 := not_three_dvd_succ_special_exponent h hq hodd h3
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> intro he <;> rw [he] at h4 <;> exact h4 (by norm_num)

/-- Palette family without the prime `3`, with capacity `8`: in the setting of
`special_exponent_le_41_of_le_eight`, under the explicit hypothesis `3 ∤ N`, `v_q(N) ≤ 37`. -/
theorem special_exponent_le_37_of_le_eight_of_not_three_dvd {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4)
    (h8 : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ 8) (h3 : ¬ 3 ∣ N) :
    N.factorization q ≤ 37 := by
  have h1 := special_exponent_le_41_of_le_eight h hq hodd hP hqP hsecond hexp h8
  have h2 := (special_mod_four h hq hodd).2
  have h4 := not_three_dvd_succ_special_exponent h hq hodd h3
  have : N.factorization q ≠ 41 := by
    intro he; rw [he] at h4; exact h4 (by norm_num)
  omega

end OddPerfect

#print axioms OddPerfect.sum_sigmaWeight_below_special_le_nine
#print axioms OddPerfect.special_exponent_le_palette
#print axioms OddPerfect.special_exponent_le_45
#print axioms OddPerfect.special_exponent_le_41_of_le_eight
#print axioms OddPerfect.not_three_dvd_succ_special_exponent
#print axioms OddPerfect.special_exponent_palette_of_not_three_dvd
#print axioms OddPerfect.special_exponent_le_37_of_le_eight_of_not_three_dvd
