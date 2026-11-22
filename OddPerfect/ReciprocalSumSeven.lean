import OddPerfect.ReciprocalSum

/-!
# An upper bound for the reciprocal sum in terms of the smallest prime factor

For an odd perfect number `N` with smallest prime factor `p₁ ≥ 7` we prove
`∑_{p ∣ N} 1/p < log 2 - 11/(50 p₁²)` (`sum_inv_lt_log_two_sub_of_seven_le`), and the form with
`p₁ ≥ 11` of the source (`sum_inv_lt_log_two_sub_of_eleven_le`).

Known mathematics. This is Corollary 16 (page 13) of J. Zelinsky, "The sum of the reciprocals of
the prime divisors of an odd perfect or odd primitive non-deficient number", arXiv:2402.14234
(version 5, 2025), which derives it from Proposition 5 (stated on page 4, proved on pages 12
and 13) with Lemma 9 (pages 8 and 9). The proof here follows that argument with these changes.

* Lemma 9 of the source states `1 + x + x² ≥ exp(x + 2x²/5)` for `0 ≤ x ≤ 1/11`. Its written
  proof bounds a tail by `(1/20) ∑ ((1/11 + 2/(5 * 121))/5)^i` and evaluates this as
  `0.0459663`; the expression is about `0.05096`, and with the first part `0.053891` the sum
  exceeds `1/10`, so the written estimate does not close. The statement is true; here it is
  proved independently in the logarithmic form `x + 2x²/5 ≤ log(1 + x + x²)` for
  `0 ≤ x ≤ 1/7` (`add_two_fifths_sq_le_log`), from `1 + x + x² = (1 - x³)/(1 - x)` and truncated
  series for `log(1 - x)` and `log(1 - x³)`. This wider range gives the bound for `p₁ = 7`.
* The hypothesis `(p_t + 2)/2 ≥ p₁` of Proposition 5 (with `p_t` the special prime) is
  discharged as in the proof of Corollary 16: `(q + 1)/2` divides `N` for the special prime `q`
  (`half_succ_dvd`), and it is at least `3`, so its smallest prime factor is a prime factor of
  `N`; hence `q ≥ 2 p₁ - 1`.
* The remaining steps are those of the source: `log 2 ≥ log(1 + 1/q) + ∑_{p ≠ q} log(1 + 1/p +
  1/p²)` (`sum_log_erase_add_log_le`), `log(1 + y) > y - y²/2`, keeping only the term `p₁` of
  `(2/5) ∑_{p ≠ q} 1/p²`, and `1/(2q²) ≤ 9/(50 p₁²)` from `3q ≥ 5 p₁`.

Every constant was checked with exact rationals outside Lean; the Lean proof does not depend on
the source.
-/

open Finset

namespace OddPerfect

/-- For `0 ≤ x ≤ 1/7`, `x + 2x²/5 ≤ log(1 + x + x²)`. Lemma 9 of Zelinsky (arXiv:2402.14234,
pages 8 and 9) in logarithmic form, on the wider range `x ≤ 1/7` (the source has `x ≤ 1/11`);
the proof is independent of the source. -/
theorem add_two_fifths_sq_le_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 7) :
    x + 2 * x ^ 2 / 5 ≤ Real.log (1 + x + x ^ 2) := by
  have hx1 : x < 1 := by linarith
  have hx3 : x ^ 3 ≤ 1 / 343 := by
    calc x ^ 3 ≤ (1 / 7) ^ 3 := by gcongr
      _ = 1 / 343 := by norm_num
  have hx3' : 0 ≤ x ^ 3 := by positivity
  have hx31 : x ^ 3 < 1 := by linarith
  have e : 1 + x + x ^ 2 = (1 - x ^ 3) / (1 - x) := by
    field_simp [show (1 : ℝ) - x ≠ 0 by linarith]
    ring
  rw [e, Real.log_div (by linarith) (by linarith)]
  have hA := le_neg_log_one_sub h0 hx1 4
  have hB := neg_log_one_sub_le hx3' hx31 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hA hB
  norm_num at hA hB
  have hA' : x ^ 5 / (1 - x) ≤ 7 / 6 * x ^ 5 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ x ^ 5 := by positivity
    nlinarith
  have hB' : (x ^ 3) ^ 2 / (1 - x ^ 3) ≤ 343 / 342 * x ^ 6 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ x ^ 6 := by positivity
    have : x ^ 6 * x ^ 3 ≤ x ^ 6 * (1 / 343) := mul_le_mul_of_nonneg_left hx3 this
    nlinarith
  have hpoly : 2 * x ^ 2 / 5 ≤ x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 - 7 / 6 * x ^ 5 - x ^ 3 -
      343 / 342 * x ^ 6 := by
    have hx2 : 0 ≤ x ^ 2 := by positivity
    have hin : 0 ≤ 1 / 10 - 2 / 3 * x - 7 / 6 * x ^ 3 - 343 / 342 * x ^ 4 := by
      have : x ^ 4 ≤ (1 / 7) ^ 4 := by gcongr
      have : x ^ 3 ≤ (1 / 7) ^ 3 := by gcongr
      norm_num at *
      linarith
    have : 0 ≤ x ^ 2 * (1 / 10 - 2 / 3 * x - 7 / 6 * x ^ 3 - 343 / 342 * x ^ 4) :=
      mul_nonneg hx2 hin
    nlinarith [pow_two_nonneg x, sq_nonneg (x ^ 2)]
  have hpow : ((x ^ 3) ^ 2 : ℝ) = x ^ 6 := by ring
  rw [hpow] at hB hB'
  linarith

/-- For `0 < y < 1/4`, `y - y²/2 < log(1 + y)`. -/
theorem sub_half_sq_lt_log_one_add {y : ℝ} (h0 : 0 < y) (h1 : y < 1 / 4) :
    y - y ^ 2 / 2 < Real.log (1 + y) := by
  have hab : |(-y)| < 1 := by rw [abs_neg, abs_of_pos h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hab 3
  rw [abs_neg, abs_of_pos h0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at h
  norm_num at h
  have h' := (abs_le.mp h).1
  have ht : y ^ 4 / (1 - y) ≤ 4 / 3 * y ^ 4 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ y ^ 4 := by positivity
    nlinarith
  have hs : 4 / 3 * y ^ 4 < y ^ 3 / 3 := by
    have : 0 < y ^ 3 := by positivity
    nlinarith
  have e3 : (-y) ^ 3 = -y ^ 3 := by ring
  rw [e3] at h'
  linarith

/-- The special prime `q` of an odd perfect number satisfies `q ≥ 2 p - 1` for every prime
factor `p` with `p ≤` every prime factor (the smallest prime factor): `(q + 1)/2` divides `N`
and is at least `3`. -/
theorem two_mul_le_special_add_one {N q p₁ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hmin : ∀ p ∈ N.primeFactors, p₁ ≤ p) :
    2 * p₁ ≤ q + 1 := by
  have h4 := (special_mod_four h hq hodd).1
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    omega
  have hdvd := half_succ_dvd h hq hodd
  set m := (q + 1) / 2 with hm
  have hm3 : 3 ≤ m := by omega
  have hr := Nat.minFac_prime (show m ≠ 1 by omega)
  have hrN : m.minFac ∣ N := (Nat.minFac_dvd m).trans hdvd
  have hrmem : m.minFac ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩
  have hle : m.minFac ≤ m := Nat.minFac_le (by omega)
  have := hmin _ hrmem
  omega

/-- For an odd perfect number `N` whose smallest prime factor `p₁` is at least `7`,
`∑_{p ∣ N} 1/p < log 2 - 11/(50 p₁²)`. Known mathematics: Corollary 16 (page 13) of Zelinsky,
arXiv:2402.14234 (version 5), stated there for `p₁ ≥ 11`; the range `p₁ ≥ 7` comes from the
independent proof of the logarithmic form of its Lemma 9 here (`add_two_fifths_sq_le_log`). -/
theorem sum_inv_lt_log_two_sub_of_seven_le {N p₁ : ℕ} (h : OddPerfect N)
    (hp₁ : p₁ ∈ N.primeFactors) (hmin : ∀ p ∈ N.primeFactors, p₁ ≤ p) (h7 : 7 ≤ p₁) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < Real.log 2 - 11 / (50 * (p₁ : ℝ) ^ 2) := by
  obtain ⟨q, hq, -, -, he, -⟩ := exists_special_prime h
  have hodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have hqmem : q ∈ N.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hq, Nat.dvd_of_factorization_pos ?_, h.ne_zero⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have h2q := two_mul_le_special_add_one h hq hodd hmin
  have hp₁q : p₁ ≠ q := by omega
  have hp₁E : p₁ ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨hp₁q, hp₁⟩
  set E := N.primeFactors.erase q with hE
  have hbase := sum_log_erase_add_log_le h hq hodd
  -- each ordinary prime: `1/p + (2/5)(1/p)² ≤ log(1 + 1/p + 1/p²)`
  have hord : ∀ p ∈ E, 1 / (p : ℝ) + 2 * (1 / (p : ℝ)) ^ 2 / 5 ≤
      Real.log (1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) := by
    intro p hp
    have hp7 : (7 : ℝ) ≤ p := by
      exact_mod_cast h7.trans (hmin p (Finset.mem_of_mem_erase hp))
    exact add_two_fifths_sq_le_log (by positivity)
      (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
  have hsumE : ∑ p ∈ E, 1 / (p : ℝ) + 2 * (1 / (p₁ : ℝ)) ^ 2 / 5 ≤
      ∑ p ∈ E, Real.log (1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) := by
    have hsq : 2 * (1 / (p₁ : ℝ)) ^ 2 / 5 ≤ ∑ p ∈ E, 2 * (1 / (p : ℝ)) ^ 2 / 5 :=
      Finset.single_le_sum (f := fun p : ℕ => 2 * (1 / (p : ℝ)) ^ 2 / 5)
        (fun p _ => by positivity) hp₁E
    have := Finset.sum_le_sum hord
    rw [Finset.sum_add_distrib] at this
    linarith
  -- the special prime
  have hq13 : (13 : ℝ) ≤ q := by exact_mod_cast (by omega : 13 ≤ q)
  have hqlog := sub_half_sq_lt_log_one_add (y := 1 / (q : ℝ)) (by positivity)
    (by rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith)
  -- `1/(2q²) ≤ 9/(50 p₁²)` from `3q ≥ 5 p₁`
  have hp0 : (0 : ℝ) < p₁ := by exact_mod_cast (by omega : 0 < p₁)
  have h35 : 5 * (p₁ : ℝ) ≤ 3 * q := by exact_mod_cast (by omega : 5 * p₁ ≤ 3 * q)
  have hcmp : (1 / (q : ℝ)) ^ 2 / 2 ≤ 9 / 50 * (1 / (p₁ : ℝ)) ^ 2 := by
    rw [div_pow, div_pow, one_pow, div_div, ← mul_div_assoc, mul_one,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htot : ∑ p ∈ N.primeFactors, 1 / (p : ℝ) = 1 / q + ∑ p ∈ E, 1 / (p : ℝ) :=
    (Finset.add_sum_erase _ _ hqmem).symm
  have e11 : 11 / (50 * (p₁ : ℝ) ^ 2) = 11 / 50 * (1 / (p₁ : ℝ)) ^ 2 := by
    field_simp
  rw [htot, e11]
  linarith

/-- For an odd perfect number `N` whose smallest prime factor `p₁` is at least `11`,
`∑_{p ∣ N} 1/p < log 2 - 11/(50 p₁²)`. Known mathematics: Corollary 16 (page 13) of Zelinsky,
arXiv:2402.14234 (version 5), in the form stated there. -/
theorem sum_inv_lt_log_two_sub_of_eleven_le {N p₁ : ℕ} (h : OddPerfect N)
    (hp₁ : p₁ ∈ N.primeFactors) (hmin : ∀ p ∈ N.primeFactors, p₁ ≤ p) (h11 : 11 ≤ p₁) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < Real.log 2 - 11 / (50 * (p₁ : ℝ) ^ 2) :=
  sum_inv_lt_log_two_sub_of_seven_le h hp₁ hmin (by omega)

/-- Telescoping with squares: for a finite set `T` of odd naturals all at least an odd `M ≥ 3`,
`∑_{p ∈ T} (1/(p-2)² - 1/p²) ≤ 1/(M-2)²`. -/
theorem sum_telescope_sq_le {T : Finset ℕ} {M : ℕ} (hM : 3 ≤ M) (hMo : Odd M)
    (hT : ∀ p ∈ T, Odd p ∧ M ≤ p) :
    ∑ p ∈ T, (1 / ((p : ℝ) - 2) ^ 2 - 1 / (p : ℝ) ^ 2) ≤ 1 / ((M : ℝ) - 2) ^ 2 := by
  set K := T.sup id + 1
  have hsub : T ⊆ (range K).image (fun i => M + 2 * i) := by
    intro p hp
    obtain ⟨hpo, hMp⟩ := hT p hp
    have hle : p ≤ T.sup id := Finset.le_sup (f := id) hp
    obtain ⟨a, ha⟩ := hpo
    obtain ⟨b, hb⟩ := hMo
    rw [Finset.mem_image]
    exact ⟨a - b, Finset.mem_range.mpr (by omega), by omega⟩
  have hnn : ∀ p ∈ (range K).image (fun i => M + 2 * i), p ∉ T →
      0 ≤ 1 / ((p : ℝ) - 2) ^ 2 - 1 / (p : ℝ) ^ 2 := by
    intro p hp _
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    have h3 : (3 : ℝ) ≤ ((M + 2 * i : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ M + 2 * i)
    rw [sub_nonneg]
    have h3' : (0 : ℝ) < ((M + 2 * i : ℕ) : ℝ) - 2 := by linarith
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  rw [Finset.sum_image (fun i _ j _ hij => by omega)]
  set g : ℕ → ℝ := fun i => 1 / ((M : ℝ) - 2 + 2 * i) ^ 2
  have hg : ∀ i ∈ range K, (1 / (((M + 2 * i : ℕ) : ℝ) - 2) ^ 2 -
      1 / ((M + 2 * i : ℕ) : ℝ) ^ 2) = g i - g (i + 1) := by
    intro i _
    simp only [g]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hg, Finset.sum_range_sub']
  have : 0 ≤ g K := by
    simp only [g]
    positivity
  simp only [g, Nat.cast_zero, mul_zero, add_zero] at this ⊢
  linarith

/-- For an odd perfect number `N` whose smallest prime factor `p₁` is at least `7`,
`∏_{p ∣ N} p/(p-1) ≤ 2 + 9/(4 p₁²)`. Known mathematics: Proposition 6 (stated on page 5) of
Zelinsky, arXiv:2402.14234 (version 5), derived there from Lemma 19 (pages 14 and 15); the source
states it for every odd perfect number, and here it is proved only for `p₁ ≥ 7`. The source's
proof of Lemma 19 has gaps, so this is a repair: its Equation (25) replaces `1/(p_j² - 1)` by the
smaller `1/p_j²` and `1/(p_i³ - 1)` by `1/p_i³`, which loses the upper bound; it passes from
`log H ≤ log h + 3/(4 p₁²)` to `H ≤ h (1 + 3/(4 p₁²))`, which does not follow (since
`exp t ≥ 1 + t`); and it calls `1/p_j² + ∑ 1/p_i³ ≤ 3/(4 p₁²)` not hard to see. Here:
`∏ p/(p-1) = 2 ∏ (p/(p-1))/A_p` with `A_p = σ(p^e)/p^e`; each factor is at most
`q²/(q² - 1)` (special prime `q`) or `p³/(p³ - 1)`; so the product is at most `2 exp δ` with
`δ = 1/(q² - 1) + ∑ 1/(p³ - 1) ≤ 1/(4 p₁ (p₁ - 1)) + 1/(4 (p₁ - 2)²)` (using `q ≥ 2 p₁ - 1`
and a telescoping sum), and `2 exp δ ≤ 2 + 2 δ (1 + δ) ≤ 2 + 9/(4 p₁²)` for `p₁ ≥ 7`. -/
theorem prod_div_sub_one_le_two_add_of_seven_le {N p₁ : ℕ} (h : OddPerfect N)
    (hp₁ : p₁ ∈ N.primeFactors) (hmin : ∀ p ∈ N.primeFactors, p₁ ≤ p) (h7 : 7 ≤ p₁) :
    ∏ p ∈ N.primeFactors, ((p : ℝ) / (p - 1)) ≤ 2 + 9 / (4 * (p₁ : ℝ) ^ 2) := by
  obtain ⟨q, hq, -, -, he, -⟩ := exists_special_prime h
  have hodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have hqmem : q ∈ N.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hq, Nat.dvd_of_factorization_pos ?_, h.ne_zero⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have h2q := two_mul_le_special_add_one h hq hodd hmin
  set S := N.primeFactors with hS
  set A : ℕ → ℝ := fun p => ((abundancy (p ^ N.factorization p) : ℚ) : ℝ) with hA
  have hpos : ∀ p ∈ S, (7 : ℝ) ≤ p := fun p hp => by exact_mod_cast h7.trans (hmin p hp)
  have hA1 : ∀ p ∈ S, 1 + 1 / (p : ℝ) ≤ A p := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have he : 0 < N.factorization p :=
      hpr.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)
    have h' := (Rat.cast_le (K := ℝ)).mpr (one_add_inv_le_abundancy_prime_pow hpr he)
    push_cast at h'
    simpa [hA, one_div] using h'
  have hA2 : ∀ p ∈ S, p ≠ q → 1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2 ≤ A p := by
    intro p hp hpq
    have hpr := Nat.prime_of_mem_primeFactors hp
    have he : 0 < N.factorization p :=
      hpr.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)
    obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hpr hpq
    have hm := abundancy_prime_pow_mono hpr (show 2 ≤ N.factorization p by omega)
    rw [abundancy_prime_pow hpr 2] at hm
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hm
    have h' := (Rat.cast_le (K := ℝ)).mpr hm
    push_cast at h'
    simp only [hA, one_div]
    linarith
  -- the product of the components is `2`
  have hprodA : ∏ p ∈ S, A p = 2 := by
    have h2 : (2 : ℚ) = ∏ p ∈ S, abundancy (p ^ N.factorization p) := by
      rw [← abundancy_eq_prod_primeFactors h.ne_zero,
        (perfect_iff_abundancy_eq_two h.pos).mp h.perfect]
    simp only [hA]
    rw [← Rat.cast_prod, ← h2]
    norm_num
  -- the factors `b p` with `p/(p-1) ≤ A p * (1 + b p)`
  set b : ℕ → ℝ := fun p => if p = q then 1 / ((p : ℝ) ^ 2 - 1) else 1 / ((p : ℝ) ^ 3 - 1)
    with hb
  have hfac : ∀ p ∈ S, (p : ℝ) / (p - 1) ≤ A p * (1 + b p) := by
    intro p hp
    have h7p := hpos p hp
    by_cases hpq : p = q
    · have hb' : b p = 1 / ((p : ℝ) ^ 2 - 1) := by simp [hb, hpq]
      rw [hb']
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp2 : (1 : ℝ) < (p : ℝ) ^ 2 := one_lt_pow₀ (by linarith) (by norm_num)
      have hp2' : (p : ℝ) ^ 2 - 1 ≠ 0 := by linarith
      have e : (p : ℝ) / (p - 1) = (1 + 1 / (p : ℝ)) * (1 + 1 / ((p : ℝ) ^ 2 - 1)) := by
        field_simp
        ring
      rw [e]
      have : (0 : ℝ) ≤ 1 + 1 / ((p : ℝ) ^ 2 - 1) := by
        have : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by linarith
        positivity
      exact mul_le_mul_of_nonneg_right (hA1 p hp) this
    · have hb' : b p = 1 / ((p : ℝ) ^ 3 - 1) := by simp [hb, hpq]
      rw [hb']
      have hp3 : (1 : ℝ) < (p : ℝ) ^ 3 := one_lt_pow₀ (by linarith) (by norm_num)
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp3' : (p : ℝ) ^ 3 - 1 ≠ 0 := by linarith
      have e : (p : ℝ) / (p - 1) =
          (1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) * (1 + 1 / ((p : ℝ) ^ 3 - 1)) := by
        field_simp
        ring
      rw [e]
      have : (0 : ℝ) ≤ 1 + 1 / ((p : ℝ) ^ 3 - 1) := by
        have : (0 : ℝ) < (p : ℝ) ^ 3 - 1 := by linarith
        positivity
      exact mul_le_mul_of_nonneg_right (hA2 p hp hpq) this
  have hbnn : ∀ p ∈ S, 0 ≤ b p := by
    intro p hp
    have h7p := hpos p hp
    simp only [hb]
    split_ifs
    · have : (1 : ℝ) < (p : ℝ) ^ 2 := one_lt_pow₀ (by linarith) (by norm_num)
      have : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by linarith
      positivity
    · have : (1 : ℝ) < (p : ℝ) ^ 3 := one_lt_pow₀ (by linarith) (by norm_num)
      have : (0 : ℝ) < (p : ℝ) ^ 3 - 1 := by linarith
      positivity
  have hprod : ∏ p ∈ S, ((p : ℝ) / (p - 1)) ≤ 2 * Real.exp (∑ p ∈ S, b p) := by
    calc ∏ p ∈ S, ((p : ℝ) / (p - 1)) ≤ ∏ p ∈ S, (A p * (1 + b p)) := by
          refine Finset.prod_le_prod (fun p hp => ?_) hfac
          have := hpos p hp
          exact div_nonneg (by linarith) (by linarith)
      _ = (∏ p ∈ S, A p) * ∏ p ∈ S, (1 + b p) := Finset.prod_mul_distrib
      _ ≤ 2 * ∏ p ∈ S, Real.exp (b p) := by
          rw [hprodA]
          gcongr with p hp
          · exact fun p hp => by have := hbnn p hp; linarith
          · have := Real.add_one_le_exp (b p)
            linarith
      _ = 2 * Real.exp (∑ p ∈ S, b p) := by rw [Real.exp_sum]
  -- the sum of the `b p`
  have hp7 : (7 : ℝ) ≤ p₁ := by exact_mod_cast h7
  have hp₁odd : Odd p₁ := h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp₁)
  have hbq : b q ≤ 1 / (4 * (p₁ : ℝ) * (p₁ - 1)) := by
    have hq' : 2 * (p₁ : ℝ) - 1 ≤ q := by
      have : ((2 * p₁ : ℕ) : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast h2q
      push_cast at this
      linarith
    simp only [hb, if_true]
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith
  have hbE : ∑ p ∈ S.erase q, b p ≤ 1 / (4 * ((p₁ : ℝ) - 2) ^ 2) := by
    have hle : ∀ p ∈ S.erase q, b p ≤ (1 / 4) * (1 / ((p : ℝ) - 2) ^ 2 - 1 / (p : ℝ) ^ 2) := by
      intro p hp
      obtain ⟨hpq, hpS⟩ := Finset.mem_erase.mp hp
      have h7p := hpos p hpS
      simp only [hb, hpq, if_false]
      have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp3 : (1 : ℝ) < (p : ℝ) ^ 3 := one_lt_pow₀ (by linarith) (by norm_num)
      have e : (1 / 4 : ℝ) * (1 / ((p : ℝ) - 2) ^ 2 - 1 / (p : ℝ) ^ 2) =
          ((p : ℝ) - 1) / (((p : ℝ) - 2) ^ 2 * (p : ℝ) ^ 2) := by
        field_simp
        ring
      rw [e, div_le_div_iff₀ (by linarith) (by positivity)]
      have key : (0 : ℝ) ≤ 3 * (p : ℝ) ^ 3 - 4 * (p : ℝ) ^ 2 - (p : ℝ) + 1 := by
        have h1 : (0 : ℝ) ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 7) := by
          have : (0 : ℝ) ≤ (p : ℝ) - 7 := by linarith
          positivity
        nlinarith
      nlinarith
    have hT : ∀ p ∈ S.erase q, Odd p ∧ p₁ ≤ p := fun p hp =>
      ⟨h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hp)),
        hmin p (Finset.mem_of_mem_erase hp)⟩
    have htel := sum_telescope_sq_le (M := p₁) (by omega) hp₁odd hT
    calc ∑ p ∈ S.erase q, b p
        ≤ ∑ p ∈ S.erase q, (1 / 4) * (1 / ((p : ℝ) - 2) ^ 2 - 1 / (p : ℝ) ^ 2) :=
          Finset.sum_le_sum hle
      _ = (1 / 4) * ∑ p ∈ S.erase q, (1 / ((p : ℝ) - 2) ^ 2 - 1 / (p : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / 4) * (1 / ((p₁ : ℝ) - 2) ^ 2) := by gcongr
      _ = 1 / (4 * ((p₁ : ℝ) - 2) ^ 2) := by field_simp
  have hsum : ∑ p ∈ S, b p ≤ 469 / 600 * (1 / (p₁ : ℝ) ^ 2) := by
    rw [← Finset.add_sum_erase _ _ hqmem]
    have h1 : 1 / (4 * (p₁ : ℝ) * (p₁ - 1)) ≤ 7 / 24 * (1 / (p₁ : ℝ) ^ 2) := by
      rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
    have h2 : 1 / (4 * ((p₁ : ℝ) - 2) ^ 2) ≤ 49 / 100 * (1 / (p₁ : ℝ) ^ 2) := by
      rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
    linarith
  -- `exp δ ≤ 1 + δ + δ²`
  set δ := ∑ p ∈ S, b p with hδ
  have hδ0 : 0 ≤ δ := Finset.sum_nonneg hbnn
  have hinv : 1 / (p₁ : ℝ) ^ 2 ≤ 1 / 49 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hδ1 : δ ≤ 1 / 50 := by nlinarith
  have hexp : Real.exp δ ≤ 1 + δ + δ ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := δ) (by rw [abs_of_nonneg hδ0]; linarith)
    have := (abs_le.mp this).2
    linarith
  have e94 : 9 / (4 * (p₁ : ℝ) ^ 2) = 9 / 4 * (1 / (p₁ : ℝ) ^ 2) := by field_simp
  rw [e94]
  have hδ2 : δ ^ 2 ≤ δ / 50 := by nlinarith
  nlinarith

end OddPerfect

#print axioms OddPerfect.add_two_fifths_sq_le_log
#print axioms OddPerfect.sub_half_sq_lt_log_one_add
#print axioms OddPerfect.two_mul_le_special_add_one
#print axioms OddPerfect.sum_inv_lt_log_two_sub_of_seven_le
#print axioms OddPerfect.sum_inv_lt_log_two_sub_of_eleven_le
#print axioms OddPerfect.sum_telescope_sq_le
#print axioms OddPerfect.prod_div_sub_one_le_two_add_of_seven_le
