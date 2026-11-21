import OddPerfect.Abundancy
import OddPerfect.SpecialPrime
import Mathlib

/-!
# The sum of the reciprocals of the prime factors of an odd perfect number

For an odd perfect number `N` we bound `∑_{p ∣ N} 1/p` over the reals.

* Lower bounds: `log 2 < ∑ 1/(p - 1)` and `23/40 < ∑ 1/p`. The second one uses the
  correction `c(p) = log(p/(p-1)) - 1/p`, explicit rational upper bounds on `c(p)` for
  `p ∈ {3, 5, 7, 11, 13, 17, 19}`, the obstruction `105 ∤ N`, and the telescoping bound
  `c(p) ≤ (1/4)(1/(p-2) - 1/p)` for the primes `p ≥ 23`.
* Upper bounds: with `q` the special prime, `∑_{p ≠ q} 1/p + log(1 + 1/q) ≤ log 2`, hence
  `∑ 1/p ≤ log 2 + 1/q - log(1 + 1/q)`, and in general
  `∑ 1/p < log 2 + 1/29 - log(30/29) < 347/500`.

Bounds of this kind are classical. The inequality `∑ 1/p < log 2` is due to D. Suryanarayana
(On odd perfect numbers II, Proc. Amer. Math. Soc. 14 (1963), 896 to 904), who also gave lower
and upper bounds by cases on whether 3 and 5 divide `N`; sharper constants are in
D. Suryanarayana and P. Hagis (Fibonacci Quart. 8 (1970), 337 to 346), and a short proof with a
further improvement is in G. L. Cohen (On odd perfect numbers, Fibonacci Quart. 16 (1978)). The
constants here are the ones proved in this file; they are weaker than the published case by
case constants.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Elementary real inequalities -/

/-- Upper bound for `-log(1 - x)` by a truncated series. -/
theorem neg_log_one_sub_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -Real.log (1 - x) ≤ (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rwa [abs_of_nonneg h0]) n
  rw [abs_of_nonneg h0] at h
  linarith [(abs_le.mp h).1]

/-- Lower bound for `-log(1 - x)` by a truncated series. -/
theorem le_neg_log_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ -Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rwa [abs_of_nonneg h0]) n
  rw [abs_of_nonneg h0] at h
  linarith [(abs_le.mp h).2]

/-- `log(p/(p-1)) = -log(1 - 1/p)` for real `p > 1`. -/
theorem log_div_sub_one_eq {p : ℝ} (hp : 1 < p) :
    Real.log (p / (p - 1)) = -Real.log (1 - 1 / p) := by
  have h1 : (1 : ℝ) - 1 / p = (p / (p - 1))⁻¹ := by
    field_simp
  rw [h1, Real.log_inv, neg_neg]

/-- For `0 < x ≤ 1`, `x < log(1 + x + x²)`. -/
theorem lt_log_one_add_add_sq {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) :
    x < Real.log (1 + x + x ^ 2) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have h := Real.exp_bound' h0.le h1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith

/-- The function `x - log(1 + x)` is monotone on `[0, ∞)`. -/
theorem sub_log_one_add_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x - Real.log (1 + x) ≤ y - Real.log (1 + y) := by
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 + y := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos h2 h1)
  rw [Real.log_div h2.ne' h1.ne'] at h
  have h3 : (1 + y) / (1 + x) - 1 ≤ y - x := by
    rw [div_sub_one h1.ne', div_le_iff₀ h1]
    nlinarith
  linarith

/-- The tail correction: for real `p ≥ 3`, `log(p/(p-1)) - 1/p ≤ (1/4)(1/(p-2) - 1/p)`. -/
theorem log_div_sub_one_sub_inv_le {p : ℝ} (hp : 3 ≤ p) :
    Real.log (p / (p - 1)) - 1 / p ≤ (1 / 4) * (1 / (p - 2) - 1 / p) := by
  rw [log_div_sub_one_eq (by linarith)]
  have h := neg_log_one_sub_le (x := 1 / p) (by positivity)
    (by rw [div_lt_one (by linarith)]; linarith) 2
  norm_num [Finset.sum_range_succ] at h
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have key : (p⁻¹ ^ 2 / 2 + p⁻¹ ^ 3 / (1 - p⁻¹)) ≤ (1 / 4) * (1 / (p - 2) - 1 / p) := by
    have e1 : p⁻¹ ^ 2 / 2 + p⁻¹ ^ 3 / (1 - p⁻¹) = (p + 1) / (2 * p ^ 2 * (p - 1)) := by
      field_simp
      ring
    have e2 : (1 / 4) * (1 / (p - 2) - 1 / p) = 1 / (2 * p * (p - 2)) := by
      field_simp
      ring
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have : -Real.log (1 - 1 / p) ≤ p⁻¹ + (p⁻¹ ^ 2 / 2 + p⁻¹ ^ 3 / (1 - p⁻¹)) := by
    simpa [one_div, add_assoc] using h
  simp only [one_div] at key this ⊢
  linarith

/-- Telescoping: for a finite set `T` of odd naturals all at least an odd `M ≥ 3`,
`∑_{p ∈ T} (1/(p-2) - 1/p) ≤ 1/(M-2)`. -/
theorem sum_telescope_le {T : Finset ℕ} {M : ℕ} (hM : 3 ≤ M) (hMo : Odd M)
    (hT : ∀ p ∈ T, Odd p ∧ M ≤ p) :
    ∑ p ∈ T, (1 / ((p : ℝ) - 2) - 1 / p) ≤ 1 / ((M : ℝ) - 2) := by
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
      0 ≤ 1 / ((p : ℝ) - 2) - 1 / p := by
    intro p hp _
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    have h3 : (3 : ℝ) ≤ ((M + 2 * i : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ M + 2 * i)
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  rw [Finset.sum_image (fun i _ j _ hij => by omega)]
  set g : ℕ → ℝ := fun i => 1 / ((M : ℝ) - 2 + 2 * i)
  have hg : ∀ i ∈ range K, (1 / (((M + 2 * i : ℕ) : ℝ) - 2) - 1 / ((M + 2 * i : ℕ) : ℝ)) =
      g i - g (i + 1) := by
    intro i _
    simp only [g]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hg, Finset.sum_range_sub']
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have : 0 ≤ g K := by
    simp only [g]
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    apply div_nonneg zero_le_one
    linarith
  simp only [g, Nat.cast_zero, mul_zero, add_zero] at this ⊢
  linarith

/-! ## Explicit corrections for small primes -/

private theorem corr_le {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    Real.log ((p : ℝ) / (p - 1)) - 1 / p ≤
      (∑ i ∈ range n, (1 / (p : ℝ)) ^ (i + 1) / (i + 1)) +
        (1 / (p : ℝ)) ^ (n + 1) / (1 - 1 / p) - 1 / p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [log_div_sub_one_eq (by linarith)]
  have := neg_log_one_sub_le (x := 1 / (p : ℝ)) (by positivity)
    (by rw [div_lt_one (by linarith)]; linarith) n
  linarith

private theorem corr3 : Real.log (((3 : ℕ) : ℝ) / ((3 : ℕ) - 1)) - 1 / ((3 : ℕ) : ℝ) ≤
    721327 / 10000000 := by
  refine (corr_le (by norm_num) 12).trans ?_
  norm_num [Finset.sum_range_succ]

private theorem corr5 : Real.log (((5 : ℕ) : ℝ) / ((5 : ℕ) - 1)) - 1 / ((5 : ℕ) : ℝ) ≤
    28933 / 1250000 := by
  refine (corr_le (by norm_num) 7).trans ?_
  norm_num [Finset.sum_range_succ]

private theorem corr7 : Real.log (((7 : ℕ) : ℝ) / ((7 : ℕ) - 1)) - 1 / ((7 : ℕ) : ℝ) ≤
    28237 / 2500000 := by
  refine (corr_le (by norm_num) 6).trans ?_
  norm_num [Finset.sum_range_succ]

private theorem corr11 : Real.log (((11 : ℕ) : ℝ) / ((11 : ℕ) - 1)) - 1 / ((11 : ℕ) : ℝ) ≤
    44017 / 10000000 := by
  refine (corr_le (by norm_num) 5).trans ?_
  norm_num [Finset.sum_range_succ]

private theorem corr13 : Real.log (((13 : ℕ) : ℝ) / ((13 : ℕ) - 1)) - 1 / ((13 : ℕ) : ℝ) ≤
    1561 / 500000 := by
  refine (corr_le (by norm_num) 4).trans ?_
  norm_num [Finset.sum_range_succ]

private theorem corr17 : Real.log (((17 : ℕ) : ℝ) / ((17 : ℕ) - 1)) - 1 / ((17 : ℕ) : ℝ) ≤
    18017 / 10000000 := by
  refine (corr_le (by norm_num) 4).trans ?_
  norm_num [Finset.sum_range_succ]

private theorem corr19 : Real.log (((19 : ℕ) : ℝ) / ((19 : ℕ) - 1)) - 1 / ((19 : ℕ) : ℝ) ≤
    359 / 250000 := by
  refine (corr_le (by norm_num) 4).trans ?_
  norm_num [Finset.sum_range_succ]

private theorem ite_le {P : Prop} [Decidable P] {x a : ℝ} (hx : x ≤ a) :
    (if P then x else 0) ≤ if P then a else 0 := by
  split_ifs
  · exact hx
  · exact le_refl 0

private theorem ite_const_le {P : Prop} [Decidable P] {a : ℝ} (ha : 0 ≤ a) :
    (if P then a else 0) ≤ a := by
  split_ifs
  · exact le_refl a
  · exact ha

/-! ## Lower bounds -/

variable {N : ℕ}

private theorem three_le_of_mem (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    3 ≤ p ∧ Odd p := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hodd : Odd p := h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  refine ⟨?_, hodd⟩
  have := hp'.two_le
  obtain ⟨k, rfl⟩ := hodd
  omega

private theorem one_lt (h : OddPerfect N) : 1 < N := by
  have h3 := three_le_card_primeFactors h
  by_contra hN
  interval_cases N <;> simp at h3

/-- For an odd perfect number, `log 2 < ∑_{p ∣ N} log(p/(p-1))`. -/
theorem log_two_lt_sum_log (h : OddPerfect N) :
    Real.log 2 < ∑ p ∈ N.primeFactors, Real.log ((p : ℝ) / (p - 1)) := by
  have hlt := abundancy_lt_prod (one_lt h)
  rw [(perfect_iff_abundancy_eq_two h.pos).mp h.perfect] at hlt
  have hlt' : (2 : ℝ) < ∏ p ∈ N.primeFactors, ((p : ℝ) / (p - 1)) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hlt
    push_cast at this
    exact this
  rw [← Real.log_prod]
  · exact Real.log_lt_log two_pos hlt'
  · intro p hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast (three_le_of_mem h hp).1
    exact (div_pos (by linarith) (by linarith)).ne'

/-- Target A1: for an odd perfect number, `log 2 < ∑_{p ∣ N} 1/(p - 1)`. -/
theorem log_two_lt_sum_inv_sub_one (h : OddPerfect N) :
    Real.log 2 < ∑ p ∈ N.primeFactors, 1 / ((p : ℝ) - 1) := by
  refine (log_two_lt_sum_log h).trans_le (Finset.sum_le_sum fun p hp => ?_)
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (three_le_of_mem h hp).1
  have := Real.log_le_sub_one_of_pos (x := (p : ℝ) / (p - 1)) (div_pos (by linarith) (by linarith))
  have e : (p : ℝ) / (p - 1) - 1 = 1 / ((p : ℝ) - 1) := by
    rw [div_sub_one (by linarith)]
    ring
  linarith

/-- Target A2: for an odd perfect number, `23/40 < ∑_{p ∣ N} 1/p`.

The proof uses explicit bounds on `log(p/(p-1)) - 1/p` for `p = 3, 5, 7, 11, 13, 17, 19`,
the fact that `3, 5, 7` do not all divide `N`, and the telescoping tail bound
`(1/4) * 1/(23 - 2)` for the primes `p ≥ 23`. -/
theorem twentythree_fortieths_lt_sum_inv (h : OddPerfect N) :
    (23 / 40 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  set S := N.primeFactors with hS
  set f : ℕ → ℝ := fun p => Real.log ((p : ℝ) / (p - 1)) - 1 / p with hf
  have hsplit : ∑ p ∈ S, Real.log ((p : ℝ) / (p - 1)) = ∑ p ∈ S, 1 / (p : ℝ) + ∑ p ∈ S, f p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by simp only [f]; ring
  -- the small primes
  have hE : S.filter (· < 23) = ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ).filter (· ∈ S) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hlt⟩
      refine ⟨?_, hp⟩
      obtain ⟨h3, hodd⟩ := three_le_of_mem h hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      interval_cases p <;> first
        | (simp; done)
        | (exfalso; revert hodd; decide)
        | (exfalso; norm_num at hpr)
    · rintro ⟨hmem, hp⟩
      exact ⟨hp, by rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num⟩
  have hsmall : ∑ p ∈ S.filter (· < 23), f p ≤
      721327 / 10000000 + 28933 / 1250000 + 44017 / 10000000 + 1561 / 500000 +
        18017 / 10000000 + 359 / 250000 := by
    rw [hE, Finset.sum_filter]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    have hn105 := not_105_dvd h
    have m3 : 3 ∈ S ↔ 3 ∣ N := by simp [hS, Nat.mem_primeFactors, h.ne_zero, Nat.prime_three]
    have m5 : 5 ∈ S ↔ 5 ∣ N := by simp [hS, Nat.mem_primeFactors, h.ne_zero, Nat.prime_five]
    have m7 : 7 ∈ S ↔ 7 ∣ N := by
      simp [hS, Nat.mem_primeFactors, h.ne_zero, (by norm_num : Nat.Prime 7)]
    simp only [f]
    have e3 := ite_le (P := 3 ∈ S) corr3
    have e5 := ite_le (P := 5 ∈ S) corr5
    have e7 := ite_le (P := 7 ∈ S) corr7
    have e11 := (ite_le (P := 11 ∈ S) corr11).trans (ite_const_le (P := 11 ∈ S) (by norm_num))
    have e13 := (ite_le (P := 13 ∈ S) corr13).trans (ite_const_le (P := 13 ∈ S) (by norm_num))
    have e17 := (ite_le (P := 17 ∈ S) corr17).trans (ite_const_le (P := 17 ∈ S) (by norm_num))
    have e19 := (ite_le (P := 19 ∈ S) corr19).trans (ite_const_le (P := 19 ∈ S) (by norm_num))
    have s357 : ((if 3 ∈ S then (721327 / 10000000 : ℝ) else 0) +
        (if 5 ∈ S then (28933 / 1250000 : ℝ) else 0) + (if 7 ∈ S then (28237 / 2500000 : ℝ) else 0))
        ≤ 721327 / 10000000 + 28933 / 1250000 := by
      by_cases i3 : 3 ∈ S <;> by_cases i5 : 5 ∈ S <;> by_cases i7 : 7 ∈ S <;>
        simp only [i3, i5, i7, if_true, if_false] <;>
        first
          | (exfalso; exact hn105 (by have := m3.mp i3; have := m5.mp i5; have := m7.mp i7; omega))
          | norm_num
    linarith
  -- the tail
  have htail : ∑ p ∈ S.filter (fun p => ¬ p < 23), f p ≤ (1 / 4) * (1 / ((23 : ℕ) - 2 : ℝ)) := by
    have hT : ∀ p ∈ S.filter (fun p => ¬ p < 23), Odd p ∧ 23 ≤ p := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact ⟨(three_le_of_mem h hp.1).2, by omega⟩
    calc ∑ p ∈ S.filter (fun p => ¬ p < 23), f p
        ≤ ∑ p ∈ S.filter (fun p => ¬ p < 23), (1 / 4) * (1 / ((p : ℝ) - 2) - 1 / p) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have : (3 : ℝ) ≤ p := by exact_mod_cast (by have := (hT p hp).2; omega : 3 ≤ p)
          exact log_div_sub_one_sub_inv_le this
      _ = (1 / 4) * ∑ p ∈ S.filter (fun p => ¬ p < 23), (1 / ((p : ℝ) - 2) - 1 / p) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / 4) * (1 / ((23 : ℕ) - 2 : ℝ)) := by
          gcongr
          exact sum_telescope_le (by norm_num) (by decide) hT
  have hsum := Finset.sum_filter_add_sum_filter_not S (· < 23) f
  have hlog := log_two_lt_sum_log h
  have hl2 := Real.log_two_gt_d9
  rw [← hS, hsplit] at hlog
  have h84 : (1 / 4 : ℝ) * (1 / ((23 : ℕ) - 2 : ℝ)) = 1 / 84 := by norm_num
  norm_num at hl2
  linarith

/-! ## Upper bounds -/

private theorem log_two_eq_sum_log_abundancy (h : OddPerfect N) :
    Real.log 2 = ∑ p ∈ N.primeFactors,
      Real.log ((abundancy (p ^ N.factorization p) : ℚ) : ℝ) := by
  have h2 : (2 : ℚ) = ∏ p ∈ N.primeFactors, abundancy (p ^ N.factorization p) := by
    rw [← abundancy_eq_prod_primeFactors h.ne_zero,
      (perfect_iff_abundancy_eq_two h.pos).mp h.perfect]
  have h2' : (2 : ℝ) = ∏ p ∈ N.primeFactors, ((abundancy (p ^ N.factorization p) : ℚ) : ℝ) := by
    rw [← Rat.cast_prod, ← h2]
    norm_num
  rw [h2', Real.log_prod]
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have he : 0 < N.factorization p :=
    hpr.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)
  have hle := one_add_inv_le_abundancy_prime_pow hpr he
  have : (0 : ℚ) < abundancy (p ^ N.factorization p) := lt_of_lt_of_le (by positivity) hle
  exact_mod_cast this.ne'

private theorem abundancy_ge_sq {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2 ≤ ((abundancy (p ^ e) : ℚ) : ℝ) := by
  have h := abundancy_prime_pow_mono hp he
  rw [abundancy_prime_pow hp 2] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  simp only [one_div]
  linarith

private theorem abundancy_ge_one {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    1 + 1 / (p : ℝ) ≤ ((abundancy (p ^ e) : ℚ) : ℝ) := by
  have h' := (Rat.cast_le (K := ℝ)).mpr (one_add_inv_le_abundancy_prime_pow hp he)
  push_cast at h'
  simpa [one_div] using h'

private theorem mem_of_odd (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : q ∈ N.primeFactors := by
  rw [Nat.mem_primeFactors]
  refine ⟨hq, Nat.dvd_of_factorization_pos ?_, h.ne_zero⟩
  obtain ⟨k, hk⟩ := hodd
  omega

/-- For an odd perfect number with special prime `q` (the prime with odd exponent),
`∑_{p ∣ N, p ≠ q} log(1 + 1/p + 1/p²) + log(1 + 1/q) ≤ log 2`. -/
theorem sum_log_erase_add_log_le (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ∑ p ∈ N.primeFactors.erase q, Real.log (1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) +
      Real.log (1 + 1 / (q : ℝ)) ≤ Real.log 2 := by
  rw [log_two_eq_sum_log_abundancy h, ← Finset.add_sum_erase _ _ (mem_of_odd h hq hodd)]
  have hq1 : Real.log (1 + 1 / (q : ℝ)) ≤
      Real.log ((abundancy (q ^ N.factorization q) : ℚ) : ℝ) := by
    refine Real.log_le_log (by positivity) (abundancy_ge_one hq ?_)
    obtain ⟨k, hk⟩ := hodd
    omega
  have hrest : ∑ p ∈ N.primeFactors.erase q, Real.log (1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) ≤
      ∑ p ∈ N.primeFactors.erase q, Real.log ((abundancy (p ^ N.factorization p) : ℚ) : ℝ) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hpq, hp⟩ := Finset.mem_erase.mp hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have he : 0 < N.factorization p :=
      hpr.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)
    obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hpr hpq
    exact Real.log_le_log (by positivity) (abundancy_ge_sq hpr (by omega))
  linarith

/-- Target B1, first form: `∑_{p ∣ N, p ≠ q} 1/p + log(1 + 1/q) ≤ log 2` for the special
prime `q`. -/
theorem sum_inv_erase_add_log_le (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ∑ p ∈ N.primeFactors.erase q, 1 / (p : ℝ) + Real.log (1 + 1 / (q : ℝ)) ≤ Real.log 2 := by
  refine le_trans ?_ (sum_log_erase_add_log_le h hq hodd)
  gcongr with p hp
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
  exact (lt_log_one_add_add_sq (by positivity) (by rw [div_le_one (by linarith)]; linarith)).le

/-- Target B1, second form: `∑_{p ∣ N} 1/p ≤ log 2 + (1/q - log(1 + 1/q))` for the special
prime `q`. -/
theorem sum_inv_le_of_special (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ≤ Real.log 2 + (1 / q - Real.log (1 + 1 / (q : ℝ))) := by
  rw [← Finset.add_sum_erase _ _ (mem_of_odd h hq hodd)]
  linarith [sum_inv_erase_add_log_le h hq hodd]

/-- The special prime of an odd perfect number, packaged with the facts used below. -/
private theorem special (h : OddPerfect N) :
    ∃ q : ℕ, q.Prime ∧ Odd (N.factorization q) ∧ q % 4 = 1 := by
  obtain ⟨q, hq, -, hq4, he, -⟩ := exists_special_prime h
  exact ⟨q, hq, Nat.odd_iff.mpr (by omega), hq4⟩

/-- Target B2: for an odd perfect number, `∑_{p ∣ N} 1/p ≤ log 2 + 1/5 - log(6/5)`. -/
theorem sum_inv_le_log_two_add (h : OddPerfect N) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ≤ Real.log 2 + 1 / 5 - Real.log (6 / 5) := by
  obtain ⟨q, hq, hodd, hq4⟩ := special h
  have hq5 : (5 : ℝ) ≤ q := by
    have := hq.two_le
    exact_mod_cast (by omega : 5 ≤ q)
  have hmono := sub_log_one_add_mono (x := 1 / (q : ℝ)) (y := 1 / 5) (by positivity)
    (one_div_le_one_div_of_le (by norm_num) hq5)
  have := sum_inv_le_of_special h hq hodd
  norm_num at hmono ⊢
  simp only [one_div] at this
  linarith

/-- Lower bound for `log(1/(1 - x))` by a truncated series, in the form used below. -/
private theorem log_inv_one_sub_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ Real.log (1 - x)⁻¹ := by
  rw [Real.log_inv]
  exact le_neg_log_one_sub h0 h1 n

/-- Target B3: for an odd perfect number, `∑_{p ∣ N} 1/p < log 2 + 1/29 - log(30/29)`. -/
theorem sum_inv_lt_log_two_add (h : OddPerfect N) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < Real.log 2 + 1 / 29 - Real.log (30 / 29) := by
  obtain ⟨q, hq, hodd, hq4⟩ := special h
  set E := N.primeFactors.erase q
  set d : ℕ → ℝ := fun p => Real.log (1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) - 1 / p with hd
  have hdpos : ∀ p ∈ E, 0 < d p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
    have := lt_log_one_add_add_sq (x := 1 / (p : ℝ)) (by positivity)
      (by rw [div_le_one (by linarith)]; linarith)
    simp only [d]
    linarith
  have hbase := sum_log_erase_add_log_le h hq hodd
  have hsplit : ∑ p ∈ E, Real.log (1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) =
      ∑ p ∈ E, 1 / (p : ℝ) + ∑ p ∈ E, d p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by simp only [d]; ring
  have htot : ∑ p ∈ N.primeFactors, 1 / (p : ℝ) = 1 / q + ∑ p ∈ E, 1 / (p : ℝ) :=
    (Finset.add_sum_erase _ _ (mem_of_odd h hq hodd)).symm
  -- the key inequality with the slack
  have key : ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ≤
      Real.log 2 + (1 / q - Real.log (1 + 1 / (q : ℝ))) - ∑ p ∈ E, d p := by
    rw [hsplit] at hbase
    linarith
  have hsingle : ∀ r ∈ E, d r ≤ ∑ p ∈ E, d p := fun r hr =>
    Finset.single_le_sum (fun p hp => (hdpos p hp).le) hr
  have mem_E : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ q + 1 → r ∈ E := by
    intro r hr hr2 hrq
    obtain ⟨hrN, hrq'⟩ := prime_dvd_of_dvd_succ_special h hq hodd hr hr2 hrq
    exact Finset.mem_erase.mpr ⟨hrq', Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩⟩
  -- numerical facts
  have l3029u : Real.log (30 / 29) ≤ 339026 / 10000000 := by
    have := neg_log_one_sub_le (x := 1 / 30) (by norm_num) (by norm_num) 3
    rw [← Real.log_inv] at this
    norm_num [Finset.sum_range_succ] at this
    linarith
  have hd3 : (36729 / 100000 : ℝ) - 1 / 3 ≤ d 3 := by
    have := log_inv_one_sub_ge (x := 4 / 13) (by norm_num) (by norm_num) 6
    simp only [d]
    norm_num [Finset.sum_range_succ] at this ⊢
    linarith
  have hd7 : (15115 / 100000 : ℝ) - 1 / 7 ≤ d 7 := by
    have := log_inv_one_sub_ge (x := 8 / 57) (by norm_num) (by norm_num) 4
    simp only [d]
    norm_num [Finset.sum_range_succ] at this ⊢
    linarith
  by_cases hq29 : q < 29
  · have hq' : q = 5 ∨ q = 13 ∨ q = 17 := by
      have := hq.two_le
      interval_cases q <;> first | omega | (exfalso; norm_num at hq)
    rcases hq' with rfl | rfl | rfl
    · have h3 := hsingle 3 (mem_E 3 Nat.prime_three (by norm_num) (by norm_num))
      have l := log_inv_one_sub_ge (x := 1 / 6) (by norm_num) (by norm_num) 4
      norm_num [Finset.sum_range_succ] at l key ⊢
      linarith
    · have h7 := hsingle 7 (mem_E 7 (by norm_num) (by norm_num) (by norm_num))
      have l := log_inv_one_sub_ge (x := 1 / 14) (by norm_num) (by norm_num) 2
      norm_num [Finset.sum_range_succ] at l key ⊢
      linarith
    · have h3 := hsingle 3 (mem_E 3 Nat.prime_three (by norm_num) (by norm_num))
      have l := log_inv_one_sub_ge (x := 1 / 18) (by norm_num) (by norm_num) 2
      norm_num [Finset.sum_range_succ] at l key ⊢
      linarith
  · have hq29' : (29 : ℝ) ≤ q := by exact_mod_cast (by omega : 29 ≤ q)
    have hmono := sub_log_one_add_mono (x := 1 / (q : ℝ)) (y := 1 / 29) (by positivity)
      (one_div_le_one_div_of_le (by norm_num) hq29')
    have hne : E.Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (mem_of_odd h hq hodd)]
      have := three_le_card_primeFactors h
      omega
    obtain ⟨r, hr⟩ := hne
    have := hsingle r hr
    have := hdpos r hr
    norm_num at hmono ⊢
    simp only [one_div] at key hmono ⊢
    linarith

/-- Target B3, rational form: for an odd perfect number, `∑_{p ∣ N} 1/p < 347/500`. -/
theorem sum_inv_lt_347_div_500 (h : OddPerfect N) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < 347 / 500 := by
  have hmain := sum_inv_lt_log_two_add h
  have hl2 := Real.log_two_lt_d9
  have l := log_inv_one_sub_ge (x := 1 / 30) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at l hl2
  linarith

end OddPerfect

#print axioms OddPerfect.neg_log_one_sub_le
#print axioms OddPerfect.le_neg_log_one_sub
#print axioms OddPerfect.log_div_sub_one_eq
#print axioms OddPerfect.lt_log_one_add_add_sq
#print axioms OddPerfect.sub_log_one_add_mono
#print axioms OddPerfect.log_div_sub_one_sub_inv_le
#print axioms OddPerfect.sum_telescope_le
#print axioms OddPerfect.log_two_lt_sum_log
#print axioms OddPerfect.log_two_lt_sum_inv_sub_one
#print axioms OddPerfect.twentythree_fortieths_lt_sum_inv
#print axioms OddPerfect.sum_log_erase_add_log_le
#print axioms OddPerfect.sum_inv_erase_add_log_le
#print axioms OddPerfect.sum_inv_le_of_special
#print axioms OddPerfect.sum_inv_le_log_two_add
#print axioms OddPerfect.sum_inv_lt_log_two_add
#print axioms OddPerfect.sum_inv_lt_347_div_500
