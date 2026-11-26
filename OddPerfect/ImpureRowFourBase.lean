import OddPerfect.ImpureRowBase
import OddPerfect.SpecialPrime
import OddPerfect.Valuation
import OddPerfect.Abundancy

/-!
# At least four impure rows for a common prime index `l ≥ 523`: version with a hypothesis

This module proves the count (C) of `ImpureRowCountFour` in a version that takes the packing
statement `PackingStatement` as a hypothesis. Setting: `N` odd perfect with special prime `q`,
`l ≥ 523` a prime dividing every ordinary index `e_p + 1`, and `M` a finite set containing every
ordinary prime whose row `σ(p ^ e_p)` is not a prime power. Then `M` has at least four elements.

Argument. If `M` has at most three elements, the packing bound leaves a set `D` of at most three
odd primes (besides `l`) whose factors `p/(p-1)` must carry the product above `2`. This forces
`D = {3, 5, c}` with `c ∈ {7, 11, 13}`. The case `c = 7` gives `105 ∣ N`. For `c ∈ {11, 13}`,
a divisor `3 ^ 4 · 5 ^ 4 · c ^ 4` or `3 ^ 4 · 5 ^ 4 · 13` of `N` has abundancy above `2` unless
`q = 5` with exponent `1`, and then `∏ p/(p-1) ≥ 25/12`, which the packing bound excludes.

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem two_lt_abundancy_3_5_11 : 2 < abundancy (3 ^ 4 * 5 ^ 4 * 11 ^ 4) := by
  rw [abundancy_mul_of_coprime (by norm_num), abundancy_mul_of_coprime (by norm_num),
    abundancy_prime_pow (by norm_num), abundancy_prime_pow (by norm_num),
    abundancy_prime_pow (by norm_num)]
  norm_num [Finset.sum_range_succ]

private theorem two_lt_abundancy_3_5_13 : 2 < abundancy (3 ^ 4 * 5 ^ 4 * 13 ^ 4) := by
  rw [abundancy_mul_of_coprime (by norm_num), abundancy_mul_of_coprime (by norm_num),
    abundancy_prime_pow (by norm_num), abundancy_prime_pow (by norm_num),
    abundancy_prime_pow (by norm_num)]
  norm_num [Finset.sum_range_succ]

private theorem two_lt_abundancy_3_5_13_one : 2 < abundancy (3 ^ 4 * 5 ^ 4 * 13 ^ 1) := by
  rw [abundancy_mul_of_coprime (by norm_num), abundancy_mul_of_coprime (by norm_num),
    abundancy_prime_pow (by norm_num), abundancy_prime_pow (by norm_num),
    abundancy_prime_pow (by norm_num)]
  norm_num [Finset.sum_range_succ]

/-- **The prime 5 is special with exponent 1.** Let `N` be an odd perfect number with special
prime `q`, `l ≥ 5` a prime dividing every ordinary index, and `3`, `5`, `c` divisors of `N`
with `c ∈ {11, 13}`. Then `q = 5` and `v_5(N) = 1`. -/
theorem impureRow_five_special {N q l c : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl5 : 5 ≤ l)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (hc : c = 11 ∨ c = 13)
    (h3 : 3 ∣ N) (h5 : 5 ∣ N) (hcN : c ∣ N) : q = 5 ∧ N.factorization 5 = 1 := by
  have hord : ∀ p, p.Prime → p ∣ N → p ≠ q → p ^ 4 ∣ N := by
    intro p hp hpN hpq
    have hd := hidx p (Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩) hpq
    have := Nat.le_of_dvd (Nat.succ_pos _) hd
    exact (hp.pow_dvd_iff_le_factorization h.ne_zero).mpr (by omega)
  obtain ⟨hq4, he4⟩ := mod_four_special h hq hodd
  have h81 : 3 ^ 4 ∣ N := hord 3 Nat.prime_three h3 (by rintro rfl; norm_num at hq4)
  have hnp := h.perfect
  by_cases hcq : c = q
  · exfalso
    have hc1 : c % 4 = 1 := by rw [hcq]; exact hq4
    have hc13 : c = 13 := by rcases hc with hc | hc <;> omega
    have h625 : 5 ^ 4 ∣ N := hord 5 (by norm_num) h5 (by omega)
    rw [hc13] at hcN
    have hd : 3 ^ 4 * 5 ^ 4 * 13 ^ 1 ∣ N :=
      (show Nat.Coprime (3 ^ 4 * 5 ^ 4) (13 ^ 1) by norm_num).mul_dvd_of_dvd_of_dvd
        ((show Nat.Coprime (3 ^ 4) (5 ^ 4) by norm_num).mul_dvd_of_dvd_of_dvd h81 h625)
        (by rw [pow_one]; exact hcN)
    exact not_perfect_of_dvd_of_two_lt_abundancy hd two_lt_abundancy_3_5_13_one hnp
  · have hc4 : c ^ 4 ∣ N := hord c (by rcases hc with rfl | rfl <;> norm_num) hcN hcq
    by_cases h5q : q = 5 ∧ N.factorization 5 = 1
    · exact h5q
    · exfalso
      have h625 : 5 ^ 4 ∣ N := by
        by_cases hq5 : q = 5
        · subst hq5
          have hne : N.factorization 5 ≠ 1 := fun e => h5q ⟨rfl, e⟩
          exact ((by norm_num : Nat.Prime 5).pow_dvd_iff_le_factorization h.ne_zero).mpr
            (by omega)
        · exact hord 5 (by norm_num) h5 (Ne.symm hq5)
      have h3c5 : 3 ^ 4 * 5 ^ 4 ∣ N :=
        (show Nat.Coprime (3 ^ 4) (5 ^ 4) by norm_num).mul_dvd_of_dvd_of_dvd h81 h625
      rcases hc with rfl | rfl
      · exact not_perfect_of_dvd_of_two_lt_abundancy
          ((show Nat.Coprime (3 ^ 4 * 5 ^ 4) (11 ^ 4) by norm_num).mul_dvd_of_dvd_of_dvd
            h3c5 hc4) two_lt_abundancy_3_5_11 hnp
      · exact not_perfect_of_dvd_of_two_lt_abundancy
          ((show Nat.Coprime (3 ^ 4 * 5 ^ 4) (13 ^ 4) by norm_num).mul_dvd_of_dvd_of_dvd
            h3c5 hc4) two_lt_abundancy_3_5_13 hnp

/-- **A special prime 5 with exponent 1 raises `∏ p/(p-1)` to `25/12`.** If `N` is an odd
perfect number with `v_5(N) = 1`, then `∏ p/(p-1)` over the prime factors of `N` is at least
`25/12`. -/
theorem impureRow_prod_ge_of_five {N : ℕ} (h : OddPerfect N) (h5 : 5 ∈ N.primeFactors)
    (he : N.factorization 5 = 1) :
    (25 : ℚ) / 12 ≤ ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have h56 : abundancy (5 ^ 1) = 6 / 5 := by
    rw [abundancy_prime_pow (by norm_num)]
    norm_num [Finset.sum_range_succ]
  have h54 : ((5 : ℕ) : ℚ) / (((5 : ℕ) : ℚ) - 1) = 5 / 4 := by norm_num
  rw [abundancy_eq_prod_primeFactors h.ne_zero, ← Finset.mul_prod_erase _ _ h5, he, h56] at hab
  have hle : ∏ p ∈ N.primeFactors.erase 5, abundancy (p ^ N.factorization p) ≤
      ∏ p ∈ N.primeFactors.erase 5, ((p : ℚ) / ((p : ℚ) - 1)) :=
    Finset.prod_le_prod₀ (fun p _ => by unfold abundancy; positivity)
      (fun p hp => (abundancy_prime_pow_lt
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) _).le)
  rw [← Finset.mul_prod_erase _ _ h5, h54]
  linarith

/-- **(C) with the packing statement as a hypothesis.** See `four_le_card_of_pure_outside`.
Restricted result; no published source was checked; novelty not verified. -/
theorem four_le_card_of_pure_outside_of (hpack : PackingStatement) {N q l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hl523 : 523 ≤ l) (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : 4 ≤ M.card := by
  by_contra hlt
  have hK : 4 + 1 < 3 ^ (l - 1) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 6 ≤ l - 1))
  obtain ⟨D, hDc, hD, hbound⟩ :=
    impureRow_setup_of hpack h hq hodd hl (by omega) hidx M hM (by omega) hK
  -- The numerical constant `B ≥ l/(l-1) · T(l, 4)`, with the tail bounded through `3 ^ 20`.
  obtain ⟨B, hB0, hBl, hB1, hB2⟩ : ∃ B : ℚ, 0 ≤ B ∧
      (l : ℚ) / ((l : ℚ) - 1) * impureRowT l 4 ≤ B ∧ B * (255 / 128) < 2 ∧
      B * (33 / 16) < 25 / 12 := by
    have hT := impureRowT_le (L := 523) (m := 20) (by norm_num) hl523 (by omega)
      (by norm_num : ((4 : ℕ) : ℚ) < 3 ^ 20 - 1)
    have hH := impureRow_H_anti (by norm_num) hl523
    refine ⟨((523 : ℕ) : ℚ) / (((523 : ℕ) : ℚ) - 1) *
      ((∏ j ∈ Finset.range 4,
          (((2 * (j + 1) * 523 + 1 : ℕ) : ℚ) / ((2 * (j + 1) * 523 : ℕ) : ℚ))) *
        (((3 : ℚ) ^ 20 - 1) / ((3 : ℚ) ^ 20 - 1 - ((4 : ℕ) : ℚ)))),
      by norm_num [Finset.prod_range_succ], ?_, by norm_num [Finset.prod_range_succ],
      by norm_num [Finset.prod_range_succ]⟩
    exact mul_le_mul hH hT (impureRowT_nonneg hK) (by norm_num)
  have hE0 : 0 ≤ ∏ p ∈ D, ((p : ℚ) / ((p : ℚ) - 1)) :=
    impureRow_prod_H_nonneg fun x hx => (hD x hx).1.two_le
  have hmain : ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) ≤
      B * ∏ p ∈ D, ((p : ℚ) / ((p : ℚ) - 1)) := by
    have := mul_le_mul_of_nonneg_right hBl hE0
    linarith
  have h2 := two_lt_prod_primeFactors_div h
  have hsmall : ∏ p ∈ D, ((p : ℚ) / ((p : ℚ) - 1)) ≤ 255 / 128 → False := fun hE => by
    linarith [mul_le_mul_of_nonneg_left hE hB0]
  have hDodd : ∀ x ∈ D, Odd x ∧ 3 ≤ x := fun x hx =>
    impureRow_odd_of_prime (hD x hx).1 (hD x hx).2.1
  by_cases h3D : 3 ∈ D
  swap
  · -- No `3`: at most three odd numbers at least `5`.
    apply hsmall
    have hle := impureRow_prod_H_odd_le 3 (D := D) (a := 4) (by norm_num) (by omega)
      (fun x hx => (hDodd x hx).1) (fun x hx => by
        have := (hDodd x hx).2
        have : x ≠ 3 := fun e => h3D (e ▸ hx)
        omega)
    have hn : ∏ i ∈ Finset.range 3, (((4 + 2 * i : ℕ) : ℚ) / (((4 + 2 * i : ℕ) : ℚ) - 1)) ≤
        255 / 128 := by
      norm_num [Finset.prod_range_succ]
    linarith
  have hE3 := (Finset.mul_prod_erase D (fun p => (p : ℚ) / ((p : ℚ) - 1)) h3D).symm
  have hc3 : D.card ≤ 3 := by omega
  have hc2 : (D.erase 3).card ≤ 2 := by rw [Finset.card_erase_of_mem h3D]; omega
  have h0 : (0 : ℚ) ≤ ((3 : ℕ) : ℚ) / (((3 : ℕ) : ℚ) - 1) := by norm_num
  have h0' : (0 : ℚ) ≤ ((5 : ℕ) : ℚ) / (((5 : ℕ) : ℚ) - 1) := by norm_num
  by_cases h5D : 5 ∈ D.erase 3
  swap
  · -- `3` without `5`: the other two are odd and at least `7`.
    apply hsmall
    rw [hE3]
    have hle := impureRow_prod_H_odd_le 2 (D := D.erase 3) (a := 7) (by norm_num) hc2
      (fun x hx => (hDodd x (Finset.mem_of_mem_erase hx)).1) (fun x hx => by
        obtain ⟨hx3, hxD⟩ := Finset.mem_erase.mp hx
        have hx5 : x ≠ 5 := fun e => h5D (e ▸ hx)
        obtain ⟨u, hu⟩ := (hDodd x hxD).1
        have := (hDodd x hxD).2
        omega)
    have hn : ((3 : ℕ) : ℚ) / (((3 : ℕ) : ℚ) - 1) *
        ∏ i ∈ Finset.range 2, (((7 + 2 * i : ℕ) : ℚ) / (((7 + 2 * i : ℕ) : ℚ) - 1)) ≤
        255 / 128 := by
      norm_num [Finset.prod_range_succ]
    exact (mul_le_mul_of_nonneg_left hle h0).trans hn
  have hE5 := (Finset.mul_prod_erase (D.erase 3) (fun p => (p : ℚ) / ((p : ℚ) - 1)) h5D).symm
  have hc1 : ((D.erase 3).erase 5).card ≤ 1 := by
    rw [Finset.card_erase_of_mem h5D]; omega
  have hD2 : ∀ x ∈ (D.erase 3).erase 5, x ∈ D ∧ x ≠ 3 ∧ x ≠ 5 := fun x hx => by
    obtain ⟨hx5, hx'⟩ := Finset.mem_erase.mp hx
    obtain ⟨hx3, hxD⟩ := Finset.mem_erase.mp hx'
    exact ⟨hxD, hx3, hx5⟩
  have h3N : 3 ∣ N := (hD 3 h3D).2.2.2
  have h5N : 5 ∣ N := (hD 5 (Finset.mem_of_mem_erase h5D)).2.2.2
  by_cases hc : ∃ c ∈ (D.erase 3).erase 5, c < 17
  · obtain ⟨c, hcD2, hc17⟩ := hc
    obtain ⟨hcD, hc3', hc5'⟩ := hD2 c hcD2
    have hcP := (hD c hcD).1
    have hcN := (hD c hcD).2.2.2
    have hD2eq : (D.erase 3).erase 5 = {c} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hcD2, fun x hx => Finset.card_le_one.mp hc1 x hx c hcD2⟩
    have hc7 : 7 ≤ c := by
      obtain ⟨u, hu⟩ := (hDodd c hcD).1
      have := (hDodd c hcD).2
      omega
    have hcases : c = 7 ∨ c = 11 ∨ c = 13 := by
      interval_cases c <;> first | omega | (exfalso; norm_num at hcP)
    have hE : 11 ≤ c → ∏ p ∈ D, ((p : ℚ) / ((p : ℚ) - 1)) ≤ 33 / 16 := fun hc11 => by
      rw [hE3, hE5, hD2eq, Finset.prod_singleton]
      have hH := impureRow_H_anti (by norm_num) hc11
      have hn : ((3 : ℕ) : ℚ) / (((3 : ℕ) : ℚ) - 1) * (((5 : ℕ) : ℚ) / (((5 : ℕ) : ℚ) - 1) *
          (((11 : ℕ) : ℚ) / (((11 : ℕ) : ℚ) - 1))) ≤ 33 / 16 := by norm_num
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH h0') h0).trans hn
    have h5P : 5 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h5N, h.ne_zero⟩
    rcases hcases with h7 | h11 | h13
    · rw [h7] at hcN
      have h105 : 3 * 5 * 7 ∣ N :=
        (show Nat.Coprime (3 * 5) 7 by norm_num).mul_dvd_of_dvd_of_dvd
          ((show Nat.Coprime 3 5 by norm_num).mul_dvd_of_dvd_of_dvd h3N h5N) hcN
      exact not_105_dvd h (by norm_num at h105; exact h105)
    · obtain ⟨-, he5⟩ := impureRow_five_special h hq hodd (by omega) hidx (Or.inl h11) h3N h5N
        hcN
      have hge := impureRow_prod_ge_of_five h h5P he5
      linarith [mul_le_mul_of_nonneg_left (hE (by omega)) hB0]
    · obtain ⟨-, he5⟩ := impureRow_five_special h hq hodd (by omega) hidx (Or.inr h13) h3N h5N
        hcN
      have hge := impureRow_prod_ge_of_five h h5P he5
      linarith [mul_le_mul_of_nonneg_left (hE (by omega)) hB0]
  · -- `3`, `5` and possibly one more element, at least `17`.
    have hc' : ∀ x ∈ (D.erase 3).erase 5, 17 ≤ x := fun x hx => by
      by_contra hlt
      exact hc ⟨x, hx, by omega⟩
    apply hsmall
    rw [hE3, hE5]
    have hle := impureRow_prod_H_odd_le 1 (D := (D.erase 3).erase 5) (a := 17) (by norm_num)
      hc1 (fun x hx => (hDodd x (hD2 x hx).1).1) hc'
    have hn : ((3 : ℕ) : ℚ) / (((3 : ℕ) : ℚ) - 1) * (((5 : ℕ) : ℚ) / (((5 : ℕ) : ℚ) - 1) *
        ∏ i ∈ Finset.range 1, (((17 + 2 * i : ℕ) : ℚ) / (((17 + 2 * i : ℕ) : ℚ) - 1))) ≤
        255 / 128 := by
      norm_num [Finset.prod_range_succ]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle h0') h0).trans hn

end OddPerfect

#print axioms OddPerfect.impureRow_five_special
#print axioms OddPerfect.impureRow_prod_ge_of_five
#print axioms OddPerfect.four_le_card_of_pure_outside_of
