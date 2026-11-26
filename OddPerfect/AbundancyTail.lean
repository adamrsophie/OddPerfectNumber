import OddPerfect.Abundancy
import OddPerfect.ProductBound

/-!
# The abundancy product and a tail bound by interval counts

* `prod_one_add_le_inv_one_sub`: for `0 ≤ x i` with `∑ x i < 1`,
  `∏ (1 + x i) ≤ 1 / (1 - ∑ x i)`.
* `two_lt_prod_primeFactors_div`: an odd perfect number `N` has
  `2 < ∏ p / (p - 1)` over its prime factors (a corollary of `abundancy_lt_prod` and
  `perfect_iff_abundancy_eq_two`).
* `sum_inv_pred_le_of_interval_card`: if every interval `(B ^ j, B ^ (j + 1)]`, `1 ≤ j`, holds
  at most `c` elements of a finite set `s` of integers above `B`, then
  `∑ 1 / (p - 1) ≤ c / (B - 1)`.

Restricted result; no published source was checked; novelty not verified.
-/

open Finset

namespace OddPerfect

theorem prod_one_add_le_inv_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℚ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hs : ∑ i ∈ s, x i < 1) :
    ∏ i ∈ s, (1 + x i) ≤ 1 / (1 - ∑ i ∈ s, x i) := by
  have h0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hx
  refine (prod_one_add_le_pade11 s x hx le_rfl (by linarith)).trans ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- A perfect number has `2 < ∏ p / (p - 1)` over its prime factors. -/
theorem two_lt_prod_primeFactors_div {N : ℕ} (h : OddPerfect N) :
    (2 : ℚ) < ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
  have hN1 : 1 < N := by
    rcases Nat.lt_or_ge 1 N with h1 | h1
    · exact h1
    · exfalso
      have h1' : N = 1 := by have := h.pos; omega
      have := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
      rw [h1', abundancy] at this
      norm_num at this
  have h2 := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have := abundancy_lt_prod hN1
  rwa [h2] at this

/-- If every interval `(B ^ j, B ^ (j + 1)]`, `1 ≤ j`, holds at most `c` elements of `s`, and
every element of `s` exceeds `B`, then `∑ 1 / (p - 1) ≤ c / (B - 1)`. -/
theorem sum_inv_pred_le_of_interval_card {s : Finset ℕ} {B c : ℕ} (hB : 2 ≤ B)
    (hs : ∀ p ∈ s, B < p)
    (hc : ∀ j, 1 ≤ j → (s.filter (fun p => B ^ j < p ∧ p ≤ B ^ (j + 1))).card ≤ c) :
    ∑ p ∈ s, (1 : ℚ) / ((p : ℚ) - 1) ≤ (c : ℚ) / ((B : ℚ) - 1) := by
  set f : ℕ → ℕ := fun p => Nat.log B (p - 1) with hf
  have hB1 : 1 < B := by omega
  have hBq : (2 : ℚ) ≤ B := by exact_mod_cast hB
  -- the block of `p`
  have hblock : ∀ p ∈ s, ∀ j, f p = j ↔ B ^ j < p ∧ p ≤ B ^ (j + 1) := by
    intro p hp j
    have hp' := hs p hp
    rw [hf]
    dsimp only
    rw [Nat.log_eq_iff (Or.inr ⟨hB1, by omega⟩)]
    have : 0 < B ^ j := pow_pos (by omega) j
    omega
  have hf1 : ∀ p ∈ s, 1 ≤ f p := by
    intro p hp
    have hp' := hs p hp
    rw [hf]
    dsimp only
    exact Nat.le_log_of_pow_le hB1 (by rw [pow_one]; omega)
  set M := s.sup f + 1 with hM
  have hmaps : ∀ p ∈ s, f p ∈ Ico 1 M := by
    intro p hp
    rw [mem_Ico]
    exact ⟨hf1 p hp, Nat.lt_succ_of_le (le_sup (f := f) hp)⟩
  set a : ℚ := 1 / (B : ℚ) with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one (by linarith)]; linarith
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ j ∈ Ico 1 M, ∑ p ∈ s with f p = j, (1 : ℚ) / ((p : ℚ) - 1)
      ≤ ∑ j ∈ Ico 1 M, (c : ℚ) * a ^ j := by
        refine sum_le_sum fun j hj => ?_
        have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
        have hterm : ∀ p ∈ s.filter (fun p => f p = j), (1 : ℚ) / ((p : ℚ) - 1) ≤ a ^ j := by
          intro p hp
          obtain ⟨hps, hpj⟩ := mem_filter.mp hp
          have hlt := ((hblock p hps j).mp hpj).1
          have hle : ((B ^ j : ℕ) : ℚ) + 1 ≤ (p : ℚ) := by exact_mod_cast hlt
          push_cast at hle
          have hBj : (0 : ℚ) < (B : ℚ) ^ j := by positivity
          rw [ha, div_pow, one_pow]
          exact one_div_le_one_div_of_le hBj (by linarith)
        have hcard : (s.filter (fun p => f p = j)).card ≤ c := by
          have hcong : s.filter (fun p => f p = j) =
              s.filter (fun p => B ^ j < p ∧ p ≤ B ^ (j + 1)) :=
            filter_congr fun p hp => hblock p hp j
          rw [hcong]
          exact hc j hj1
        calc ∑ p ∈ s with f p = j, (1 : ℚ) / ((p : ℚ) - 1)
            ≤ (s.filter (fun p => f p = j)).card • a ^ j := sum_le_card_nsmul _ _ _ hterm
          _ ≤ (c : ℚ) * a ^ j := by
            rw [nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg ha0 j)
    _ = (c : ℚ) * ∑ j ∈ Ico 1 M, a ^ j := by rw [mul_sum]
    _ ≤ (c : ℚ) * (a ^ 1 / (1 - a)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one ha0 ha1) (Nat.cast_nonneg c)
    _ = (c : ℚ) / ((B : ℚ) - 1) := by
        rw [ha, pow_one]
        have hB0 : (B : ℚ) ≠ 0 := by linarith
        have hB10 : (B : ℚ) - 1 ≠ 0 := by linarith
        field_simp

end OddPerfect

#print axioms OddPerfect.prod_one_add_le_inv_one_sub
#print axioms OddPerfect.two_lt_prod_primeFactors_div
#print axioms OddPerfect.sum_inv_pred_le_of_interval_card
