import OddPerfect.CycloRootCount
import OddPerfect.AbundancyTail

/-!
# Primes with a common receiver: one center and a bounded tail

* `exists_center_of_common_receiver`: let `d ≥ 3` and `u ≠ d` be primes and `S` a finite set
  of primes at least `B ≥ 3` such that `∑ i < d, p ^ i` is a power of `u` for every `p ∈ S`.
  Then removing at most one element of `S` (its least element) leaves a set whose product of
  `p / (p - 1)` is at most `(B ^ (d - 1) - 1) / (B ^ (d - 1) - 2)`.

Two elements `a < b` of `S` satisfy `a ^ (d - 1) < b` (`pow_lt_of_geom_sum_eq_prime_pow`).
So with `A = B ^ (d - 1)` every element after the least one is above `A`, and every interval
`(A ^ j, A ^ (j + 1)]`, `1 ≤ j`, holds at most one of them. The interval count bound
`sum_inv_pred_le_of_interval_card` gives `∑ 1 / (p - 1) ≤ 1 / (A - 1)`, and
`prod_one_add_le_inv_one_sub` turns this into the product bound.

Restricted result; no published source was checked; novelty not verified.
-/

open Finset

namespace OddPerfect

/-- **One center for a common receiver.** Let `d ≥ 3` and `u ≠ d` be primes and `S` a finite
set of primes at least `B ≥ 3` such that `∑ i < d, p ^ i` is a power of `u` for every `p ∈ S`.
Then some `C ⊆ S` with at most one element has
`∏ p ∈ S \ C, p / (p - 1) ≤ (B ^ (d - 1) - 1) / (B ^ (d - 1) - 2)`.
Restricted result; no published source was checked; novelty not verified. -/
theorem exists_center_of_common_receiver {d u B : ℕ} {S : Finset ℕ} (hd : d.Prime)
    (hd3 : 3 ≤ d) (hu : u.Prime) (hud : u ≠ d) (hB : 3 ≤ B)
    (hS : ∀ p ∈ S, p.Prime ∧ B ≤ p ∧ ∃ w, ∑ i ∈ Finset.range d, p ^ i = u ^ w) :
    ∃ C ⊆ S, C.card ≤ 1 ∧
      ∏ p ∈ S \ C, ((p : ℚ) / ((p : ℚ) - 1)) ≤
        ((B : ℚ) ^ (d - 1) - 1) / ((B : ℚ) ^ (d - 1) - 2) := by
  classical
  have hd1 : 2 ≤ d - 1 := by omega
  -- two elements of `S` are far apart
  have hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → a ^ (d - 1) < b := by
    intro a ha b hb hab
    obtain ⟨hap, -, wa, hwa⟩ := hS a ha
    obtain ⟨hbp, -, wb, hwb⟩ := hS b hb
    exact pow_lt_of_geom_sum_eq_prime_pow hd hu hud hap hbp hab hwa hwb
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = B ^ (d - 1) := ⟨_, rfl⟩
  have hA9 : 9 ≤ A := by
    rw [hA]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ B ^ 2 := Nat.pow_le_pow_left hB 2
      _ ≤ B ^ (d - 1) := Nat.pow_le_pow_right (by omega) hd1
  have hAq : (9 : ℚ) ≤ A := by exact_mod_cast hA9
  have hAcast : (B : ℚ) ^ (d - 1) = (A : ℚ) := by rw [hA, Nat.cast_pow]
  -- the tail bound for any part of `S` above `A`
  have key : ∀ T ⊆ S, (∀ p ∈ T, A < p) →
      ∏ p ∈ T, ((p : ℚ) / ((p : ℚ) - 1)) ≤ ((A : ℚ) - 1) / ((A : ℚ) - 2) := by
    intro T hT hTA
    have hband : ∀ j, 1 ≤ j →
        (T.filter (fun p => A ^ j < p ∧ p ≤ A ^ (j + 1))).card ≤ 1 := by
      intro j hj
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      by_contra hne
      have main : ∀ x ∈ T, ∀ y ∈ T, A ^ j < x → y ≤ A ^ (j + 1) → x < y → False := by
        intro x hx y hy hxj hyj hxy
        have h1 := hgap x (hT hx) y (hT hy) hxy
        have h2 : x ^ 2 ≤ x ^ (d - 1) := Nat.pow_le_pow_right (by omega) hd1
        have h3 : A ^ (j + 1) ≤ A ^ (j * 2) := Nat.pow_le_pow_right (by omega) (by omega)
        have h4 : (A ^ j) ^ 2 < x ^ 2 := Nat.pow_lt_pow_left hxj (by norm_num)
        rw [← pow_mul] at h4
        omega
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact main a ha.1 b hb.1 ha.2.1 hb.2.2 h
      · exact main b hb.1 a ha.1 hb.2.1 ha.2.2 h
    have hsum := sum_inv_pred_le_of_interval_card (s := T) (B := A) (c := 1) (by omega) hTA hband
    rw [Nat.cast_one] at hsum
    have hA1 : (0 : ℚ) < (A : ℚ) - 1 := by linarith
    have hlt : ∑ p ∈ T, (1 : ℚ) / ((p : ℚ) - 1) < 1 := by
      refine lt_of_le_of_lt hsum ?_
      rw [div_lt_one hA1]
      linarith
    have hnn : ∀ p ∈ T, (0 : ℚ) ≤ 1 / ((p : ℚ) - 1) := by
      intro p hp
      have : (A : ℚ) < p := by exact_mod_cast hTA p hp
      exact div_nonneg zero_le_one (by linarith)
    have hprod := prod_one_add_le_inv_one_sub T (fun p => (1 : ℚ) / ((p : ℚ) - 1)) hnn hlt
    have heq : ∏ p ∈ T, ((p : ℚ) / ((p : ℚ) - 1)) =
        ∏ p ∈ T, (1 + (1 : ℚ) / ((p : ℚ) - 1)) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (A : ℚ) < p := by exact_mod_cast hTA p hp
      have hne : (p : ℚ) - 1 ≠ 0 := (by linarith : (0 : ℚ) < (p : ℚ) - 1).ne'
      rw [one_add_div hne, sub_add_cancel]
    rw [heq]
    refine hprod.trans ?_
    have ht : (∑ p ∈ T, (1 : ℚ) / ((p : ℚ) - 1)) * ((A : ℚ) - 1) ≤ 1 :=
      (le_div_iff₀ hA1).1 hsum
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  rcases S.eq_empty_or_nonempty with hSe | hne
  · refine ⟨∅, empty_subset _, by simp, ?_⟩
    rw [hSe, empty_sdiff, prod_empty, hAcast, le_div_iff₀ (by linarith)]
    linarith
  · refine ⟨{S.min' hne}, singleton_subset_iff.2 (S.min'_mem hne), by simp, ?_⟩
    rw [hAcast]
    refine key _ sdiff_subset ?_
    intro p hp
    rw [mem_sdiff, mem_singleton] at hp
    have hlt : S.min' hne < p := lt_of_le_of_ne (S.min'_le p hp.1) (Ne.symm hp.2)
    have h1 := hgap _ (S.min'_mem hne) p hp.1 hlt
    have h2 : B ≤ S.min' hne := (hS _ (S.min'_mem hne)).2.1
    have h3 : A ≤ (S.min' hne) ^ (d - 1) := by
      rw [hA]
      exact Nat.pow_le_pow_left h2 _
    omega

end OddPerfect

#print axioms OddPerfect.exists_center_of_common_receiver
