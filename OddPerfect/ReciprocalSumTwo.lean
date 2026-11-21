import OddPerfect.ReciprocalSum

/-!
# A sharper lower bound for the reciprocal sum of the prime factors

For an odd perfect number `N` we prove `29/50 < ∑_{p ∣ N} 1/p` and `581/1000 < ∑_{p ∣ N} 1/p`.

This is a known kind of estimate (Suryanarayana; Cohen 1978 has stronger constants obtained with a
case analysis). No claim of novelty is made: the proof only extends the finite computation of
`OddPerfect.twentythree_fortieths_lt_sum_inv`.

Write `c(p) = log(p/(p-1)) - 1/p`, so `log 2 < ∑ 1/p + ∑ c(p)`. For an odd cutoff `B`:

* the prime factors `p ≥ B` contribute at most `(1/4) * 1/(B - 2)` to `∑ c(p)`;
* each odd prime `p < B` satisfies `c(p) ≤ u p`, an explicit rational number from the
  truncated series of `-log(1 - 1/p)`;
* the prime factors below `B` lie in an explicit list `L` of the odd primes below `B` (the cover
  is checked by trial division) and miss one of `3, 5, 7` (since `105 ∤ N`); as `u 7` is the
  smallest of `u 3, u 5, u 7`, their contribution is at most `∑_{p ∈ L} u p - u 7`.

The resulting rational inequality is checked by the kernel.
-/

open Finset

namespace OddPerfect

/-- The rational upper bound for `log(p/(p-1)) - 1/p`:
`∑_{k=2}^{12} 1/(k p^k) + (1/p)^13/(1 - 1/p)`. -/
def corrBound (p : ℕ) : ℚ :=
  ∑ i ∈ range 11, (1 / (p : ℚ)) ^ (i + 2) / ((i : ℚ) + 2) + (1 / (p : ℚ)) ^ 13 / (1 - 1 / (p : ℚ))

/-- The finite cover check: every entry of `L` is at least `3`, and every `p < B` is less
than `3`, lies in `L`, or has a divisor `d` with `2 ≤ d < min(p, K)`. -/
def coverCheck (B K : ℕ) (L : List ℕ) : Bool :=
  L.all (fun p => 3 ≤ p) &&
    (List.range B).all fun p =>
      p < 3 || L.contains p || (List.range K).any fun d => 2 ≤ d && d < p && p % d == 0

/-- `corrBound p` is positive for `p ≥ 2`. -/
theorem corrBound_pos {p : ℕ} (hp : 2 ≤ p) : 0 < corrBound p := by
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have hx : (1 : ℚ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
  unfold corrBound
  have h1 : 0 < (1 / (p : ℚ)) ^ 13 / (1 - 1 / (p : ℚ)) :=
    div_pos (pow_pos (by positivity) _) (by linarith)
  have h2 : 0 ≤ ∑ i ∈ range 11, (1 / (p : ℚ)) ^ (i + 2) / ((i : ℚ) + 2) :=
    Finset.sum_nonneg fun i _ => by positivity
  linarith

/-- `log(p/(p-1)) - 1/p ≤ corrBound p` for every natural `p ≥ 2`. -/
theorem log_div_sub_one_sub_inv_le_corrBound {p : ℕ} (hp : 2 ≤ p) :
    Real.log ((p : ℝ) / (p - 1)) - 1 / p ≤ (corrBound p : ℝ) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [log_div_sub_one_eq (by linarith)]
  have h := neg_log_one_sub_le (x := 1 / (p : ℝ)) (by positivity)
    (by rw [div_lt_one (by linarith)]; linarith) 12
  have e : ∑ i ∈ range 12, (1 / (p : ℝ)) ^ (i + 1) / ((i : ℝ) + 1) =
      ∑ i ∈ range 11, (1 / (p : ℝ)) ^ (i + 2) / ((i : ℝ) + 2) + 1 / p := by
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring_nf
    · simp
  unfold corrBound
  push_cast
  linarith

/-- A passed cover check puts every odd prime below `B` in `L`. -/
theorem mem_of_coverCheck {B K : ℕ} {L : List ℕ} (hc : coverCheck B K L = true) {p : ℕ}
    (hpB : p < B) (hp : p.Prime) (hp2 : p ≠ 2) : p ∈ L := by
  simp only [coverCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, List.contains_iff_mem, List.any_eq_true, beq_iff_eq] at hc
  rcases hc.2 p hpB with (h3 | hmem) | ⟨d, -, ⟨h2d, hdp⟩, hd⟩
  · have := hp.two_le
    omega
  · exact hmem
  · rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hd) with h | h <;> omega

/-- A passed cover check makes every entry of `L` at least `3`. -/
theorem three_le_of_mem_coverCheck {B K : ℕ} {L : List ℕ} (hc : coverCheck B K L = true)
    {p : ℕ} (hp : p ∈ L) : 3 ≤ p := by
  simp only [coverCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  exact hc.1 p hp

private theorem corrBound_seven_le : corrBound 7 ≤ corrBound 3 ∧ corrBound 7 ≤ corrBound 5 := by
  decide +kernel

/-- The generic transfer: a checked rational inequality for a cutoff `B` and a list `L` of the
odd primes below `B` gives the lower bound `t < ∑_{p ∣ N} 1/p` for every odd perfect `N`. -/
theorem lt_sum_inv_of_check {N : ℕ} (h : OddPerfect N) (B K : ℕ) (L : List ℕ) (t : ℚ)
    (hB : 9 ≤ B) (hBo : Odd B) (hc : coverCheck B K L = true) (hnd : L.Nodup)
    (hchk : t + ((L.map corrBound).sum - corrBound 7) + 1 / (4 * ((B : ℚ) - 2)) ≤
      6931471803 / 10000000000) :
    (t : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  set S := N.primeFactors with hS
  set f : ℕ → ℝ := fun p => Real.log ((p : ℝ) / (p - 1)) - 1 / p with hf
  have hodd : ∀ p ∈ S, 3 ≤ p ∧ Odd p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have ho : Odd p := h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    refine ⟨?_, ho⟩
    have := hp'.two_le
    obtain ⟨k, rfl⟩ := ho
    omega
  have hsplit : ∑ p ∈ S, Real.log ((p : ℝ) / (p - 1)) = ∑ p ∈ S, 1 / (p : ℝ) + ∑ p ∈ S, f p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by simp only [f]; ring
  -- one of 3, 5, 7 is not a prime factor
  have hm : ∃ m, (m = 3 ∨ m = 5 ∨ m = 7) ∧ m ∉ S := by
    have hn105 := not_105_dvd h
    by_contra hcon
    push Not at hcon
    have d3 := Nat.dvd_of_mem_primeFactors (hcon 3 (Or.inl rfl))
    have d5 := Nat.dvd_of_mem_primeFactors (hcon 5 (Or.inr (Or.inl rfl)))
    have d7 := Nat.dvd_of_mem_primeFactors (hcon 7 (Or.inr (Or.inr rfl)))
    exact hn105 (by omega)
  obtain ⟨m, hm357, hmS⟩ := hm
  have hmL : m ∈ L.toFinset := by
    rw [List.mem_toFinset]
    refine mem_of_coverCheck hc (by omega) ?_ (by omega)
    rcases hm357 with rfl | rfl | rfl <;> norm_num
  -- the head
  have hsub : S.filter (· < B) ⊆ L.toFinset.erase m := by
    intro p hp
    rw [Finset.mem_filter] at hp
    refine Finset.mem_erase.mpr ⟨fun hpm => hmS (hpm ▸ hp.1), List.mem_toFinset.mpr ?_⟩
    have := (hodd p hp.1).1
    exact mem_of_coverCheck hc hp.2 (Nat.prime_of_mem_primeFactors hp.1) (by omega)
  have hheadQ : ∑ p ∈ S.filter (· < B), corrBound p ≤
      (L.map corrBound).sum - corrBound 7 := by
    have hpos : ∀ p ∈ L.toFinset.erase m, p ∉ S.filter (· < B) → 0 ≤ corrBound p := by
      intro p hp _
      exact (corrBound_pos (by
        have := three_le_of_mem_coverCheck hc
          (List.mem_toFinset.mp (Finset.mem_of_mem_erase hp)); omega)).le
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hpos).trans ?_
    rw [Finset.sum_erase_eq_sub hmL, List.sum_toFinset _ hnd]
    have := corrBound_seven_le
    rcases hm357 with rfl | rfl | rfl <;> linarith
  have hhead : ∑ p ∈ S.filter (· < B), f p ≤
      (((L.map corrBound).sum - corrBound 7 : ℚ) : ℝ) := by
    refine (Finset.sum_le_sum fun p hp => ?_).trans
      (le_of_eq_of_le (Rat.cast_sum _ _).symm ((Rat.cast_le (K := ℝ)).mpr hheadQ))
    have := (hodd p (Finset.mem_filter.mp hp).1).1
    exact log_div_sub_one_sub_inv_le_corrBound (by omega)
  -- the tail
  have htail : ∑ p ∈ S.filter (fun p => ¬ p < B), f p ≤ (1 / 4) * (1 / ((B : ℝ) - 2)) := by
    have hT : ∀ p ∈ S.filter (fun p => ¬ p < B), Odd p ∧ B ≤ p := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact ⟨(hodd p hp.1).2, by omega⟩
    calc ∑ p ∈ S.filter (fun p => ¬ p < B), f p
        ≤ ∑ p ∈ S.filter (fun p => ¬ p < B), (1 / 4) * (1 / ((p : ℝ) - 2) - 1 / p) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have : (3 : ℝ) ≤ p := by exact_mod_cast (by have := (hT p hp).2; omega : 3 ≤ p)
          exact log_div_sub_one_sub_inv_le this
      _ = (1 / 4) * ∑ p ∈ S.filter (fun p => ¬ p < B), (1 / ((p : ℝ) - 2) - 1 / p) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / 4) * (1 / ((B : ℝ) - 2)) := by
          gcongr
          exact sum_telescope_le (by omega) hBo hT
  have hsum := Finset.sum_filter_add_sum_filter_not S (· < B) f
  have hlog := log_two_lt_sum_log h
  have hl2 := Real.log_two_gt_d9
  rw [← hS, hsplit] at hlog
  have hchkR := (Rat.cast_le (K := ℝ)).mpr hchk
  have hB' : (9 : ℝ) ≤ B := by exact_mod_cast hB
  have e : (1 / 4 : ℝ) * (1 / ((B : ℝ) - 2)) = 1 / (4 * ((B : ℝ) - 2)) := by
    field_simp
  push_cast at hchkR hhead
  norm_num at hl2
  linarith

/-- For an odd perfect number, `29/50 < ∑_{p ∣ N} 1/p` (cutoff `B = 101`). -/
theorem twentynine_fiftieths_lt_sum_inv {N : ℕ} (h : OddPerfect N) :
    (29 / 50 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  have := lt_sum_inv_of_check h 101 11
    [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    (29 / 50) (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  push_cast at this
  exact this

/-- For an odd perfect number, `581/1000 < ∑_{p ∣ N} 1/p` (cutoff `B = 1009`). -/
theorem sum_inv_gt_581_div_1000 {N : ℕ} (h : OddPerfect N) :
    (581 / 1000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  have := lt_sum_inv_of_check h 1009 32
    [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
     101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
     193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
     293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401,
     409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509,
     521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631,
     641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
     757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877,
     881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]
    (581 / 1000) (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  push_cast at this
  exact this

end OddPerfect

#print axioms OddPerfect.corrBound_pos
#print axioms OddPerfect.log_div_sub_one_sub_inv_le_corrBound
#print axioms OddPerfect.mem_of_coverCheck
#print axioms OddPerfect.three_le_of_mem_coverCheck
#print axioms OddPerfect.lt_sum_inv_of_check
#print axioms OddPerfect.twentynine_fiftieths_lt_sum_inv
#print axioms OddPerfect.sum_inv_gt_581_div_1000
