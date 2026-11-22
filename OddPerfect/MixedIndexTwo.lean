import OddPerfect.MixedIndex
import OddPerfect.MixedIndexTwoData

/-!
# The mixed index family 3, 5, 7 with special prime 5: any special exponent

Let `N` be an odd perfect number in which `5` has odd exponent `k` (so `5` is the special prime
and `k ≡ 1 (mod 4)`), and suppose every prime `p ≠ 5` dividing `N` has an index
`m_p = v_p(N) + 1` divisible by `3`, `5` or `7`. This file proves:

* `not_mixed_index_special_five_three_sq`: this is impossible when `v_3(N) = 2`;
* `not_mixed_index_special_five_of_three`: this is impossible when the index of `3` is divisible
  by `3` or by `5`.

The case `k = 1` with `v_3(N) = 2` is `not_mixed_index_three_five_seven`. The exponent `k = 5`
is impossible because `7 ∣ σ(5 ^ 5)`, so `k ≥ 9` otherwise. The remaining cases are kernel
checked trees (`MixedIndexTwo.chk2`). The case where the index of `3` is divisible by `7` but
neither by `3` nor by `5` is not covered. Whether these results are new has not been verified
against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace MixedIndexTwo

open MixedIndex (isAt pow_dvd_of_le)

/-- In an odd perfect number where `5` has odd exponent, every other prime has even exponent
and the exponent of `5` is `1` or at least `9`. -/
theorem five_exponent {N : ℕ} (h : OddPerfect N) (h5o : Odd (N.factorization 5)) :
    (∀ p : ℕ, p.Prime → p ≠ 5 → Even (N.factorization p)) ∧
      (N.factorization 5 = 1 ∨ 9 ≤ N.factorization 5) := by
  obtain ⟨q, hq, -, -, hq4, hev⟩ := exists_special_prime h
  have hq5 : q = 5 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr h5o) (hev 5 Nat.prime_five (Ne.symm hne))
  subst hq5
  refine ⟨hev, ?_⟩
  have h3d : 3 ∣ N := OPNStarter.force_prime h.2 Nat.prime_five rfl Nat.prime_three
    (by norm_num) (three_dvd_sigma_five h5o)
  have h5d : 5 ∣ N := Nat.dvd_of_factorization_pos (by obtain ⟨j, hj⟩ := h5o; omega)
  have hne5 : N.factorization 5 ≠ 5 := by
    intro hk
    have h7 : 7 ∣ σ 1 (5 ^ N.factorization 5) := by
      rw [hk, sigma_one_apply_prime_pow Nat.prime_five]
      norm_num [Finset.sum_range_succ]
    exact not_seven_dvd_of_three_five h h3d h5d
      (OPNStarter.force_prime h.2 Nat.prime_five rfl (by norm_num) (by norm_num) h7)
  omega

/-- Running an accepted tree from a root with one known prime `r`. -/
theorem run {N : ℕ} (h : OddPerfect N) (h5o : Odd (N.factorization 5))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 →
      3 ∣ N.factorization p + 1 ∨ 5 ∣ N.factorization p + 1 ∨ 7 ∣ N.factorization p + 1)
    {B : List (ℕ × ℕ)} (hB : ∀ x ∈ B, (x.1 = 3 ∨ x.1 = 5) ∧ x.1 ^ x.2 ∣ N) {c3 c5 : Bool}
    (hc3 : c3 = true → N.factorization 3 = 2) (hc5 : c5 = true → N.factorization 5 = 1)
    {r : ℕ} (hr : r.Prime) (hrN : r ∣ N) (hr3 : r ≠ 3) (hr5 : r ≠ 5) {t : MixedIndex.Tr}
    (ht : ∀ p k, isAt p k t = false) (hok : chk2 primes B c3 c5 [r] [] 0 0 t = true) : False := by
  refine chk2_sound h h5o hexp primes_prime hB hc3 hc5 t [r] [] 0 0
    ⟨?_, by simp, Or.inl rfl, Or.inl rfl⟩ ?_ hok
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨hr, hrN, hr3, hr5⟩
  · intro p k hk
    rw [ht p k] at hk
    exact absurd hk Bool.false_ne_true

/-- No odd perfect number `N` has `v_3(N) = 2`, odd `v_5(N)`, and an index `v_p(N) + 1`
divisible by `3`, `5` or `7` at every prime `p ≠ 5` dividing `N`. -/
theorem not_mixed_index_special_five_three_sq {N : ℕ} (h : OddPerfect N)
    (h3 : N.factorization 3 = 2) (h5o : Odd (N.factorization 5))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 →
      3 ∣ N.factorization p + 1 ∨ 5 ∣ N.factorization p + 1 ∨ 7 ∣ N.factorization p + 1) :
    False := by
  rcases (five_exponent h h5o).2 with hk | hk
  · exact not_mixed_index_three_five_seven h h3 hk hexp
  · refine run h h5o hexp (B := [(3, 2), (5, 9)]) (c3 := true) (c5 := false) ?_ (fun _ => h3)
      (fun h' => absurd h' Bool.false_ne_true) (r := 13) (by norm_num)
      (OPNStarter.thirteen_dvd_of_three_sq h.2 h3) (by norm_num) (by norm_num)
      (fun _ _ => rfl) ok_s1
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨Or.inl rfl, pow_dvd_of_le (by simp [h3])⟩
    · exact ⟨Or.inr rfl, pow_dvd_of_le hk⟩

/-- No odd perfect number `N` has odd `v_5(N)`, an index `v_3(N) + 1` divisible by `3` or `5`,
and an index `v_p(N) + 1` divisible by `3`, `5` or `7` at every prime `p ≠ 5` dividing `N`. -/
theorem not_mixed_index_special_five_of_three {N : ℕ} (h : OddPerfect N)
    (h5o : Odd (N.factorization 5))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 →
      3 ∣ N.factorization p + 1 ∨ 5 ∣ N.factorization p + 1 ∨ 7 ∣ N.factorization p + 1)
    (h3i : 3 ∣ N.factorization 3 + 1 ∨ 5 ∣ N.factorization 3 + 1) : False := by
  obtain ⟨hev, hk⟩ := five_exponent h h5o
  have he3 := Nat.even_iff.mp (hev 3 Nat.prime_three (by norm_num))
  have hB : ∀ {e : ℕ}, e ≤ N.factorization 3 → ∀ x ∈ [(3, e), (5, if N.factorization 5 = 1
      then 1 else 9)], (x.1 = 3 ∨ x.1 = 5) ∧ x.1 ^ x.2 ∣ N := by
    intro e he x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨Or.inl rfl, pow_dvd_of_le he⟩
    · refine ⟨Or.inr rfl, pow_dvd_of_le ?_⟩
      dsimp only
      rcases hk with hk | hk <;> split_ifs <;> omega
  have hforce : ∀ a r, r.Prime → r ≠ 2 → a + 1 ∣ N.factorization 3 + 1 →
      r ∣ σ 1 (3 ^ a) → r ∣ N := fun a r hr hr2 ha hd =>
    OPNStarter.force_prime h.2 Nat.prime_three rfl hr hr2
      (hd.trans (OPNExample.sigma_prime_pow_dvd Nat.prime_three ha))
  rcases h3i with h3i | h3i
  · by_cases h2 : N.factorization 3 = 2
    · exact not_mixed_index_special_five_three_sq h h2 h5o hexp
    have h8 : 8 ≤ N.factorization 3 := by omega
    have h13 : 13 ∣ N := hforce 2 13 (by norm_num) (by norm_num) h3i (by
      rw [sigma_one_apply_prime_pow Nat.prime_three]; norm_num [Finset.sum_range_succ])
    rcases hk with hk | hk
    · have := hB h8
      simp only [hk, if_true] at this
      exact run h h5o hexp this (fun h' => absurd h' Bool.false_ne_true) (fun _ => hk)
        (by norm_num) h13 (by norm_num) (by norm_num) (fun _ _ => rfl) ok_b1
    · have := hB h8
      simp only [show N.factorization 5 ≠ 1 by omega, if_false] at this
      exact run h h5o hexp this (fun h' => absurd h' Bool.false_ne_true)
        (fun h' => absurd h' Bool.false_ne_true) (by norm_num) h13 (by norm_num) (by norm_num)
        (fun _ _ => rfl) ok_b9
  · have h4 : 4 ≤ N.factorization 3 := by omega
    have h11 : 11 ∣ N := hforce 4 11 (by norm_num) (by norm_num) h3i (by
      rw [sigma_one_apply_prime_pow Nat.prime_three]; norm_num [Finset.sum_range_succ])
    rcases hk with hk | hk
    · have := hB h4
      simp only [hk, if_true] at this
      exact run h h5o hexp this (fun h' => absurd h' Bool.false_ne_true) (fun _ => hk)
        (by norm_num) h11 (by norm_num) (by norm_num) (fun _ _ => rfl) ok_c1
    · have := hB h4
      simp only [show N.factorization 5 ≠ 1 by omega, if_false] at this
      exact run h h5o hexp this (fun h' => absurd h' Bool.false_ne_true)
        (fun h' => absurd h' Bool.false_ne_true) (by norm_num) h11 (by norm_num) (by norm_num)
        (fun _ _ => rfl) ok_c9

end MixedIndexTwo

end OddPerfect

#print axioms OddPerfect.MixedIndexTwo.five_exponent
#print axioms OddPerfect.MixedIndexTwo.run
#print axioms OddPerfect.MixedIndexTwo.not_mixed_index_special_five_three_sq
#print axioms OddPerfect.MixedIndexTwo.not_mixed_index_special_five_of_three
