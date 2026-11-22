import OddPerfect.MixedIndexTwo
import OddPerfect.MixedIndexThreeData1
import OddPerfect.MixedIndexThreeData2
import OddPerfect.MixedIndexThreeData3
import OddPerfect.MixedIndexThreeData4
import OddPerfect.MixedIndexThreeData5

/-!
# The mixed index family 3, 5, 7 with special prime 5

Let `N` be an odd perfect number in which `5` has odd exponent (so `5` is the special prime).
This file proves that some prime `p ≠ 5` dividing `N` has an index `m_p = v_p(N) + 1` divisible
by none of `3`, `5`, `7` (`not_mixed_index_special_five`).

The index of `3` divisible by `3` or by `5` is excluded by
`MixedIndexTwo.not_mixed_index_special_five_of_three`. Otherwise `7` divides the index of `3`,
so `v_3(N) ≥ 6` and `σ(3 ^ 6) = 1093` divides `σ(3 ^ v_3(N))` and hence `N`. From the root
`1093 ∣ N`, with the fixed divisor `3 ^ 6 * 5` (special exponent `1`, capacity `1` at `5`) or
`3 ^ 6 * 5 ^ 9` (special exponent at least `9`), kernel checked trees (`MixedIndexThree.chk3`)
close every branch. No exact exponent of `3` and no capacity rule at `3` are used. The tree for
the special exponent at least `9` is split into chunks (`cut`), each checked from its own state.

The theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81, 2012) covers the indices divisible
by `3` or by `5`; whether the present result is new has not been verified against the
literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace MixedIndexThree

/-- Running an accepted tree from a valid state. -/
theorem run3 {N : ℕ} (h : OddPerfect N) (h5o : Odd (N.factorization 5))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 →
      3 ∣ N.factorization p + 1 ∨ 5 ∣ N.factorization p + 1 ∨ 7 ∣ N.factorization p + 1)
    {B : List (ℕ × ℕ)} (hB : ∀ x ∈ B, (x.1 = 3 ∨ x.1 = 5) ∧ x.1 ^ x.2 ∣ N) {c3 : ℕ} {c5 : Bool}
    (hc3 : c3 ≠ 0 → N.factorization 3 = c3) (hc5 : c5 = true → N.factorization 5 = 1)
    {Acc : List St} (hAcc : ∀ s ∈ Acc, Inv N s → False) {t : Tr} (ht : isHd t = false)
    (s : St) (hinv : Inv N s)
    (hok : chk3 primes B c3 c5 Acc s.1 s.2.1 s.2.2.1 s.2.2.2 t = true) : False := by
  refine chk3_sound h h5o hexp primes_prime hB hc3 hc5 hAcc t s.1 s.2.1 s.2.2.1 s.2.2.2 hinv
    ?_ hok
  intro p k hk
  rw [isHd_of_isAt hk] at ht
  exact absurd ht (by decide)

/-- No odd perfect number `N` with odd `v_5(N)` has an index `v_p(N) + 1` divisible by `3`, `5`
or `7` at every prime `p ≠ 5` dividing `N`. -/
theorem not_mixed_index_special_five {N : ℕ} (h : OddPerfect N)
    (h5o : Odd (N.factorization 5))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 →
      3 ∣ N.factorization p + 1 ∨ 5 ∣ N.factorization p + 1 ∨ 7 ∣ N.factorization p + 1) :
    False := by
  by_cases h35 : 3 ∣ N.factorization 3 + 1 ∨ 5 ∣ N.factorization 3 + 1
  · exact MixedIndexTwo.not_mixed_index_special_five_of_three h h5o hexp h35
  have h3d : 3 ∣ N := OPNStarter.force_prime h.2 Nat.prime_five rfl Nat.prime_three
    (by norm_num) (MixedIndexTwo.three_dvd_sigma_five h5o)
  have h7 : 7 ∣ N.factorization 3 + 1 := by
    rcases hexp 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3d, h.ne_zero⟩) (by norm_num)
      with h' | h' | h'
    · exact absurd (Or.inl h') h35
    · exact absurd (Or.inr h') h35
    · exact h'
  have h6 : 6 ≤ N.factorization 3 := by
    have := Nat.le_of_dvd (by omega) h7
    omega
  have h1093 : 1093 ∣ N := by
    refine OPNStarter.force_prime h.2 Nat.prime_three rfl (by norm_num) (by norm_num) ?_
    refine Dvd.dvd.trans ?_ (OPNExample.sigma_prime_pow_dvd Nat.prime_three (a := 6) h7)
    rw [sigma_one_apply_prime_pow Nat.prime_three]
    decide
  have hinv := inv_root (N := N) (r := 1093) (by norm_num) h1093 (by norm_num) (by norm_num)
  have hnil : ∀ s ∈ ([] : List St), Inv N s → False := by simp
  have hoff : (0 : ℕ) ≠ 0 → N.factorization 3 = 0 := fun h' => absurd rfl h'
  rcases (MixedIndexTwo.five_exponent h h5o).2 with hk | hk
  · refine run3 h h5o hexp (B := [(3, 6), (5, 1)]) ?_ hoff (c5 := true) (fun _ => hk)
      (Acc := acc_g1) (by simp [acc_g1]) rfl _ hinv ok_g1_top
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨Or.inl rfl, MixedIndex.pow_dvd_of_le h6⟩
    · exact ⟨Or.inr rfl, MixedIndex.pow_dvd_of_le (by simp [hk])⟩
  · have hB : ∀ x ∈ [(3, 6), (5, 9)], (x.1 = 3 ∨ x.1 = 5) ∧ x.1 ^ x.2 ∣ N := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨Or.inl rfl, MixedIndex.pow_dvd_of_le h6⟩
      · exact ⟨Or.inr rfl, MixedIndex.pow_dvd_of_le hk⟩
    have hc5 : false = true → N.factorization 5 = 1 := fun h' => absurd h' Bool.false_ne_true
    have hAcc : ∀ s ∈ acc_g9, Inv N s → False := by
      intro s hs hs'
      simp only [acc_g9, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_0
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_1
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_2
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_3
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_4
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_5
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_6
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_7
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_8
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_9
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_10
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_11
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_12
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_13
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_14
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_15
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_16
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_17
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_18
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_19
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_20
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_21
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_22
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_23
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_24
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_25
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_26
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_27
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_28
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_29
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_30
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_31
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_32
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_33
      · exact run3 h h5o hexp hB hoff hc5 hnil rfl _ hs' ok_g9_34
    exact run3 h h5o hexp hB hoff hc5 hAcc rfl _ hinv ok_g9_top

/-- If `5` is the special prime of an odd perfect number `N`, then some prime `p ≠ 5` dividing
`N` has an index `v_p(N) + 1` prime to `105`. -/
theorem exists_index_coprime_105 {N : ℕ} (h : OddPerfect N)
    (h5o : Odd (N.factorization 5)) :
    ∃ p ∈ N.primeFactors, p ≠ 5 ∧ Nat.Coprime (N.factorization p + 1) 105 := by
  by_contra hne
  push Not at hne
  refine not_mixed_index_special_five h h5o fun p hp hp5 => ?_
  by_contra h'
  push Not at h'
  obtain ⟨h3, h5, h7⟩ := h'
  have c3 : Nat.Coprime (N.factorization p + 1) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  have c5 : Nat.Coprime (N.factorization p + 1) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5).symm
  have c7 : Nat.Coprime (N.factorization p + 1) 7 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7).symm
  exact hne p hp hp5 ((c3.mul_right c5).mul_right c7)

end MixedIndexThree

end OddPerfect

#print axioms OddPerfect.MixedIndexThree.run3
#print axioms OddPerfect.MixedIndexThree.not_mixed_index_special_five
#print axioms OddPerfect.MixedIndexThree.exists_index_coprime_105
