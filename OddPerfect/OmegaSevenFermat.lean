import OddPerfect.OmegaSeven

/-!
# Six prime factors with `3, 5, 17` the three smallest

The prefix `3, 5, 17` is the one that the search of `OddPerfect/OmegaSix.lean` cannot close:
with `257` and `65537` next, the abundancy bounds of the Fermat primes stay below `2` for every
exponent. This file closes the part of that case in which the fourth smallest prime factor is
at least `601`, so it proves: if `3, 5, 17` are the three smallest prime factors of an odd perfect
number with exactly six prime factors, then the fourth smallest is below `601`.

The case `17 ∣ N` in full is not proved. Measured with an exact mirror of the search, the
fourth primes `19` to `593` need over one million nodes even with exponent caps for the Fermat
type primes (`factorization_le_of_fermat`) and the rule that at least two prime factors are not
of Fermat type (`two_le_card_not_fermatType`); several fourth primes (`137`, `257`, `263`,
`269`, `271`) exceed `10 ^ 5` nodes each. The caps do not reduce the cost of the part closed
here, so they are not used.
-/

namespace OddPerfect.OmegaSevenSearch

open OmegaSixSearch

variable {N : ℕ}

/-- A root state: `3`, `5`, `17` are prime factors, with exponents at least two, one, one, and
every other prime factor exceeds `m`. -/
private theorem holds_root_3_5_17 (h : OddPerfect N) (h3 : 3 ∈ N.primeFactors)
    (h5 : 5 ∈ N.primeFactors) (h17 : 17 ∈ N.primeFactors) {m : ℕ}
    (hm : ∀ q ∈ N.primeFactors, q ≠ 3 → q ≠ 5 → q ≠ 17 → m < q) :
    Holds N [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨17, 1, false⟩] (N.primeFactors.card - 3) m := by
  have h2 : 3 ≤ N.primeFactors.card := by
    have : ({3, 5, 17} : Finset ℕ) ⊆ N.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    simpa using Finset.card_le_card this
  refine ⟨h, by simp, ?_, by simp; omega, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨h3, kmin_le h h3, fun h => by simp at h⟩
    · exact ⟨h5, kmin_le h h5, fun h => by simp at h⟩
    · exact ⟨h17, kmin_le h h17, fun h => by simp at h⟩
  · intro q hq hn
    simp only [List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hn
    exact hm q hq hn.1 hn.2.1 hn.2.2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Six prime factors with `3, 5, 17` the three smallest and all others above `600` is
impossible. -/
theorem closed_3_5_17_big : Closed [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨17, 1, false⟩] 3 600 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨17, 1, false⟩] 3 600 =
      [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709,
        719, 727, 733, 739, 743, 751, 757, 761] by
    decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact closed_of_solve 30 (by decide +kernel)

/-- The core of `exists_prime_dvd_of_card_eq_six_of_seventeen`, with the hypotheses `3 ∣ N`
and `5 ∣ N` stated explicitly. -/
theorem exists_prime_dvd_of_three_five_seventeen_aux (h : OddPerfect N)
    (h6 : N.primeFactors.card = 6) (h3 : 3 ∣ N) (h5 : 5 ∣ N) (h17 : 17 ∣ N)
    (h11 : ¬ 11 ∣ N) (h13 : ¬ 13 ∣ N) :
    ∃ p, p.Prime ∧ 17 < p ∧ p < 601 ∧ p ∣ N := by
  have m3 : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have m5 : 5 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h5, h.ne_zero⟩
  have m17 : 17 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h17, h.ne_zero⟩
  have h7 : ¬ 7 ∣ N := fun h7 => not_105_dvd h (Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (by norm_num) (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5 : 15 ∣ N) h7)
  by_contra hno
  push Not at hno
  have H := holds_root_3_5_17 h m3 m5 m17 (m := 600) (by
    intro q hq hq3 hq5 hq17
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqN := Nat.dvd_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := fun e => h.not_two_dvd (e ▸ hqN)
    have := hqp.two_le
    by_contra hle
    rcases Nat.lt_or_ge q 17 with hlt | hge
    · interval_cases q <;> simp_all <;> norm_num at hqp
    · exact hno q hqp (by omega) (by omega) hqN)
  rw [h6] at H
  exact closed_3_5_17_big N H

end OddPerfect.OmegaSevenSearch

namespace OddPerfect

/-- If `3, 5, 17` are the three smallest prime factors of an odd perfect number `N` with exactly
six distinct prime factors (that is, `17 ∣ N`, `11 ∤ N` and `13 ∤ N`; then `3, 5 ∣ N` by
`fifteen_dvd_of_card_eq_six` and `7 ∤ N` since `105 ∤ N`), then some prime `p` with
`17 < p < 601` divides `N`. -/
theorem exists_prime_dvd_of_card_eq_six_of_seventeen {N : ℕ} (h : OddPerfect N)
    (h6 : N.primeFactors.card = 6) (h17 : 17 ∣ N) (h11 : ¬ 11 ∣ N) (h13 : ¬ 13 ∣ N) :
    ∃ p, p.Prime ∧ 17 < p ∧ p < 601 ∧ p ∣ N := by
  have h15 := fifteen_dvd_of_card_eq_six h h6
  exact OmegaSevenSearch.exists_prime_dvd_of_three_five_seventeen_aux h h6
    ((Nat.dvd_mul_right 3 5).trans h15) ((Nat.dvd_mul_left 5 3).trans h15) h17 h11 h13

end OddPerfect

#print axioms OddPerfect.OmegaSevenSearch.closed_3_5_17_big
#print axioms OddPerfect.OmegaSevenSearch.exists_prime_dvd_of_three_five_seventeen_aux
#print axioms OddPerfect.exists_prime_dvd_of_card_eq_six_of_seventeen
