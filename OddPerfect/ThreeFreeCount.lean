import OddPerfect.ThreeFreeThree
import OddPerfect.Counting
import OddPerfect.SpecialPrime

/-!
# Counting corollaries of the modular three exception theorem

Consequences of `four_le_card_mod_exceptions`: an odd perfect number `N` with special prime `q`
and `3 ∤ N` has at least four prime factors `p ≠ q` whose exponent `e` has `3 ∤ e + 1`.

* Such an exponent is even and positive and is not 2, so it is at least 4.
* Hence at least four prime factors other than `q` have exponent different from 2.
* Counting: `2 ω(N) + 7 ≤ Ω(N)` when `3 ∤ N`.

These are formal consequences inside this library. The literature has much stronger results
when `3 ∤ N` (for example Nielsen's bound of at least twelve distinct prime factors), which are
not proved here.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

/-- A prime factor `p ≠ q` of an odd perfect number with special prime `q` whose exponent `e`
has `3 ∤ e + 1` has `4 ≤ e`: the exponent is even and positive, and `e = 2` gives `3 ∣ e + 1`. -/
theorem four_le_factorization_of_mem_mod_exceptions {N q p : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hp : p ∈ (N.primeFactors.erase q).filter fun p => ¬ 3 ∣ N.factorization p + 1) :
    4 ≤ N.factorization p := by
  obtain ⟨hpe, h3⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hpe
  obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hpN
  obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hpp hpq
  have h1 := hpp.factorization_pos_of_dvd h.ne_zero hpd
  by_contra hlt
  have h2 : N.factorization p = 2 := by omega
  rw [h2] at h3
  exact h3 (by norm_num)

/-- If `3 ∤ N`, at least four prime factors other than the special prime `q` have exponent
different from 2. A superset of the set in `four_le_card_mod_exceptions`. -/
theorem four_le_card_ne_two {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N) :
    4 ≤ ((N.primeFactors.erase q).filter fun p => N.factorization p ≠ 2).card := by
  refine (four_le_card_mod_exceptions h hq hodd h3).trans (Finset.card_le_card ?_)
  intro p hp
  obtain ⟨hpe, hp3⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨hpe, fun h2 => hp3 ?_⟩
  rw [h2]

/-- If `3 ∤ N`, then `2 ω(N) + 7 ≤ Ω(N)`: the special prime has exponent at least 1, four
further prime factors have exponent at least 4 by `four_le_card_mod_exceptions`, and the rest
have exponent at least 2. A formal consequence inside this library; the literature has much
stronger results when `3 ∤ N` (at least twelve distinct prime factors, Nielsen), which are not
proved here. -/
theorem two_mul_omega_add_seven_le {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    2 * ω N + 7 ≤ Ω N := by
  obtain ⟨q, hq, hqN, -, hk4, -⟩ := exists_special_prime h
  have hodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have hqm : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩
  set B := (N.primeFactors.erase q).filter fun p => ¬ 3 ∣ N.factorization p + 1 with hB
  have hcard : 4 ≤ B.card := four_le_card_mod_exceptions h hq hodd h3
  have hBsub : B ⊆ N.primeFactors := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have key : ∀ p ∈ N.primeFactors,
      2 + (if p ∈ B then 2 else 0) ≤ N.factorization p + (if p = q then 1 else 0) := by
    intro p hp
    have h1 := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd h.ne_zero
      (Nat.dvd_of_mem_primeFactors hp)
    by_cases hpq : p = q
    · have hpB : p ∉ B := by
        rw [hB, Finset.mem_filter, Finset.mem_erase]
        tauto
      subst hpq
      rw [if_neg hpB, if_pos rfl]
      omega
    · obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors hp) hpq
      by_cases hpB : p ∈ B
      · have := four_le_factorization_of_mem_mod_exceptions h hq hodd hpB
        simp only [hpB, hpq, if_true, if_false]
        omega
      · simp only [hpB, hpq, if_false]
        omega
  have hs := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' N.primeFactors q
    (fun _ => 1), Finset.sum_ite_mem, Finset.inter_eq_right.mpr hBsub] at hs
  simp only [Finset.sum_const, smul_eq_mul, if_pos hqm] at hs
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  omega

end OddPerfect

#print axioms OddPerfect.four_le_factorization_of_mem_mod_exceptions
#print axioms OddPerfect.four_le_card_ne_two
#print axioms OddPerfect.two_mul_omega_add_seven_le
