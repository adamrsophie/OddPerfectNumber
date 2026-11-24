import OddPerfect.DefectTreeCheck
import OddPerfect.ExcessFiveData3
import OddPerfect.ExcessFiveData5
import OddPerfect.ExcessFiveData7
import OddPerfect.ExcessFiveData11
import OddPerfect.ExcessFiveData13
import OddPerfect.SmallestPrime
import OddPerfect.Counting

/-!
# Total excess at least 5

Let `N` be an odd perfect number with special prime `q`. Every other prime factor `p` has an
even exponent `e_p ≥ 2`; call `e_p / 2 - 1` its excess and `T` the total excess. This module
proves `T ≥ 5` (`five_le_excess`), equivalently `ω(m) + 5 ≤ Ω(m)` in Euler's form
`N = q ^ a * m ^ 2` with `q ∤ m` (`five_le_cardFactors_sub`), and in the variables of `N`,
`Ω(N) ≥ 2 * ω(N) + a + 8` (`two_mul_omega_add_special_add_eight_le_Omega`).

Relation to published results. Since `Ω(N) - 2 * ω(N) = a - 2 + 2 * (Ω(m) - ω(m))`, the
published inequality `Ω(N) ≥ 2 * ω(N) + 51` of Ochem and Rao (Math. Comp. 83, 2014) gives
`2 * T ≥ 53 - a`, hence `T ≥ 5` for every special exponent `a ≤ 41`. The statements here do not
depend on `a`. Whether the case `a ≥ 45` is new has not been verified against the literature.
P. Ochem reported on the Mersenne Forum in July 2026 that a run for `Ω(N) ≥ 2 * ω(N) + 55`
had finished (not published, not checked here); with that constant the case `a = 45` would
follow as well.

## The proof

Suppose `T ≤ 4`. With `s = v_3(σ(q ^ a))` and `D = supportDefect N q`, the defect identity
`ω(N) + 2 * s + D = 5 * T + 5 + #escapeRows` and `#escapeRows ≤ 1` give `ω(N) + D ≤ 26`. If
`3 ∣ N`, the certificate with root 3 and lower bound 3 applies. If `3 ∤ N`, the smallest prime
factor `p` is at least 5, `ω(N) ≤ 5 * T + 2 ≤ 22` and Grün's bound `3 * p < 2 * ω(N) + 6` give
`p ≤ 16`, so `p` is 5, 7, 11 or 13, and the certificate with root `p` and lower bound `p`
applies. The five certificates (parameters `K = 26`, `w = 1`, cap 4 for `T`) come from an exact
search and are checked in the kernel by the checker `DefectTree.check` of
`OddPerfect.DefectTreeCode`; its soundness theorem `DefectTree.check_sound` turns each into a
contradiction. The search trees have 1782, 290, 159, 19 and 52 nodes for the roots 3, 5, 7, 11
and 13. A control search without the ledger rule of the checker also closes for all five
roots (1867, 350, 168, 24 and 56 nodes), so for this bound the ledger only shortens the trees.

The total excess is not bounded by this method; the odd perfect number conjecture is open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace OddPerfect

/-- An accepted defect tree certificate with weight 1, cap `k` for the total excess and bound
`5 * k + 6` refutes `T ≤ k` for an odd perfect number whose prime factors are at least the lower
bound of the certificate and which is divided by its root. -/
theorem false_of_check_excess_cap {k : ℕ} {P : DefectTree.Params} {pc : DefectTree.PCert}
    {tab : DefectTree.Tab} {c : DefectTree.Cert} (hc : DefectTree.check P pc tab c = true)
    (hP : P.cap = some k ∧ P.w = 1 ∧ P.K = 5 * k + 6) {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hT : ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) ≤ k)
    (hu : ∀ p ∈ N.primeFactors, P.u ≤ p) (hroot : P.root ∣ N) : False := by
  obtain ⟨hcap, hw, hK⟩ := hP
  refine DefectTree.check_sound hc h hq hodd (fun c' hc' => ?_) ?_ hu hroot
  · rw [hcap, Option.some.injEq] at hc'
    exact hc' ▸ hT
  · rw [hw, hK]
    have e := card_primeFactors_add_two_mul_add_defect_eq h hq hodd
    have hE := card_escapeRows_le_one_all h hq hodd
    omega

/-- If `3 ∤ N` and `T ≤ k`, the smallest prime factor `p` of the odd perfect number `N` satisfies
`5 ≤ p` and `3 * p < 10 * k + 10`, divides `N` and is at most every prime factor. -/
theorem minFac_facts_of_not_three_dvd {N q k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N)
    (hT : ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) ≤ k) :
    N.minFac.Prime ∧ 5 ≤ N.minFac ∧ 3 * N.minFac < 10 * k + 10 ∧ N.minFac ∣ N ∧
      ∀ p ∈ N.primeFactors, N.minFac ≤ p := by
  have hm := three_le_minFac h
  have hN1 : N ≠ 1 := fun h1 => by rw [h1] at hm; simp at hm
  have hp := Nat.minFac_prime hN1
  have hd := Nat.minFac_dvd N
  have h3m : N.minFac ≠ 3 := fun e => h3 (e ▸ hd)
  have h4m : N.minFac ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
  have hw := card_primeFactors_le_five_excess_add_two_of_not_three_dvd h hq hodd h3
  have hg := three_mul_minFac_lt h
  refine ⟨hp, by omega, by omega, hd, fun p hp' => ?_⟩
  exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp').two_le
    (Nat.dvd_of_mem_primeFactors hp')

/-- If the total excess of `N` is at least `k` whenever the exponent of `q` is odd, then in
Euler's form `N = q ^ a * m ^ 2` with `q ∤ m` of an odd perfect number, `ω(m) + k ≤ Ω(m)`. -/
theorem cardFactors_sub_of_le_excess {N q a m k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hqm : ¬ q ∣ m) (hN : N = q ^ a * m ^ 2)
    (hT : Odd (N.factorization q) →
      k ≤ ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) :
    ArithmeticFunction.cardDistinctFactors m + k ≤ ArithmeticFunction.cardFactors m := by
  have hN0 := h.ne_zero
  have hm0 : m ≠ 0 := by rintro rfl; simp [hN] at hN0
  have hq0 : q ^ a ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hfac : ∀ p, N.factorization p = a * q.factorization p + 2 * m.factorization p := by
    intro p
    rw [hN, Nat.factorization_mul hq0 (pow_ne_zero _ hm0), Finsupp.add_apply,
      Nat.factorization_pow, Nat.factorization_pow]
    rfl
  have hmq : m.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqm
  have hkq : N.factorization q = a := by
    rw [hfac, hq.factorization_self, hmq]
    ring
  have hk : Odd a := by
    by_contra hk
    obtain ⟨j, rfl⟩ := Nat.not_odd_iff_even.mp hk
    exact not_isSquare h ⟨q ^ j * m, by rw [hN]; ring⟩
  have hne : ∀ p, p ≠ q → N.factorization p = 2 * m.factorization p := by
    intro p hpq
    rw [hfac, hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq)]
    ring
  have hset : N.primeFactors.erase q = m.primeFactors := by
    ext p
    rw [Finset.mem_erase, ← Nat.support_factorization, ← Nat.support_factorization,
      Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨hpq, hp⟩
      rw [hne p hpq] at hp
      omega
    · intro hp
      have hpq : p ≠ q := by rintro rfl; exact hp hmq
      exact ⟨hpq, by rw [hne p hpq]; omega⟩
  have key := hT (hkq ▸ hk)
  rw [hset] at key
  have hsum : ∑ p ∈ m.primeFactors, (N.factorization p / 2 - 1)
      = ∑ p ∈ m.primeFactors, (m.factorization p - 1) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpq : p ≠ q := by rintro rfl; exact (Nat.dvd_of_mem_primeFactors hp |> hqm)
    rw [hne p hpq]
    omega
  have hOm : Ω m = ∑ p ∈ m.primeFactors, (m.factorization p - 1) + m.primeFactors.card := by
    rw [cardFactors_eq_sum_primeFactors, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hm0
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  rw [cardDistinctFactors_eq_card_primeFactors, hOm]
  omega

/-- If the total excess of an odd perfect number `N` with special prime `q` is at least `k`,
then `2 * ω(N) + a + 2 * k ≤ Ω(N) + 2`, where `a` is the exponent of `q`. -/
theorem two_mul_omega_add_special_le_Omega_of_le_excess {N q k : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hT : k ≤ ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) :
    2 * ArithmeticFunction.cardDistinctFactors N + N.factorization q + 2 * k ≤
      ArithmeticFunction.cardFactors N + 2 := by
  have hN0 := h.ne_zero
  have hqN : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    obtain ⟨j, hj⟩ := hodd
    omega
  have hsum : ∑ p ∈ N.primeFactors.erase q, N.factorization p
      = ∑ p ∈ N.primeFactors.erase q, (2 * (N.factorization p / 2 - 1) + 2) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hpos := hpp.factorization_pos_of_dvd hN0 (Nat.dvd_of_mem_primeFactors hpN)
    obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hpp hpq
    omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem hqN] at hsum
  have hcard := Finset.card_pos.mpr ⟨q, hqN⟩
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors,
    ← Finset.add_sum_erase _ _ hqN, hsum]
  omega

/-- For an odd perfect number `N` with special prime `q`, the total excess
`∑ (v_p(N) / 2 - 1)` over the prime factors `p ≠ q` is at least 5. For a special exponent at
most 41 this follows from a published inequality of Ochem and Rao (see the module docstring);
whether the remaining case is new has not been verified against the literature. -/
theorem five_le_excess {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    5 ≤ ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) := by
  by_contra hlt
  have hT : ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) ≤ 4 := by omega
  by_cases h3 : 3 ∣ N
  · refine false_of_check_excess_cap DefectTree.check_Excess5R3 ⟨rfl, rfl, rfl⟩ h hq hodd hT
      (fun p hp => ?_) h3
    show 3 ≤ p
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hd := Nat.dvd_of_mem_primeFactors hp
    have ho := Nat.odd_iff.mp h.1
    by_contra hp3
    have : p = 2 := by omega
    subst this
    omega
  · obtain ⟨hp, h5, hlt3, hd, hle⟩ := minFac_facts_of_not_three_dvd h hq hodd h3 hT
    generalize N.minFac = p at hp h5 hlt3 hd hle
    have hp16 : p ≤ 16 := by omega
    interval_cases p
    all_goals try (norm_num at hp; done)
    · exact false_of_check_excess_cap DefectTree.check_Excess5R5 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd
    · exact false_of_check_excess_cap DefectTree.check_Excess5R7 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd
    · exact false_of_check_excess_cap DefectTree.check_Excess5R11 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd
    · exact false_of_check_excess_cap DefectTree.check_Excess5R13 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd

/-- In Euler's form `N = q ^ a * m ^ 2` with `q ∤ m` of an odd perfect number,
`ω(m) + 5 ≤ Ω(m)`. For `a ≤ 41` this follows from a published inequality of Ochem and Rao (see
the module docstring); whether the case `a ≥ 45` is new has not been verified against the
literature. -/
theorem five_le_cardFactors_sub {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hN : N = q ^ a * m ^ 2) :
    ArithmeticFunction.cardDistinctFactors m + 5 ≤ ArithmeticFunction.cardFactors m :=
  cardFactors_sub_of_le_excess h hq hqm hN (five_le_excess h hq)

/-- For an odd perfect number `N` with special prime `q` of exponent `a`,
`2 * ω(N) + a + 8 ≤ Ω(N)`. The published inequality `Ω(N) ≥ 2 * ω(N) + 51` of Ochem and Rao
(Math. Comp. 83, 2014) is stronger for `a ≤ 41` and weaker for `a ≥ 45` (the special exponent
is 1 modulo 4). This is the bound `five_le_excess` in other variables, not a second
obstruction. -/
theorem two_mul_omega_add_special_add_eight_le_Omega {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    2 * ArithmeticFunction.cardDistinctFactors N + N.factorization q + 8 ≤
      ArithmeticFunction.cardFactors N := by
  have := two_mul_omega_add_special_le_Omega_of_le_excess h hq hodd
    (five_le_excess h hq hodd)
  omega

end OddPerfect

#print axioms OddPerfect.false_of_check_excess_cap
#print axioms OddPerfect.minFac_facts_of_not_three_dvd
#print axioms OddPerfect.cardFactors_sub_of_le_excess
#print axioms OddPerfect.two_mul_omega_add_special_le_Omega_of_le_excess
#print axioms OddPerfect.five_le_excess
#print axioms OddPerfect.five_le_cardFactors_sub
#print axioms OddPerfect.two_mul_omega_add_special_add_eight_le_Omega
