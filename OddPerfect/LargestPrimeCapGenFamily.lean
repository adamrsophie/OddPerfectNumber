import OddPerfect.LargestPrimeCapGen
import OddPerfect.Network
import OddPerfect.SpecialPrime
import OddPerfect.LargestPrimeFactorThreeFinal

/-!
# The exponent of the largest prime factor when every index is an odd prime

Restricted family result; no novelty is claimed, and whether it is in the literature was not
verified.

Let `N` be an odd perfect number with special prime `q`, special exponent `e_q = 1`, and
largest prime factor `P ≠ q`. Let `E` be a finite set of exponents `e` such that `e + 1` is an
odd prime different from `P`, and assume every prime factor `p ∉ {q, P}` has `e_p ∈ E`. Then
`e_P ≤ ∑ e ∈ E, primeIndexCap (e + 1)` (`factorization_largest_le_sum_primeIndexCap`).

The proof reads the ledger `e_P = Σ_p v_P(σ(p ^ e_p))`: the special row `q + 1` is not
divisible by `P`, and the rows of exponent `e` add up to at most `primeIndexCap (e + 1)` by
`sum_factorization_geom_sum_le_primeIndexCap`. Both restrictions are essential to the
argument: the special exponent must be `1`, and every index `e + 1` must be prime (composite
indices need another argument).

Instances: exponents in `{2, 4, 6}` give `e_P ≤ 22`; exponents in `{2, 6}` give `e_P ≤ 14`
(the bound `15`, rounded down as `e_P` is even); exponents in `{2, 4}` give `e_P ≤ 8`, the
bound of `factorization_largest_le_eight`, derived again from the general theorem.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- General family bound. Let `N` be an odd perfect number with special prime `q`, `e_q = 1`,
and largest prime factor `P ≠ q`. Let `E` be a finite set of exponents `e` such that `e + 1` is
a prime different from `2` and from `P`. If every prime factor other than `q` and `P` has its
exponent in `E`, then `e_P ≤ ∑ e ∈ E, primeIndexCap (e + 1)`. The special exponent `1` and the
primality of the indices `e + 1` are essential to the argument. -/
theorem factorization_largest_le_sum_primeIndexCap {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P) (E : Finset ℕ)
    (hE : ∀ e ∈ E, (e + 1).Prime ∧ e + 1 ≠ 2 ∧ e + 1 ≠ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P → N.factorization p ∈ E) :
    N.factorization P ≤ ∑ e ∈ E, primeIndexCap (e + 1) := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hodd : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hP2 : P ≠ 2 := fun h2 => by have := hodd P hP; omega
  have hsum := sigmaWeight_sum_eq h.2 hPp hP2
  rw [← Finset.sum_erase N.primeFactors (f := fun p => sigmaWeight N p P)
    (sigmaWeight_self hPp)] at hsum
  set g : ℕ → ℕ → ℕ := fun p e =>
    if N.factorization p = e then (∑ i ∈ Finset.range (e + 1), p ^ i).factorization P else 0
    with hgdef
  have hpt : ∀ p ∈ N.primeFactors.erase P, sigmaWeight N p P ≤ ∑ e ∈ E, g p e := by
    intro p hp
    obtain ⟨hpP, hp'⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hp'
    by_cases hpq : p = q
    · subst hpq
      have hs : σ 1 (p ^ N.factorization p) = p + 1 := by
        rw [hq1, sigma_one_apply_prime_pow hpp]
        simp [Finset.sum_range_succ, add_comm]
      have hlt : p < P := lt_of_le_of_ne (hmax p hp') hpP
      have := hodd p hp'
      have := hodd P hP
      have hnd : ¬ P ∣ p + 1 := fun hd => by
        have := Nat.le_of_dvd (by omega) hd
        omega
      unfold sigmaWeight
      rw [hs, Nat.factorization_eq_zero_of_not_dvd hnd]
      exact Nat.zero_le _
    · simp only [hgdef]
      rw [Finset.sum_ite_eq, if_pos (hexp p hp' hpq hpP)]
      unfold sigmaWeight
      rw [sigma_one_apply_prime_pow hpp]
  have hle := Finset.sum_le_sum hpt
  rw [hsum, Finset.sum_comm] at hle
  refine hle.trans (Finset.sum_le_sum fun e he => ?_)
  obtain ⟨hl, hl2, hlP⟩ := hE e he
  simp only [hgdef]
  rw [← Finset.sum_filter]
  refine sum_factorization_geom_sum_le_primeIndexCap hPp hl hl2 hlP _ fun u hu => ?_
  obtain ⟨huP, hu'⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hu).1
  exact ⟨(Nat.prime_of_mem_primeFactors hu').one_lt, lt_of_le_of_ne (hmax u hu') huP⟩

private theorem largest_gt_200000 {N P : ℕ} (h : OddPerfect N)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P) : 200000 < P := by
  obtain ⟨p, hp, hlt⟩ := exists_primeFactor_gt_200000 h
  exact lt_of_lt_of_le hlt (hmax p hp)

/-- Exponents `2`, `4`, `6`. Let `N` be an odd perfect number with special prime `q`, `e_q = 1`,
and largest prime factor `P ≠ q`. If every prime factor other than `q` and `P` has exponent
`2`, `4` or `6`, then `e_P ≤ 22`. Restricted family result. -/
theorem factorization_largest_le_twentytwo {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 4 ∨ N.factorization p = 6) :
    N.factorization P ≤ 22 := by
  have hbig := largest_gt_200000 h hmax
  have hb := factorization_largest_le_sum_primeIndexCap h hq hq1 hP hPq hmax {2, 4, 6}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> refine ⟨by norm_num, by norm_num, by omega⟩)
    (fun p hp hpq hpP => by simpa using hexp p hp hpq hpP)
  have hc : ∑ e ∈ ({2, 4, 6} : Finset ℕ), primeIndexCap (e + 1) = 22 := by decide
  omega

/-- Exponents `2`, `6`. Let `N` be an odd perfect number with special prime `q`, `e_q = 1`,
and largest prime factor `P ≠ q`. If every prime factor other than `q` and `P` has exponent
`2` or `6`, then `e_P ≤ 14` (the general bound is `15`, and `e_P` is even). Restricted family
result. -/
theorem factorization_largest_le_fourteen {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 6) :
    N.factorization P ≤ 14 := by
  have hbig := largest_gt_200000 h hmax
  have hb := factorization_largest_le_sum_primeIndexCap h hq hq1 hP hPq hmax {2, 6}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> refine ⟨by norm_num, by norm_num, by omega⟩)
    (fun p hp hpq hpP => by simpa using hexp p hp hpq hpP)
  have hc : ∑ e ∈ ({2, 6} : Finset ℕ), primeIndexCap (e + 1) = 15 := by decide
  obtain ⟨k, hk⟩ := even_factorization_of_ne h hq (by rw [hq1]; exact odd_one)
    (Nat.prime_of_mem_primeFactors hP) hPq
  omega

/-- Exponents `2`, `4`, derived from the general theorem: the hypotheses and the conclusion of
`factorization_largest_le_eight`. Restricted family result. -/
theorem factorization_largest_le_eight_of_primeIndexCap {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization P ≤ 8 := by
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by rw [hq1]; norm_num)
  have h4 := (special_mod_four h hq (by rw [hq1]; exact odd_one)).1
  have := hq.two_le
  have hqP := lt_of_le_of_ne (hmax q hqmem) hPq.symm
  have hb := factorization_largest_le_sum_primeIndexCap h hq hq1 hP hPq hmax {2, 4}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> refine ⟨by norm_num, by norm_num, by omega⟩)
    (fun p hp hpq hpP => by simpa using hexp p hp hpq hpP)
  have hc : ∑ e ∈ ({2, 4} : Finset ℕ), primeIndexCap (e + 1) = 9 := by decide
  obtain ⟨k, hk⟩ := even_factorization_of_ne h hq (by rw [hq1]; exact odd_one)
    (Nat.prime_of_mem_primeFactors hP) hPq
  omega

end OddPerfect

#print axioms OddPerfect.factorization_largest_le_sum_primeIndexCap
#print axioms OddPerfect.factorization_largest_le_twentytwo
#print axioms OddPerfect.factorization_largest_le_fourteen
#print axioms OddPerfect.factorization_largest_le_eight_of_primeIndexCap
