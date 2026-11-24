import OddPerfect.PrimeCap
import OddPerfect.Network
import OddPerfect.SpecialPrime
import OddPerfect.LargestPrimeFactorThreeFinal

/-!
# The exponent of the largest prime factor, with the capacity for prime senders

Restricted family results; no novelty is claimed, and whether they are in the literature was
not verified.

`factorization_le_sum_of_cap` reads the ledger `e_P = Σ_p v_P(σ(p ^ e_p))` at a prime factor
`P` that is at least every prime factor of `N`. Every row other than `P` either has weight `0`
at `P` or has its exponent in a finite set `E`; the rows of exponent `e` come from distinct
primes below `P`, so a cap `c e` valid for every finite set of primes below `P` bounds them.

With the special exponent `1` and the largest prime factor `P ≠ q`, the special row `q + 1` is
not divisible by `P`, and the capacity `primeSenderCap` of `OddPerfect.PrimeCap` gives:

* exponents in `{2, 4, 6}`: `e_P ≤ 18` (the bound `19`, rounded down as `e_P` is even; the
  bound of `factorization_largest_le_twentytwo` was `22`);
* exponents in `{2, 6}`: `e_P ≤ 12` (the bound `13`, rounded down; it was `14`);
* exponents in `{2, 4}`: `e_P ≤ 8` again.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Ledger with a cap. Let `N` be an odd perfect number and `P` a prime factor at least every
prime factor of `N`. Let `E` be a finite set of exponents and `c` a function such that for
every `e ∈ E` and every finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(∑ i ≤ e, u ^ i) ≤ c e`. If every prime factor `p ≠ P` has
`sigmaWeight N p P = 0` or exponent in `E`, then `e_P ≤ ∑ e ∈ E, c e`. -/
theorem factorization_le_sum_of_cap {N P : ℕ} (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P) (E : Finset ℕ) (c : ℕ → ℕ)
    (hc : ∀ e ∈ E, ∀ U : Finset ℕ, (∀ u ∈ U, u.Prime ∧ u < P) →
      ∑ u ∈ U, (∑ i ∈ Finset.range (e + 1), u ^ i).factorization P ≤ c e)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ P → sigmaWeight N p P = 0 ∨ N.factorization p ∈ E) :
    N.factorization P ≤ ∑ e ∈ E, c e := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hP2 : P ≠ 2 := fun h2 => by
    have := Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hP))
    omega
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
    rcases hexp p hp' hpP with h0 | hE
    · rw [h0]
      exact Nat.zero_le _
    · simp only [hgdef]
      rw [Finset.sum_ite_eq, if_pos hE]
      unfold sigmaWeight
      rw [sigma_one_apply_prime_pow hpp]
  have hle := Finset.sum_le_sum hpt
  rw [hsum, Finset.sum_comm] at hle
  refine hle.trans (Finset.sum_le_sum fun e he => ?_)
  simp only [hgdef]
  rw [← Finset.sum_filter]
  refine hc e he _ fun u hu => ?_
  obtain ⟨huP, hu'⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hu).1
  exact ⟨Nat.prime_of_mem_primeFactors hu', lt_of_le_of_ne (hmax u hu') huP⟩

private theorem sigmaWeight_special_eq_zero {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hqm : q ∈ N.primeFactors)
    (hPq : P ≠ q) (hmax : ∀ p ∈ N.primeFactors, p ≤ P) : sigmaWeight N q P = 0 := by
  have hodd : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hs : σ 1 (q ^ N.factorization q) = q + 1 := by
    rw [hq1, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ, add_comm]
  have hlt : q < P := lt_of_le_of_ne (hmax q hqm) hPq.symm
  have := hodd q hqm
  have := hodd P hP
  have hnd : ¬ P ∣ q + 1 := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  unfold sigmaWeight
  rw [hs, Nat.factorization_eq_zero_of_not_dvd hnd]

/-- Family bound for prime senders. Let `N` be an odd perfect number with special prime `q`,
`e_q = 1`, and largest prime factor `P ≠ q`. Let `E` be a finite set of exponents `e` with
`3 ≤ e + 1 ≤ 11` and `P ∤ e + 1`. If every prime factor other than `q` and `P` has its
exponent in `E`, then `e_P ≤ ∑ e ∈ E, primeSenderCap (e + 1)`. Restricted family result. -/
theorem factorization_largest_le_sum_primeSenderCap {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P) (E : Finset ℕ)
    (hE : ∀ e ∈ E, 3 ≤ e + 1 ∧ e + 1 ≤ 11 ∧ ¬ P ∣ e + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P → N.factorization p ∈ E) :
    N.factorization P ≤ ∑ e ∈ E, primeSenderCap (e + 1) := by
  have hqm : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by rw [hq1]; norm_num)
  refine factorization_le_sum_of_cap h hP hmax E (fun e => primeSenderCap (e + 1))
    (fun e he U hU => ?_) (fun p hp hpP => ?_)
  · obtain ⟨h3, h11, hPe⟩ := hE e he
    exact sum_factorization_geom_sum_le_primeSenderCap (Nat.prime_of_mem_primeFactors hP)
      hPe h3 h11 U hU
  · by_cases hpq : p = q
    · subst hpq
      exact Or.inl (sigmaWeight_special_eq_zero h hq hq1 hP hqm hPq hmax)
    · exact Or.inr (hexp p hp hpq hpP)

private theorem largest_gt_200000 {N P : ℕ} (h : OddPerfect N)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P) : 200000 < P := by
  obtain ⟨p, hp, hlt⟩ := exists_primeFactor_gt_200000 h
  exact lt_of_lt_of_le hlt (hmax p hp)

private theorem not_dvd_small {P n : ℕ} (hP : 200000 < P) (hn : 0 < n) (hn11 : n ≤ 11) :
    ¬ P ∣ n := fun hd => by
  have := Nat.le_of_dvd hn hd
  omega

/-- Exponents `2`, `4`, `6`, prime senders. Let `N` be an odd perfect number with special prime
`q`, `e_q = 1`, and largest prime factor `P ≠ q`. If every prime factor other than `q` and `P`
has exponent `2`, `4` or `6`, then `e_P ≤ 18` (the bound `19`, and `e_P` is even). Restricted
family result. -/
theorem factorization_largest_le_eighteen {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 4 ∨ N.factorization p = 6) :
    N.factorization P ≤ 18 := by
  have hbig := largest_gt_200000 h hmax
  have hb := factorization_largest_le_sum_primeSenderCap h hq hq1 hP hPq hmax {2, 4, 6}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;>
        exact ⟨by norm_num, by norm_num, not_dvd_small hbig (by norm_num) (by norm_num)⟩)
    (fun p hp hpq hpP => by simpa using hexp p hp hpq hpP)
  have hc : ∑ e ∈ ({2, 4, 6} : Finset ℕ), primeSenderCap (e + 1) = 19 := by decide
  obtain ⟨k, hk⟩ := even_factorization_of_ne h hq (by rw [hq1]; exact odd_one)
    (Nat.prime_of_mem_primeFactors hP) hPq
  omega

/-- Exponents `2`, `6`, prime senders. Let `N` be an odd perfect number with special prime `q`,
`e_q = 1`, and largest prime factor `P ≠ q`. If every prime factor other than `q` and `P` has
exponent `2` or `6`, then `e_P ≤ 12` (the bound `13`, and `e_P` is even). Restricted family
result. -/
theorem factorization_largest_le_twelve {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 6) :
    N.factorization P ≤ 12 := by
  have hbig := largest_gt_200000 h hmax
  have hb := factorization_largest_le_sum_primeSenderCap h hq hq1 hP hPq hmax {2, 6}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;>
        exact ⟨by norm_num, by norm_num, not_dvd_small hbig (by norm_num) (by norm_num)⟩)
    (fun p hp hpq hpP => by simpa using hexp p hp hpq hpP)
  have hc : ∑ e ∈ ({2, 6} : Finset ℕ), primeSenderCap (e + 1) = 13 := by decide
  obtain ⟨k, hk⟩ := even_factorization_of_ne h hq (by rw [hq1]; exact odd_one)
    (Nat.prime_of_mem_primeFactors hP) hPq
  omega

/-- Exponents `2`, `4`, prime senders: the hypotheses and the conclusion of
`factorization_largest_le_eight`, derived from `primeSenderCap` (`2 + 6 = 8`). Restricted
family result. -/
theorem factorization_largest_le_eight_of_primeSenderCap {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization P ≤ 8 := by
  have hbig := largest_gt_200000 h hmax
  have hb := factorization_largest_le_sum_primeSenderCap h hq hq1 hP hPq hmax {2, 4}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;>
        exact ⟨by norm_num, by norm_num, not_dvd_small hbig (by norm_num) (by norm_num)⟩)
    (fun p hp hpq hpP => by simpa using hexp p hp hpq hpP)
  have hc : ∑ e ∈ ({2, 4} : Finset ℕ), primeSenderCap (e + 1) = 8 := by decide
  omega

end OddPerfect

#print axioms OddPerfect.factorization_le_sum_of_cap
#print axioms OddPerfect.factorization_largest_le_sum_primeSenderCap
#print axioms OddPerfect.factorization_largest_le_eighteen
#print axioms OddPerfect.factorization_largest_le_twelve
#print axioms OddPerfect.factorization_largest_le_eight_of_primeSenderCap
