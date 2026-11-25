import OddPerfect.PrimeCapMore
import OddPerfect.PrimeCapFamily

/-!
# The exponent of the largest prime factor, prime senders with indices up to 23

Restricted family results; no novelty is claimed, and whether they are in the literature was
not verified.

The ledger `factorization_le_sum_of_cap` of `OddPerfect.PrimeCapFamily` with the capacity
`primeSenderCapMore` of `OddPerfect.PrimeCapMore`:

* `factorization_largest_le_sum_primeSenderCapMore`: special exponent `1`, largest prime
  factor `P ≠ q`, and every other exponent `e` in a finite set `E` with `3 ≤ e + 1 ≤ 23`.
* `factorization_largest_le_seventyeight`: exponents in `{2, 4, 6, 8, 10, 12}` give
  `e_P ≤ 78` (`2 + 6 + 11 + 15 + 19 + 25`).
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem sigmaWeight_special_eq_zero' {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
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

/-- Family bound for prime senders, indices up to 23. Let `N` be an odd perfect number with
special prime `q`, `e_q = 1`, and largest prime factor `P ≠ q`. Let `E` be a finite set of
exponents `e` with `3 ≤ e + 1 ≤ 23` and `P ∤ e + 1`. If every prime factor other than `q` and
`P` has its exponent in `E`, then `e_P ≤ ∑ e ∈ E, primeSenderCapMore (e + 1)`. Restricted
family result. -/
theorem factorization_largest_le_sum_primeSenderCapMore {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P) (E : Finset ℕ)
    (hE : ∀ e ∈ E, 3 ≤ e + 1 ∧ e + 1 ≤ 23 ∧ ¬ P ∣ e + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P → N.factorization p ∈ E) :
    N.factorization P ≤ ∑ e ∈ E, primeSenderCapMore (e + 1) := by
  have hqm : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by rw [hq1]; norm_num)
  refine factorization_le_sum_of_cap h hP hmax E (fun e => primeSenderCapMore (e + 1))
    (fun e he U hU => ?_) (fun p hp hpP => ?_)
  · obtain ⟨h3, h23, hPe⟩ := hE e he
    exact sum_factorization_geom_sum_le_primeSenderCapMore (Nat.prime_of_mem_primeFactors hP)
      hPe h3 h23 U hU
  · by_cases hpq : p = q
    · subst hpq
      exact Or.inl (sigmaWeight_special_eq_zero' h hq hq1 hP hqm hPq hmax)
    · exact Or.inr (hexp p hp hpq hpP)

/-- Exponents `2, 4, 6, 8, 10, 12`, prime senders. Let `N` be an odd perfect number with
special prime `q`, `e_q = 1`, and largest prime factor `P ≠ q`. If every prime factor other
than `q` and `P` has exponent `2`, `4`, `6`, `8`, `10` or `12`, then `e_P ≤ 78`. Restricted
family result. -/
theorem factorization_largest_le_seventyeight {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p ∈ ({2, 4, 6, 8, 10, 12} : Finset ℕ)) :
    N.factorization P ≤ 78 := by
  obtain ⟨p, hp, hlt⟩ := exists_primeFactor_gt_200000 h
  have hbig : 200000 < P := lt_of_lt_of_le hlt (hmax p hp)
  have hb := factorization_largest_le_sum_primeSenderCapMore h hq hq1 hP hPq hmax
    {2, 4, 6, 8, 10, 12}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      refine ⟨by omega, by omega, fun hd => ?_⟩
      have := Nat.le_of_dvd (by omega) hd
      omega)
    hexp
  have hc : ∑ e ∈ ({2, 4, 6, 8, 10, 12} : Finset ℕ), primeSenderCapMore (e + 1) = 78 := by
    decide
  omega

end OddPerfect

#print axioms OddPerfect.factorization_largest_le_sum_primeSenderCapMore
#print axioms OddPerfect.factorization_largest_le_seventyeight
