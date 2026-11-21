import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.Ring

/-!
# A prime must cross a coprime factorization of a perfect number

An elementary cut consequence of multiplicativity and perfectness.
The factors may have arbitrarily many prime divisors.
-/

namespace OPNCut

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem lt_sigma_one {n : ℕ} (h : 1 < n) : n < σ 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have hmem := Nat.one_mem_properDivisors_iff_one_lt.mpr h
  have hle : 1 ≤ ∑ i ∈ n.properDivisors, i :=
    Finset.single_le_sum (fun (i : ℕ) (_ : i ∈ n.properDivisors) => Nat.zero_le i) hmem
  omega

/-- One prime dividing the first factor also divides the divisor sum of the second.
Swapping the factors gives the other direction of the cut. -/
theorem exists_crossing_prime {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hc : a.Coprime b) (hperf : (a * b).Perfect) :
    ∃ r : ℕ, r.Prime ∧ r ∣ a ∧ r ∣ σ 1 b := by
  have hmul : σ 1 a * σ 1 b = 2 * (a * b) := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime hc, sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf
  apply Nat.Prime.not_coprime_iff_dvd.mp
  intro hcop
  have hdiv : a ∣ σ 1 a * σ 1 b := by
    rw [hmul]
    exact dvd_mul_of_dvd_right (dvd_mul_right a b) 2
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_right hdiv
  have hkbig : 2 ≤ k := by
    by_contra! h
    have hsmall := Nat.mul_le_mul_left a (show k ≤ 1 by omega)
    exact (lt_sigma_one ha).not_ge (by simpa [hk] using hsmall)
  have hcontra : 2 * (a * b) < σ 1 a * σ 1 b := calc
    2 * (a * b) < 2 * (a * σ 1 b) :=
      Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left (lt_sigma_one hb) (by omega)) (by decide)
    _ ≤ σ 1 a * σ 1 b := by
      rw [hk]
      calc
        2 * (a * σ 1 b) = (a * 2) * σ 1 b := by ring
        _ ≤ (a * k) * σ 1 b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left a hkbig)
  omega

/-- A particular prime-power component on the second side supplies a crossing edge.
Here the source exponent is its full exponent in the second factor. -/
theorem exists_crossing_component {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hc : a.Coprime b) (hperf : (a * b).Perfect) :
    ∃ r ∈ a.primeFactors, ∃ p ∈ b.primeFactors,
      r ∣ σ 1 (p ^ b.factorization p) := by
  obtain ⟨r, hr, hra, hsig⟩ := exists_crossing_prime ha hb hc hperf
  refine ⟨r, Nat.mem_primeFactors.mpr ⟨hr, hra, by omega⟩, ?_⟩
  rw [isMultiplicative_sigma.multiplicative_factorization _ (by omega : b ≠ 0),
    Nat.prod_factorization_eq_prod_primeFactors] at hsig
  exact (hr.prime.dvd_finsetProd_iff _).mp hsig

end OPNCut

#print axioms OPNCut.exists_crossing_prime

#print axioms OPNCut.exists_crossing_component
