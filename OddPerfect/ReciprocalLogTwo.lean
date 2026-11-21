import OddPerfect.ReciprocalSum
import OddPerfect.SpecialPrime
import OddPerfect.SupportBridges
import Mathlib

/-!
# The sum of the reciprocals of the prime factors of an odd perfect number is below `log 2`

With `q` the special prime of an odd perfect number `N` and `S` its set of prime factors,
`log 2 ≥ ∑_{p ∈ S, p ≠ q} log(1 + 1/p + 1/p²) + log(1 + 1/q)`. The elementary bounds
`x + x²/4 ≤ log(1 + x + x²)` for `0 ≤ x ≤ 1/3` and `x - log(1 + x) ≤ x²/2` for `x ≥ 0`
give, for every `U ⊆ S.erase q`,
`∑_{p ∈ S} 1/p ≤ log 2 + 1/(2q²) - (1/4) ∑_{p ∈ U} 1/p²`.
A prime `r ≠ q` of `N` divides `(q + 1)/2`, so `1/(4r²) ≥ 1/(q + 1)²`, and since
`(q + 1)² < 2q²` the right side is below `log 2`. This is a classical result.
-/

open Finset

namespace OddPerfect

/-- For real `y ≥ 0`, `2y/(2 + y) ≤ log(1 + y)`. -/
theorem two_mul_div_two_add_le_log {y : ℝ} (hy : 0 ≤ y) :
    2 * y / (2 + y) ≤ Real.log (1 + y) := by
  set z := y / (2 + y) with hzdef
  have h2y : 0 < 2 + y := by linarith
  have hz0 : 0 ≤ z := div_nonneg hy h2y.le
  have hz1 : z < 1 := by rw [div_lt_one h2y]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (show |z| < 1 by rwa [abs_of_nonneg hz0])
  have hle := le_hasSum hs 0 (fun k _ => by positivity)
  have h1z : 0 < 1 - z := by linarith
  have hprod : 1 + z = (1 + y) * (1 - z) := by
    rw [hzdef]
    field_simp
    ring
  rw [hprod, Real.log_mul (by linarith) h1z.ne'] at hle
  have e : 2 * y / (2 + y) = 2 * z := by rw [hzdef]; ring
  norm_num at hle
  linarith

/-- For `0 ≤ x ≤ 1/3`, `x + x²/4 ≤ log(1 + x + x²)`. -/
theorem add_sq_div_four_le_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 3) :
    x + x ^ 2 / 4 ≤ Real.log (1 + x + x ^ 2) := by
  have h := two_mul_div_two_add_le_log (y := x + x ^ 2) (by positivity)
  rw [show (1 : ℝ) + (x + x ^ 2) = 1 + x + x ^ 2 by ring] at h
  refine le_trans ?_ h
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

/-- For `x ≥ 0`, `x - log(1 + x) ≤ x²/2`. -/
theorem sub_log_one_add_le_sq {x : ℝ} (h0 : 0 ≤ x) :
    x - Real.log (1 + x) ≤ x ^ 2 / 2 := by
  have h := two_mul_div_two_add_le_log h0
  have : x - x ^ 2 / 2 ≤ 2 * x / (2 + x) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [pow_nonneg h0 3]
  linarith

variable {N : ℕ}

private theorem mem_of_odd' (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : q ∈ N.primeFactors := by
  rw [Nat.mem_primeFactors]
  refine ⟨hq, Nat.dvd_of_factorization_pos ?_, h.ne_zero⟩
  obtain ⟨k, hk⟩ := hodd
  omega

private theorem three_le_of_mem' (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    (3 : ℝ) ≤ p := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hodd : Odd p := h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have := hp'.two_le
  obtain ⟨k, rfl⟩ := hodd
  exact_mod_cast (by omega : 3 ≤ 2 * k + 1)

/-- Main lemma: for an odd perfect number with special prime `q` and any set `U` of prime
factors of `N` other than `q`,
`∑_{p ∣ N} 1/p ≤ log 2 + 1/(2q²) - (1/4) ∑_{p ∈ U} 1/p²`. -/
theorem sum_inv_le_log_two_add_sub (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {U : Finset ℕ} (hU : U ⊆ N.primeFactors.erase q) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ≤
      Real.log 2 + 1 / (2 * (q : ℝ) ^ 2) - (1 / 4) * ∑ p ∈ U, 1 / (p : ℝ) ^ 2 := by
  set E := N.primeFactors.erase q
  have hqmem := mem_of_odd' h hq hodd
  have hbase := sum_log_erase_add_log_le h hq hodd
  have hE : ∑ p ∈ E, (1 / (p : ℝ) + (1 / 4) * (1 / (p : ℝ) ^ 2)) ≤
      ∑ p ∈ E, Real.log (1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have h3 := three_le_of_mem' h (Finset.mem_of_mem_erase hp)
    have := add_sq_div_four_le_log (x := 1 / (p : ℝ)) (by positivity)
      (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
    rw [div_pow, one_pow] at this ⊢
    linarith
  have hq3 := three_le_of_mem' h hqmem
  have hql := sub_log_one_add_le_sq (x := 1 / (q : ℝ)) (by positivity)
  have hU' : ∑ p ∈ U, 1 / (p : ℝ) ^ 2 ≤ ∑ p ∈ E, 1 / (p : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hU (fun _ _ _ => by positivity)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hE
  have htot : ∑ p ∈ N.primeFactors, 1 / (p : ℝ) = 1 / q + ∑ p ∈ E, 1 / (p : ℝ) :=
    (Finset.add_sum_erase _ _ hqmem).symm
  have e : (1 / (q : ℝ)) ^ 2 / 2 = 1 / (2 * (q : ℝ) ^ 2) := by field_simp
  rw [e] at hql
  linarith

/-- Gap form: for an odd perfect number with special prime `q`,
`∑_{p ∣ N} 1/p ≤ log 2 + 1/(2q²) - 1/(q + 1)²`. -/
theorem sum_inv_le_log_two_add_gap (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ≤
      Real.log 2 + 1 / (2 * (q : ℝ) ^ 2) - 1 / ((q : ℝ) + 1) ^ 2 := by
  obtain ⟨r, hrN, hrq, hrdvd, -⟩ := exists_orderOf_eq_two_special h hq hodd
  have hmain := sum_inv_le_log_two_add_sub h hq hodd
    (U := {r}) (Finset.singleton_subset_iff.mpr (Finset.mem_erase.mpr ⟨hrq, hrN⟩))
  rw [Finset.sum_singleton] at hmain
  have hq3 := three_le_of_mem' h (mem_of_odd' h hq hodd)
  have hr3 := three_le_of_mem' h hrN
  have hrle : 2 * r ≤ q + 1 := by
    have hpos : 0 < (q + 1) / 2 := by
      have := hq.two_le
      omega
    have := Nat.le_of_dvd hpos hrdvd
    omega
  have hrle' : 2 * (r : ℝ) ≤ q + 1 := by exact_mod_cast hrle
  have key : 1 / ((q : ℝ) + 1) ^ 2 ≤ (1 / 4) * (1 / (r : ℝ) ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / 4 * (1 / (r : ℝ) ^ 2) * ((q : ℝ) + 1) ^ 2 = ((q + 1) / (2 * r)) ^ 2 := by
      field_simp
      ring
    rw [this]
    have h1 : (1 : ℝ) ≤ (q + 1) / (2 * r) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    nlinarith
  linarith

/-- For an odd perfect number `N`, `∑_{p ∣ N} 1/p < log 2`. -/
theorem sum_inv_lt_log_two (h : OddPerfect N) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < Real.log 2 := by
  obtain ⟨q, hq, -, -, he, -⟩ := exists_special_prime h
  have hodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have hgap := sum_inv_le_log_two_add_gap h hq hodd
  have hq3 := three_le_of_mem' h (mem_of_odd' h hq hodd)
  have : 1 / ((q : ℝ) + 1) ^ 2 > 1 / (2 * (q : ℝ) ^ 2) := by
    rw [gt_iff_lt, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end OddPerfect

#print axioms OddPerfect.two_mul_div_two_add_le_log
#print axioms OddPerfect.add_sq_div_four_le_log
#print axioms OddPerfect.sub_log_one_add_le_sq
#print axioms OddPerfect.sum_inv_le_log_two_add_sub
#print axioms OddPerfect.sum_inv_le_log_two_add_gap
#print axioms OddPerfect.sum_inv_lt_log_two
