import OddPerfect.Seed.Starter
import Mathlib.NumberTheory.FactorisationProperties

/-!
# An exponent-pattern exclusion for perfect numbers

The arguments cover all positive exponents congruent to two modulo three.
No bound on the number or size of the other prime divisors is required.
-/

namespace OPNExample

open ArithmeticFunction OPNStarter
open scoped ArithmeticFunction.sigma

/-- A geometric sum of length `d` divides every sum whose length is a multiple of `d`. -/
theorem geom_sum_dvd_geom_sum {d m : ℕ} (p : ℕ) (hd : d ∣ m) :
    (∑ i ∈ Finset.range d, p ^ i) ∣ ∑ i ∈ Finset.range m, p ^ i := by
  obtain ⟨k, rfl⟩ := hd
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add]
    apply dvd_add ih
    simp only [pow_add, ← Finset.mul_sum]
    exact dvd_mul_left _ _

/-- If `a+1` divides the true component length `e+1`, the divisor sum
of `p^a` divides that of `p^e`. -/
theorem sigma_prime_pow_dvd {p a e : ℕ} (hp : p.Prime) (h : a + 1 ∣ e + 1) :
    σ 1 (p ^ a) ∣ σ 1 (p ^ e) := by
  simp only [sigma_one_apply_prime_pow hp]
  exact geom_sum_dvd_geom_sum p h

private theorem abundant_divisor_excludes {d n : ℕ} (hn : n.Perfect) (hd : d ∣ n)
    (h : 2 * d < σ 1 d) : False := by
  rw [sigma_one_apply] at h
  have hab := (Nat.abundant_iff_sum_divisors.mpr h).of_dvd hd hn.2.ne'
  exact ((Nat.perfect_iff_not_abundant_and_not_deficient hn.2.ne).mp hn).1 hab

/-- No perfect number has the exponents of both 3 and 5 congruent to 2 modulo 3. -/
theorem exclude_three_and_five_exponents {n : ℕ} (hn : n.Perfect)
    (h3 : n.factorization 3 % 3 = 2) (h5 : n.factorization 5 % 3 = 2) : False := by
  have p3 : Nat.Prime 3 := by decide
  have p5 : Nat.Prime 5 := by decide
  have p13 : Nat.Prime 13 := by decide
  have d9 : 3 ^ 2 ∣ n := (p3.pow_dvd_iff_le_factorization hn.2.ne').mpr (by omega)
  have d25 : 5 ^ 2 ∣ n := (p5.pow_dvd_iff_le_factorization hn.2.ne').mpr (by omega)
  have d13 : 13 ∣ n := by
    apply force_prime hn p3 rfl p13 (by decide)
    refine Dvd.dvd.trans ?_ (sigma_prime_pow_dvd (a := 2) p3 (by omega))
    rw [sigma_one_apply_prime_pow p3]
    decide
  have d31 : 31 ∣ n := by
    apply force_prime hn p5 rfl (by decide) (by decide)
    refine Dvd.dvd.trans ?_ (sigma_prime_pow_dvd (a := 2) p5 (by omega))
    rw [sigma_one_apply_prime_pow p5]
    decide
  have d225 := (show Nat.Coprime (3 ^ 2) (5 ^ 2) by decide).mul_dvd_of_dvd_of_dvd d9 d25
  by_cases e13 : n.factorization 13 = 1
  · have d7 : 7 ∣ n := by
      apply force_prime hn p13 e13 (by decide) (by decide)
      rw [sigma_one_apply_prime_pow p13]
      decide
    have d2925 := (show Nat.Coprime 225 13 by decide).mul_dvd_of_dvd_of_dvd d225 d13
    have d20475 := (show Nat.Coprime 2925 7 by decide).mul_dvd_of_dvd_of_dvd d2925 d7
    have hvalue : 2925 * 7 = 3 ^ 2 * 5 ^ 2 * 13 ^ 1 * 7 ^ 1 := by decide
    rw [hvalue] at d20475
    apply abundant_divisor_excludes hn d20475
    repeat' rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
    rw [sigma_one_apply_prime_pow p3, sigma_one_apply_prime_pow p5,
      sigma_one_apply_prime_pow p13, sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]
    decide
  · have one_le := (p13.dvd_iff_one_le_factorization hn.2.ne').mp d13
    have d169 : 13 ^ 2 ∣ n := (p13.pow_dvd_iff_le_factorization hn.2.ne').mpr (by omega)
    have d38025 := (show Nat.Coprime 225 169 by decide).mul_dvd_of_dvd_of_dvd d225 d169
    have d1178775 := (show Nat.Coprime 38025 31 by decide).mul_dvd_of_dvd_of_dvd d38025 d31
    have hvalue : 38025 * 31 = 3 ^ 2 * 5 ^ 2 * 13 ^ 2 * 31 ^ 1 := by decide
    rw [hvalue] at d1178775
    apply abundant_divisor_excludes hn d1178775
    repeat' rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
    rw [sigma_one_apply_prime_pow p3, sigma_one_apply_prime_pow p5,
      sigma_one_apply_prime_pow p13, sigma_one_apply_prime_pow (by decide : Nat.Prime 31)]
    decide

end OPNExample

#print axioms OPNExample.geom_sum_dvd_geom_sum
#print axioms OPNExample.sigma_prime_pow_dvd
#print axioms OPNExample.exclude_three_and_five_exponents
