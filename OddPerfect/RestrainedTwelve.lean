import OddPerfect.RestrainedEight

/-!
# Restrained odd perfect numbers: prime factors `t ≡ 2 (mod 3)`

Conditional family results. Setting of `restrained_two_sources`: `N` is an odd perfect number
with special prime `q`, `r ≠ q` is a further prime, and every prime factor other than `q` and
`r` has exponent exactly 2.

* `pow_pred_modEq_one_of_sq_dvd`: if `t` is a prime, `b` is coprime to `t`,
  `t ^ 2 ∣ b ^ n - 1` and `t ∤ n`, then `b ^ (t - 1) ≡ 1 (mod t ^ 2)`. In `ZMod (t ^ 2)` the
  element `y = b ^ (t - 1)` satisfies `y ^ t = 1` (Euler) and `y ^ n = 1`, and `t` and `n` are
  coprime, so the order of `y` is 1.
* `restrained_two_mod_three_cases`: a prime factor `t ≡ 2 (mod 3)` of `N` divides
  `σ(q ^ α)`, or divides `v_3(N) + 1`, or satisfies `3 ^ (t - 1) ≡ 1 (mod t ^ 2)`, that is,
  `t` is a Wieferich prime to the base 3. If `t ∤ σ(q ^ α)`, the two sources lemma gives
  `t ^ 2 ∣ σ(3 ^ E)`, and `2 σ(3 ^ E) = 3 ^ (E + 1) - 1`.
* `restrained_two_mod_three_cases_of_one`: the same when `v_q(N) = 1`, with `t ∣ q + 1` as
  the first alternative.

Conditional family result; whether this is in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- **Lifting to the square.** Let `t` be a prime and `b` coprime to `t`. If
`t ^ 2 ∣ b ^ n - 1` and `t ∤ n`, then `b ^ (t - 1) ≡ 1 (mod t ^ 2)`. -/
theorem pow_pred_modEq_one_of_sq_dvd {b t n : ℕ} (ht : t.Prime) (hbt : b.Coprime t)
    (hdvd : t ^ 2 ∣ b ^ n - 1) (hn : ¬ t ∣ n) : b ^ (t - 1) ≡ 1 [MOD t ^ 2] := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [Nat.coprime_zero_left] at hbt
      exact absurd hbt ht.one_lt.ne'
    · exact hb
  have h1 : b ^ n ≡ 1 [MOD t ^ 2] := ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hb)).mpr hdvd).symm
  have h2 : b ^ Nat.totient (t ^ 2) ≡ 1 [MOD t ^ 2] :=
    Nat.ModEq.pow_totient (Nat.Coprime.pow_right 2 hbt)
  have hphi : Nat.totient (t ^ 2) = t * (t - 1) := by
    rw [Nat.totient_prime_pow ht two_pos]
    simp
  rw [hphi] at h2
  rw [← ZMod.natCast_eq_natCast_iff] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  have hyt : ((b : ZMod (t ^ 2)) ^ (t - 1)) ^ t = 1 := by
    rw [← pow_mul, mul_comm]
    exact h2
  have hyn : ((b : ZMod (t ^ 2)) ^ (t - 1)) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
  have hcop : Nat.Coprime t n := (Nat.Prime.coprime_iff_not_dvd ht).mpr hn
  have ho := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyt) (orderOf_dvd_of_pow_eq_one hyn)
  rw [hcop.gcd_eq_one] at ho
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp ho)

/-- Twice the divisor sum of a power of 3: `2 σ(3 ^ E) + 1 = 3 ^ (E + 1)`. -/
theorem two_mul_sigma_three_pow_add_one (E : ℕ) : 2 * σ 1 (3 ^ E) + 1 = 3 ^ (E + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_three]
  generalize E + 1 = m
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

/-- **Restrained family, prime factors `t ≡ 2 (mod 3)`.** Such a prime factor divides
`σ(q ^ α)` (with `α = v_q(N)`), or divides `v_3(N) + 1`, or satisfies
`3 ^ (t - 1) ≡ 1 (mod t ^ 2)`; the third alternative says that `t` is a Wieferich prime to
the base 3.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_two_mod_three_cases {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t ∈ N.primeFactors) (ht3 : t % 3 = 2) :
    t ∣ σ 1 (q ^ N.factorization q) ∨ t ∣ N.factorization 3 + 1 ∨
      3 ^ (t - 1) ≡ 1 [MOD t ^ 2] := by
  by_cases hA : t ∣ σ 1 (q ^ N.factorization q)
  · exact Or.inl hA
  by_cases hB : t ∣ N.factorization 3 + 1
  · exact Or.inr (Or.inl hB)
  refine Or.inr (Or.inr ?_)
  have htp := Nat.prime_of_mem_primeFactors ht
  have hsrc := restrained_two_sources h hq hodd hr hrq hsq ht ht3
  rw [padicValNat.eq_zero_of_not_dvd hA, add_zero] at hsrc
  have h2 : t ^ 2 ∣ σ 1 (3 ^ N.factorization 3) := by
    rw [← hsrc]
    exact pow_padicValNat_dvd
  have h3 : t ^ 2 ∣ 3 ^ (N.factorization 3 + 1) - 1 := by
    rw [← two_mul_sigma_three_pow_add_one, Nat.add_sub_cancel]
    exact Dvd.dvd.mul_left h2 2
  have hcop : Nat.Coprime 3 t :=
    (Nat.coprime_primes Nat.prime_three htp).mpr (by rintro rfl; norm_num at ht3)
  exact pow_pred_modEq_one_of_sq_dvd htp hcop h3 hB

/-- **Restrained family with special exponent 1.** When `v_q(N) = 1`, a prime factor
`t ≡ 2 (mod 3)` of `N` divides `q + 1`, or divides `v_3(N) + 1`, or is a Wieferich prime to
the base 3.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_two_mod_three_cases_of_one {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hq1 : N.factorization q = 1) (ht : t ∈ N.primeFactors) (ht3 : t % 3 = 2) :
    t ∣ q + 1 ∨ t ∣ N.factorization 3 + 1 ∨ 3 ^ (t - 1) ≡ 1 [MOD t ^ 2] := by
  have hc := restrained_two_mod_three_cases h hq (by rw [hq1]; exact odd_one) hr hrq hsq ht ht3
  have hs : σ 1 (q ^ N.factorization q) = q + 1 := by
    rw [hq1, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ, add_comm]
  rwa [hs] at hc

end OddPerfect

#print axioms OddPerfect.pow_pred_modEq_one_of_sq_dvd
#print axioms OddPerfect.two_mul_sigma_three_pow_add_one
#print axioms OddPerfect.restrained_two_mod_three_cases
#print axioms OddPerfect.restrained_two_mod_three_cases_of_one
