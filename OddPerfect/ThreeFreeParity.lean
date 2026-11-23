import OddPerfect.Euler

/-!
# Prime exponent parity for odd perfect numbers without a factor of three

The divisor sums of the prime-power components constrain their exponents modulo three.
An odd number of components have both prime and exponent congruent to one modulo three.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The divisor sum of an odd perfect number coprime to three is two modulo three. -/
private theorem three_free_sigma_mod_three {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    σ 1 N % 3 = 2 := by
  have hn0 : N % 3 ≠ 0 := fun hz => h3 (Nat.dvd_iff_mod_eq_zero.mpr hz)
  have hn1 : N % 3 = 1 := by
    rcases h.touchard with h12 | h36 <;> omega
  rw [h.sigma_eq, Nat.mul_mod, hn1]

/-- The divisor sum of a nonzero number is the product of its component divisor sums. -/
private theorem three_free_sigma_product {N : ℕ} (hN : N ≠ 0) :
    σ 1 N = ∏ p ∈ N.primeFactors, σ 1 (p ^ N.factorization p) := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hN,
    Nat.prod_factorization_eq_prod_primeFactors]

/-- A component divisor sum of an odd perfect number coprime to three is nonzero modulo three. -/
private theorem three_free_component_mod_three_ne_zero {N p : ℕ} (h : OddPerfect N)
    (h3 : ¬ 3 ∣ N) (hp : p ∈ N.primeFactors) : σ 1 (p ^ N.factorization p) % 3 ≠ 0 := by
  have hd : σ 1 (p ^ N.factorization p) ∣ σ 1 N := by
    rw [three_free_sigma_product h.ne_zero]
    exact Finset.dvd_prod_of_mem (fun q => σ 1 (q ^ N.factorization q)) hp
  intro hz
  have hd3 := (Nat.dvd_iff_mod_eq_zero.mpr hz).trans hd
  rw [Nat.dvd_iff_mod_eq_zero, three_free_sigma_mod_three h h3] at hd3
  omega

/-- Powers of two are one modulo three at even exponents and two at odd exponents. -/
private theorem two_pow_mod_three_by_parity (e : ℕ) :
    (2 : ℕ) ^ e % 3 = if e % 2 = 0 then 1 else 2 := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    by_cases he : e % 2 = 0
    · have hs : (e + 1) % 2 ≠ 0 := by omega
      norm_num [if_pos he, if_neg hs]
    · have hs : (e + 1) % 2 = 0 := by omega
      norm_num [if_neg he, if_pos hs]

/-- For a prime congruent to one modulo three, its power divisor sum reduces to its length. -/
private theorem sigma_prime_pow_mod_three_of_one {p e : ℕ} (hp : p.Prime) (hp1 : p % 3 = 1) :
    σ 1 (p ^ e) % 3 = (e + 1) % 3 := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_nat_mod]
  simp [Nat.pow_mod, hp1]

/-- For a prime congruent to two modulo three, its power divisor sum reduces to one for an
even exponent and zero for an odd exponent. -/
private theorem sigma_prime_pow_mod_three_of_two {p e : ℕ} (hp : p.Prime) (hp2 : p % 3 = 2) :
    σ 1 (p ^ e) % 3 = if e % 2 = 0 then 1 else 0 := by
  rw [sigma_one_apply_prime_pow hp]
  induction e with
  | zero =>
    change (∑ k ∈ Finset.range (0 + 1), p ^ k) % 3 = 1
    rw [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, zero_add]
    rfl
  | succ e ih =>
    rw [Finset.sum_range_succ (fun k => p ^ k) (e + 1), Nat.add_mod, ih]
    have hpow : p ^ (e + 1) % 3 = if (e + 1) % 2 = 0 then 1 else 2 := by
      rw [Nat.pow_mod, hp2, two_pow_mod_three_by_parity]
    rw [hpow]
    by_cases he : e % 2 = 0
    · have hs : (e + 1) % 2 ≠ 0 := by omega
      norm_num [if_pos he, if_neg hs]
    · have hs : (e + 1) % 2 = 0 := by omega
      norm_num [if_neg he, if_pos hs]

/-- In an odd perfect number not divisible by 3, a prime factor that is 1 modulo 3 does not
have an exponent that is 2 modulo 3. -/
theorem factorization_mod_three_ne_two_of_not_three_dvd {N p : ℕ} (h : OddPerfect N)
    (h3 : ¬ 3 ∣ N) (hp : p.Prime) (hpN : p ∣ N) (hp1 : p % 3 = 1) :
    N.factorization p % 3 ≠ 2 := by
  have hm : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have hne := three_free_component_mod_three_ne_zero h h3 hm
  rw [sigma_prime_pow_mod_three_of_one hp hp1] at hne
  omega

/-- In an odd perfect number not divisible by 3, every prime factor that is 2 modulo 3 has an
even exponent. -/
theorem even_factorization_of_mod_three_eq_two_of_not_three_dvd {N p : ℕ} (h : OddPerfect N)
    (h3 : ¬ 3 ∣ N) (hp : p.Prime) (hpN : p ∣ N) (hp2 : p % 3 = 2) :
    Even (N.factorization p) := by
  have hm : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have hne := three_free_component_mod_three_ne_zero h h3 hm
  rw [sigma_prime_pow_mod_three_of_two hp hp2] at hne
  apply Nat.even_iff.mpr
  by_contra he
  exact hne (if_neg he)

/-- In an odd perfect number not divisible by 3, the number of prime factors that are 1 modulo 3
with exponent 1 modulo 3 is odd. -/
theorem odd_card_one_mod_three_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    Odd (N.primeFactors.filter fun p => p % 3 = 1 ∧ N.factorization p % 3 = 1).card := by
  have hres (p : ℕ) (hp : p ∈ N.primeFactors) :
      σ 1 (p ^ N.factorization p) % 3 =
        if p % 3 = 1 ∧ N.factorization p % 3 = 1 then 2 else 1 := by
    have hpP := Nat.prime_of_mem_primeFactors hp
    have hpN := Nat.dvd_of_mem_primeFactors hp
    by_cases hp1 : p % 3 = 1
    · have he := factorization_mod_three_ne_two_of_not_three_dvd h h3 hpP hpN hp1
      rw [sigma_prime_pow_mod_three_of_one hpP hp1]
      by_cases h1 : N.factorization p % 3 = 1
      · rw [if_pos (And.intro hp1 h1)]
        omega
      · have hm : ¬ (p % 3 = 1 ∧ N.factorization p % 3 = 1) := fun hm => h1 hm.2
        rw [if_neg hm]
        omega
    · have hp0 : p % 3 ≠ 0 := fun hz => h3 ((Nat.dvd_iff_mod_eq_zero.mpr hz).trans hpN)
      have hp2 : p % 3 = 2 := by omega
      have he := Nat.even_iff.mp
        (even_factorization_of_mod_three_eq_two_of_not_three_dvd h h3 hpP hpN hp2)
      have hm : ¬ (p % 3 = 1 ∧ N.factorization p % 3 = 1) := fun hm => hp1 hm.1
      rw [sigma_prime_pow_mod_three_of_two hpP hp2, if_pos he, if_neg hm]
  let c := (N.primeFactors.filter fun p => p % 3 = 1 ∧ N.factorization p % 3 = 1).card
  change Odd c
  have hpow : (2 : ℕ) ^ c % 3 = 2 := by
    calc
      _ = (∏ p ∈ N.primeFactors,
          if p % 3 = 1 ∧ N.factorization p % 3 = 1 then (2 : ℕ) else 1) % 3 := by
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      _ = (∏ p ∈ N.primeFactors, σ 1 (p ^ N.factorization p) % 3) % 3 :=
        congrArg (fun x : ℕ => x % 3) (Finset.prod_congr rfl fun p hp => (hres p hp).symm)
      _ = σ 1 N % 3 := by rw [← Finset.prod_nat_mod, ← three_free_sigma_product h.ne_zero]
      _ = 2 := three_free_sigma_mod_three h h3
  rw [two_pow_mod_three_by_parity] at hpow
  by_cases hc : c % 2 = 0
  · rw [if_pos hc] at hpow
    omega
  · exact Nat.odd_iff.mpr (by omega)

end OddPerfect

#print axioms OddPerfect.factorization_mod_three_ne_two_of_not_three_dvd
#print axioms OddPerfect.even_factorization_of_mod_three_eq_two_of_not_three_dvd
#print axioms OddPerfect.odd_card_one_mod_three_of_not_three_dvd
