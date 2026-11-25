import OddPerfect.RestrainedFifteen
import OddPerfect.RestrainedFive
import OddPerfect.ClassicalSmall

/-!
# Restrained odd perfect numbers: the primes that are 5 modulo 12

Setting of `restrained_prod_sq_dvd`: `N` is an odd perfect number with special prime `q` and
exponent `a = v_q(N)`, `r ≠ q` is a further prime, and every prime factor other than `q` and `r`
has exponent exactly 2 (the restrained family). The landed results give `r = 3`, `E = v_3(N)`
even and `q ≡ 1 (mod 12)`.

* `RestrainedFiveModTwelve.not_dvd_three_pow_sub_one`: a prime `p ≡ 5 (mod 12)` does not divide
  `3 ^ n - 1` for odd `n`. As `3 ^ n - 1 = 2 σ(3 ^ (n - 1))`, this is a short corollary of the
  landed `mod_three_eq_one_of_dvd_geom_sum_three` (3 is a square modulo `p`, so by reciprocity
  `p` is a square modulo 3).
* `restrained_five_mod_twelve_sq_dvd`: a prime factor `p ≡ 5 (mod 12)` of `N` has
  `p ^ 2 ∣ σ(q ^ a) / 2`. It receives its exponent 2 only from the components of 3 and `q`
  (`restrained_two_sources`), and it does not divide `σ(3 ^ E)` as `E` is even.
* `restrained_five_mod_twelve_prod_sq_dvd`: the product of the squares of these primes divides
  `σ(q ^ a) / 2`.
* `restrained_five_mod_twelve_prod_sq_dvd_succ` and `restrained_five_mod_twelve_le_succ`: at
  `a = 1`, twice that product divides `q + 1`, and `2 p ^ 2 ≤ q + 1` for each such `p`.

The restrained family is not excluded by these results. They are conditional family results
checked by the kernel; their novelty was not verified. The odd perfect number conjecture is open
and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open RestrainedSeven RestrainedFifteen

namespace RestrainedFiveModTwelve

/-- A prime `p ≡ 5 (mod 12)` does not divide `3 ^ n - 1` for odd `n`: otherwise it divides
`σ(3 ^ (n - 1))` with `n - 1` even, and `mod_three_eq_one_of_dvd_geom_sum_three` gives
`p ≡ 1 (mod 3)`. No odd perfect number is involved. -/
theorem not_dvd_three_pow_sub_one {p n : ℕ} (hp : p.Prime) (h12 : p % 12 = 5) (hn : Odd n) :
    ¬ p ∣ 3 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  intro hd
  have hg := geom_sum_mul_add (2 : ℕ) (2 * k + 1)
  norm_num only at hg
  have he : 3 ^ (2 * k + 1) - 1 = 2 * ∑ i ∈ Finset.range (2 * k + 1), 3 ^ i := by omega
  rw [he] at hd
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have h3 := mod_three_eq_one_of_dvd_geom_sum_three hp (by omega) ⟨k, (two_mul k)⟩
    (hcop.dvd_of_dvd_mul_left hd)
  omega

end RestrainedFiveModTwelve

/-- **Restrained family: a prime 5 modulo 12.** A prime factor `p ≡ 5 (mod 12)` of `N` has
`p ^ 2 ∣ σ(q ^ a) / 2` with `a = v_q(N)`: by `restrained_two_sources`
`v_p(σ(3 ^ E)) + v_p(σ(q ^ a)) = 2`, and `p ∤ σ(3 ^ E)` because `E` is even and 3 is not a
square modulo `p`. The family is not excluded; novelty not verified. -/
theorem restrained_five_mod_twelve_sq_dvd {N q r p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hp : p ∈ N.primeFactors) (h12 : p % 12 = 5) :
    p ^ 2 ∣ σ 1 (q ^ N.factorization q) / 2 := by
  obtain ⟨-, -, hE, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hpp := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpp⟩
  have hs := restrained_two_sources h hq hodd hr hrq hsq hp (by omega)
  have hnd : ¬ p ∣ σ 1 (3 ^ N.factorization 3) := fun hd => by
    rw [sigma_one_apply_prime_pow Nat.prime_three] at hd
    have := mod_three_eq_one_of_dvd_geom_sum_three hpp (by omega) hE hd
    omega
  rw [padicValNat.eq_zero_of_not_dvd hnd, zero_add] at hs
  have hdvd : p ^ 2 ∣ σ 1 (q ^ N.factorization q) := by
    have := pow_padicValNat_dvd (p := p) (n := σ 1 (q ^ N.factorization q))
    rwa [hs] at this
  have h2q : 2 ∣ σ 1 (q ^ N.factorization q) :=
    two_dvd_sigma_odd hq (by have := F.mod12; omega) hodd
  have hcop : Nat.Coprime (p ^ 2) 2 :=
    Nat.Coprime.pow_left 2 ((Nat.coprime_primes hpp Nat.prime_two).mpr (by omega))
  rw [← Nat.mul_div_cancel' h2q] at hdvd
  exact hcop.dvd_of_dvd_mul_left hdvd

/-- **Restrained family: the primes 5 modulo 12, product form.** The product of `p ^ 2` over
the prime factors `p ≠ 3, q` of `N` with `p ≡ 5 (mod 12)` divides `σ(q ^ a) / 2`, from
`restrained_five_mod_twelve_sq_dvd`. The family is not excluded; novelty not verified. -/
theorem restrained_five_mod_twelve_prod_sq_dvd {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (∏ p ∈ {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 12 = 5}, p ^ 2) ∣
      σ 1 (q ^ N.factorization q) / 2 :=
  prod_sq_dvd (fun _ ht => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp ht).1)
    fun _ ht => restrained_five_mod_twelve_sq_dvd h hq hodd hr hrq hsq
      (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2.2.2

/-- **Restrained family at `a = 1`.** If `v_q(N) = 1`, twice the product of `p ^ 2` over the
prime factors `p ≠ 3, q` of `N` with `p ≡ 5 (mod 12)` divides `q + 1`, as `σ(q) = q + 1`.
The family is not excluded; novelty not verified. -/
theorem restrained_five_mod_twelve_prod_sq_dvd_succ {N q r : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ha : N.factorization q = 1) :
    2 * ∏ p ∈ {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 12 = 5}, p ^ 2 ∣ q + 1 := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hP := restrained_five_mod_twelve_prod_sq_dvd h hq hodd hr hrq hsq
  have hs : σ 1 (q ^ N.factorization q) = q + 1 := by
    rw [ha, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ, add_comm]
  rw [hs] at hP
  have h2 : 2 ∣ q + 1 := by
    have := F.mod12
    omega
  have := Nat.mul_dvd_mul_left 2 hP
  rwa [Nat.mul_div_cancel' h2] at this

/-- **Restrained family at `a = 1`, size.** If `v_q(N) = 1`, every prime factor `p ≠ 3, q`
of `N` with `p ≡ 5 (mod 12)` satisfies `2 p ^ 2 ≤ q + 1`.
The family is not excluded; novelty not verified. -/
theorem restrained_five_mod_twelve_le_succ {N q r p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ha : N.factorization q = 1) (hp : p ∈ N.primeFactors) (hp3 : p ≠ 3) (hpq : p ≠ q)
    (h12 : p % 12 = 5) :
    2 * p ^ 2 ≤ q + 1 := by
  have hmem : p ∈ {p ∈ N.primeFactors | p ≠ 3 ∧ p ≠ q ∧ p % 12 = 5} :=
    Finset.mem_filter.mpr ⟨hp, hp3, hpq, h12⟩
  have hd := (Nat.mul_dvd_mul_left 2 (Finset.dvd_prod_of_mem (fun t => t ^ 2) hmem)).trans
    (restrained_five_mod_twelve_prod_sq_dvd_succ h hq hodd hr hrq hsq ha)
  exact Nat.le_of_dvd (by omega) hd

end OddPerfect

#print axioms OddPerfect.RestrainedFiveModTwelve.not_dvd_three_pow_sub_one
#print axioms OddPerfect.restrained_five_mod_twelve_sq_dvd
#print axioms OddPerfect.restrained_five_mod_twelve_prod_sq_dvd
#print axioms OddPerfect.restrained_five_mod_twelve_prod_sq_dvd_succ
#print axioms OddPerfect.restrained_five_mod_twelve_le_succ
