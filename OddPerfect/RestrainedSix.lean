import OddPerfect.RestrainedFive
import OddPerfect.ForcingClosed

/-!
# Restrained odd perfect numbers: divisors of the exponent index of 3

Setting of `restrained_exception_eq_three`: `N` is an odd perfect number with special prime
`q`, `r ≠ q` is a further prime, and every prime factor other than `q` and `r` has exponent
exactly 2. The theorem `restrained_exception_eq_three` gives `r = 3`, `7 ∤ N`, and that
the exponent `e = v_3(N)` is even and at least 4.

This file shows `3 ∤ e + 1`, `5 ∤ e + 1`, `11 ∤ e + 1`, `17 ∤ e + 1`, and hence `6 ≤ e`.

* `3 ∤ e + 1`: by `exists_exponent_not_three_dvd_succ` some even exponent `f` has `3 ∤ f + 1`;
  every prime other than `q` and `3` has `f = 2`, and `q` has an odd exponent, so the prime is 3.
* `d ∣ e + 1` with `d ∈ {5, 11, 17}`: then `σ(3^(d-1)) ∣ σ(3^e) ∣ 2N`. A prime `p ≡ 3 (mod 4)`
  dividing `σ(3^(d-1))` divides `N` and is neither `q` (which is `1 (mod 4)`) nor 3, so its
  exponent is 2, and `7 ∣ σ(p^2) ∣ 2N` contradicts `7 ∤ N`. The witnesses are
  `σ(3^4) = 11^2` with `σ(11^2) = 7 · 19`, `σ(3^10) = 23 · 3851` with `σ(23^2) = 7 · 79`, and
  `σ(3^16) = 1871 · 34511` with `σ(1871^2) = 7 · 500359`.

These exclude infinite arithmetic classes of the exponent but leave infinitely many exponents.
Ochem and Zelinsky (arXiv 2607.19746, 2026) prove the far stronger bound that the exponent of 3
is at least 23,000,000,000; that bound is not proved here.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace RestrainedSix

/-- The family facts after substituting `r = 3`. -/
private theorem setup {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → N.factorization p = 2) ∧
      4 ≤ N.factorization 3 ∧ Even (N.factorization 3) ∧ ¬ 7 ∣ N := by
  obtain ⟨rfl, h4, hev, -, -, h7⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  exact ⟨hsq, h4, hev, h7⟩

/-- The generic step: a divisor `d` of `e + 1` and a prime `p ≡ 3 (mod 4)`, `p ≠ 3`, dividing
`σ(3^(d-1))` with `7 ∣ σ(p^2)` contradict the family. -/
private theorem key {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → N.factorization p = 2) (h7 : ¬ 7 ∣ N)
    {d p : ℕ} (hd1 : 1 ≤ d) (hd : d ∣ N.factorization 3 + 1) (hp : p.Prime) (hp4 : p % 4 = 3)
    (hp3 : p ≠ 3) (hpd : p ∣ σ 1 (3 ^ (d - 1))) (h7p : 7 ∣ σ 1 (p ^ 2)) : False := by
  have hdiv : σ 1 (3 ^ (d - 1)) ∣ σ 1 (3 ^ N.factorization 3) :=
    ForcingClosed.sigma_prime_pow_dvd_of_dvd Nat.prime_three (by rwa [Nat.sub_add_cancel hd1])
  have h2N := hpd.trans (hdiv.trans (OPNStarter.component_sigma_dvd h.perfect Nat.prime_three rfl))
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have hpN : p ∣ N := hcop.dvd_of_dvd_mul_left h2N
  have hq4 := (special_mod_four h hq hodd).1
  have hpq : p ≠ q := by rintro rfl; omega
  have he := hsq p (Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩) hpq hp3
  have h7N := h7p.trans (OPNStarter.component_sigma_dvd h.perfect hp he)
  exact h7 ((by norm_num : Nat.Coprime 7 2).dvd_of_dvd_mul_left h7N)

private theorem sigma_eq {p k : ℕ} (hp : p.Prime) : σ 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i :=
  sigma_one_apply_prime_pow hp

private theorem s5 : σ 1 (3 ^ 4) = 121 := by
  rw [sigma_eq Nat.prime_three]; simp [Finset.sum_range_succ]

private theorem s11 : σ 1 (3 ^ 10) = 88573 := by
  rw [sigma_eq Nat.prime_three]; simp [Finset.sum_range_succ]

private theorem s17 : σ 1 (3 ^ 16) = 64570081 := by
  rw [sigma_eq Nat.prime_three]; simp [Finset.sum_range_succ]

private theorem p1871 : Nat.Prime 1871 := by norm_num

private theorem t11 : σ 1 (11 ^ 2) = 133 := by
  rw [sigma_eq (by norm_num)]; simp [Finset.sum_range_succ]

private theorem t23 : σ 1 (23 ^ 2) = 553 := by
  rw [sigma_eq (by norm_num)]; simp [Finset.sum_range_succ]

private theorem t1871 : σ 1 (1871 ^ 2) = 3502513 := by
  rw [sigma_eq p1871]; simp [Finset.sum_range_succ]

end RestrainedSix

open RestrainedSix

/-- In the restrained family (hypotheses of `restrained_exception_eq_three`), the exponent
`e = v_3(N)` satisfies `3 ∤ e + 1`. The exceptional prime is 3 by
`restrained_exception_eq_three`, and `exists_exponent_not_three_dvd_succ` supplies an even
exponent `f` with `3 ∤ f + 1`. -/
theorem restrained_three_not_dvd_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ¬ 3 ∣ N.factorization 3 + 1 := by
  obtain ⟨hsq3, -, -, -⟩ := setup h hq hodd hr hrq hsq
  obtain ⟨p, hp, hpe, hp3⟩ := exists_exponent_not_three_dvd_succ h
  have hpq : p ≠ q := by
    rintro rfl
    have := Nat.odd_iff.mp hodd
    omega
  by_cases h3 : p = 3
  · exact h3 ▸ hp3
  · exact absurd (hp3 (by rw [hsq3 p hp hpq h3])) id

/-- In the restrained family, `5 ∤ v_3(N) + 1`. Here `r = 3` and `7 ∤ N` come from
`restrained_exception_eq_three`; the witness is `σ(3^4) = 11^2` and `7 ∣ σ(11^2) = 133`. -/
theorem restrained_five_not_dvd_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ¬ 5 ∣ N.factorization 3 + 1 := by
  obtain ⟨hsq3, -, -, h7⟩ := setup h hq hodd hr hrq hsq
  intro hd
  exact key h hq hodd hsq3 h7 (d := 5) (p := 11) (by norm_num) hd (by norm_num) (by norm_num)
    (by norm_num) (by rw [show 5 - 1 = 4 from rfl, s5]; norm_num) (by rw [t11]; norm_num)

/-- In the restrained family, `11 ∤ v_3(N) + 1`. Here `r = 3` and `7 ∤ N` come from
`restrained_exception_eq_three`; the witness is `23 ∣ σ(3^10) = 88573` and
`7 ∣ σ(23^2) = 553`. -/
theorem restrained_eleven_not_dvd_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ¬ 11 ∣ N.factorization 3 + 1 := by
  obtain ⟨hsq3, -, -, h7⟩ := setup h hq hodd hr hrq hsq
  intro hd
  exact key h hq hodd hsq3 h7 (d := 11) (p := 23) (by norm_num) hd (by norm_num) (by norm_num)
    (by norm_num) (by rw [show 11 - 1 = 10 from rfl, s11]; norm_num) (by rw [t23]; norm_num)

/-- In the restrained family, `17 ∤ v_3(N) + 1`. Here `r = 3` and `7 ∤ N` come from
`restrained_exception_eq_three`; the witness is `1871 ∣ σ(3^16) = 64570081` and
`7 ∣ σ(1871^2) = 3502513`. -/
theorem restrained_seventeen_not_dvd_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ¬ 17 ∣ N.factorization 3 + 1 := by
  obtain ⟨hsq3, -, -, h7⟩ := setup h hq hodd hr hrq hsq
  intro hd
  exact key h hq hodd hsq3 h7 (d := 17) (p := 1871) (by norm_num) hd p1871 (by norm_num)
    (by norm_num) (by rw [show 17 - 1 = 16 from rfl, s17]; norm_num) (by rw [t1871]; norm_num)

/-- In the restrained family, `6 ≤ v_3(N)`: the exponent is even and at least 4 by
`restrained_exception_eq_three`, and `4` is excluded by `restrained_five_not_dvd_succ`. -/
theorem restrained_six_le_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    6 ≤ N.factorization 3 := by
  obtain ⟨-, h4, ⟨k, hk⟩, -⟩ := setup h hq hodd hr hrq hsq
  have h5 := restrained_five_not_dvd_succ h hq hodd hr hrq hsq
  by_contra hlt
  have he : N.factorization 3 = 4 := by omega
  rw [he] at h5
  exact h5 (by norm_num)

end OddPerfect

#print axioms OddPerfect.restrained_three_not_dvd_succ
#print axioms OddPerfect.restrained_five_not_dvd_succ
#print axioms OddPerfect.restrained_eleven_not_dvd_succ
#print axioms OddPerfect.restrained_seventeen_not_dvd_succ
#print axioms OddPerfect.restrained_six_le_three
