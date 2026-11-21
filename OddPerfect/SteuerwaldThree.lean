import OddPerfect.Euler
import Mathlib.Tactic.NormNum.Prime

/-!
# Steuerwald's theorem when `3 ∣ N`

Steuerwald (1937): in an odd perfect number the primes other than the special prime
cannot all have exponent exactly two. This file proves the case `3 ∣ N`. The `3`-adic
valuation of `σ(N) = 2N` is exactly two, while a forcing chain starting at `σ(3^2) = 13`
always produces three distinct non special primes `p ≡ 1 (mod 3)`, each contributing a
factor `3` through `σ(p^2) = 1 + p + p^2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Pairing consecutive terms: if `n ∣ q + 1` and `k` is odd then `n` divides the sum. -/
private lemma dvd_geom_of_odd' {q n k : ℕ} (hn : n ∣ q + 1) (hk : Odd k) :
    n ∣ ∑ i ∈ Finset.range (k + 1), q ^ i := by
  obtain ⟨j, rfl⟩ := hk
  induction j with
  | zero => simpa [Finset.sum_range_succ, add_comm] using hn
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 + 1 = 2 * j + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, add_assoc]
    refine dvd_add ih ?_
    rw [show q ^ (2 * j + 1 + 1) + q ^ (2 * j + 1 + 1 + 1) = q ^ (2 * j + 2) * (q + 1) by ring]
    exact dvd_mul_of_dvd_right hn _

/-- Three distinct non special primes `p ≡ 1 (mod 3)` of exponent two each put a factor `3`
into `σ(N)`, contradicting `v_3(N) = 2`. -/
private lemma three_primes {N q p₁ p₂ p₃ : ℕ} (h : OddPerfect N)
    (h3 : N.factorization 3 = 2)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2)
    (hp₁ : p₁.Prime) (hN₁ : p₁ ∣ N) (hq₁ : p₁ ≠ q) (hm₁ : p₁ % 3 = 1)
    (hp₂ : p₂.Prime) (hN₂ : p₂ ∣ N) (hq₂ : p₂ ≠ q) (hm₂ : p₂ % 3 = 1)
    (hp₃ : p₃.Prime) (hN₃ : p₃ ∣ N) (hq₃ : p₃ ≠ q) (hm₃ : p₃ % 3 = 1)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) : False := by
  let f := fun p => (σ 1 (p ^ N.factorization p)).factorization 3
  have hbal := OPNStarter.valuation_balance h.perfect 3
  change (2 : ℕ).factorization 3 + N.factorization 3 = ∑ p ∈ N.primeFactors, f p at hbal
  rw [h3, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3 ∣ 2)] at hbal
  have hall : ∀ p ∈ ({p₁, p₂, p₃} : Finset ℕ), p.Prime ∧ p ∣ N ∧ p ≠ q ∧ p % 3 = 1 := by
    intro p hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨hp₁, hN₁, hq₁, hm₁⟩
    · exact ⟨hp₂, hN₂, hq₂, hm₂⟩
    · exact ⟨hp₃, hN₃, hq₃, hm₃⟩
  have hsub : ({p₁, p₂, p₃} : Finset ℕ) ⊆ N.primeFactors := fun p hm => by
    obtain ⟨hpp, hpN, -, -⟩ := hall p hm
    exact Nat.mem_primeFactors.mpr ⟨hpp, hpN, h.ne_zero⟩
  have hone : ∀ p ∈ ({p₁, p₂, p₃} : Finset ℕ), 1 ≤ f p := fun p hm => by
    obtain ⟨hpp, -, hpq, hp3⟩ := hall p hm
    have he := hsq p (hsub hm) hpq
    have hne : σ 1 (p ^ N.factorization p) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
    have hd : 3 ∣ σ 1 (p ^ N.factorization p) := by
      rw [he, sigma_one_apply_prime_pow hpp, Nat.dvd_iff_mod_eq_zero]
      simp [Finset.sum_range_succ, Nat.add_mod, Nat.pow_mod, hp3]
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hne).mp (by simpa using hd)
  have hle : ∑ p ∈ ({p₁, p₂, p₃} : Finset ℕ), f p ≤ ∑ p ∈ N.primeFactors, f p :=
    Finset.sum_le_sum_of_subset hsub
  have hcard : ({p₁, p₂, p₃} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  have hlow : 3 ≤ ∑ p ∈ ({p₁, p₂, p₃} : Finset ℕ), f p := by
    have := Finset.card_nsmul_le_sum _ f 1 hone
    rwa [hcard, smul_eq_mul, mul_one] at this
  omega

/-- Steuerwald's theorem, case `3 ∣ N`. -/
theorem steuerwald_of_three_dvd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2) (h3 : 3 ∣ N) : False := by
  obtain ⟨q', -, -, hq4, -, hev⟩ := exists_special_prime h
  have hqq : q = q' := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (hev q hq hne)
  subst hqq
  have hpN : ∀ p, p.Prime → p ∣ N → p ≠ q → N.factorization p = 2 := fun p hp hd hne =>
    hsq p (Nat.mem_primeFactors.mpr ⟨hp, hd, h.ne_zero⟩) hne
  have hq3 : (3 : ℕ) ≠ q := by rintro rfl; norm_num at hq4
  have h3e := hpN 3 Nat.prime_three h3 hq3
  have force2 : ∀ p r, p.Prime → p ∣ N → p ≠ q → r.Prime → r ≠ 2 → r ∣ σ 1 (p ^ 2) →
      r ∣ N := fun p r hp hd hne hr hr2 hdiv =>
    OPNStarter.force_prime h.perfect hp (hpN p hp hd hne) hr hr2 hdiv
  have forceq : ∀ r, r.Prime → r ≠ 2 → r ∣ q + 1 → r ∣ N := fun r hr hr2 hdiv =>
    OPNStarter.force_prime h.perfect hq rfl hr hr2
      (by rw [sigma_one_apply_prime_pow hq]; exact dvd_geom_of_odd' hdiv hodd)
  have d13 : 13 ∣ N := force2 3 13 Nat.prime_three h3 hq3 (by norm_num) (by norm_num)
    (by rw [sigma_one_apply_prime_pow Nat.prime_three]; decide)
  by_cases h13q : 13 = q
  · -- Case B: `q = 13`, so `7 ∣ 14 ∣ σ(13^k)`; then `19` and `127` follow.
    subst h13q
    have d7 : 7 ∣ N := forceq 7 (by norm_num) (by norm_num) (by norm_num)
    have d19 : 19 ∣ N := force2 7 19 (by norm_num) d7 (by norm_num) (by norm_num)
      (by norm_num) (by rw [sigma_one_apply_prime_pow (by norm_num)]; decide)
    have d127 : 127 ∣ N := force2 19 127 (by norm_num) d19 (by norm_num) (by norm_num)
      (by norm_num) (by rw [sigma_one_apply_prime_pow (by norm_num)]; decide)
    exact three_primes (p₁ := 7) (p₂ := 19) (p₃ := 127) h h3e hsq
      (by norm_num) d7 (by norm_num) (by norm_num)
      (by norm_num) d19 (by norm_num) (by norm_num)
      (by norm_num) d127 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have d61 : 61 ∣ N := force2 13 61 (by norm_num) d13 h13q (by norm_num) (by norm_num)
    (by rw [sigma_one_apply_prime_pow (by norm_num)]; decide)
  by_cases h61q : 61 = q
  · -- Case A2: `q = 61`, so `31 ∣ 62 ∣ σ(61^k)`; then `331` follows.
    subst h61q
    have d31 : 31 ∣ N := forceq 31 (by norm_num) (by norm_num) (by norm_num)
    have d331 : 331 ∣ N := force2 31 331 (by norm_num) d31 (by norm_num) (by norm_num)
      (by norm_num) (by rw [sigma_one_apply_prime_pow (by norm_num)]; decide)
    exact three_primes (p₁ := 13) (p₂ := 31) (p₃ := 331) h h3e hsq
      (by norm_num) d13 (by norm_num) (by norm_num)
      (by norm_num) d31 (by norm_num) (by norm_num)
      (by norm_num) d331 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have d97 : 97 ∣ N := force2 61 97 (by norm_num) d61 h61q (by norm_num) (by norm_num)
    (by rw [sigma_one_apply_prime_pow (by norm_num)]; decide)
  by_cases h97q : 97 = q
  · -- Case A1b: `q = 97`, so `7 ∣ 98 ∣ σ(97^k)`.
    subst h97q
    have d7 : 7 ∣ N := forceq 7 (by norm_num) (by norm_num) (by norm_num)
    exact three_primes (p₁ := 13) (p₂ := 61) (p₃ := 7) h h3e hsq
      (by norm_num) d13 (by norm_num) (by norm_num)
      (by norm_num) d61 (by norm_num) (by norm_num)
      (by norm_num) d7 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  -- Case A1a: `13`, `61`, `97` are all non special.
  exact three_primes (p₁ := 13) (p₂ := 61) (p₃ := 97) h h3e hsq
    (by norm_num) d13 (Ne.symm (Ne.symm h13q)) (by norm_num)
    (by norm_num) d61 h61q (by norm_num)
    (by norm_num) d97 h97q (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end OddPerfect

#print axioms OddPerfect.steuerwald_of_three_dvd
