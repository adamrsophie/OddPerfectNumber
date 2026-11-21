import OddPerfect.Certificate
import OddPerfect.Steuerwald
import OddPerfect.SpecialPrime

/-!
# Exponent six (Hagis and McDaniel 1972)

In an odd perfect number the primes other than the special prime cannot all have exponent
exactly six.

* `7 ∤ N`: Steuerwald's prime length argument with `l = 7`.
* `7 ∣ N`: since `7 ≡ 3 (mod 4)`, `7` is ordinary and `v_7(N) = 6`. Every ordinary prime
  `p ≡ 1 (mod 7)` has `7 ∣ σ(p^6)`, so seven such primes overflow the `7`-adic ledger.
  The forcing chain starts with `σ(7^6) = 29 · 4733`; the special prime `q` is one of
  `4733`, `70001`, or neither.
  * neither: `7 → 4733 → 70001 → 50359 → 71 → 883 → 379 → 43`.
  * `q = 4733`: `q + 1 = 2 · 3^2 · 263` forces `3` and `263`; then `3 → 1093 → 14939 → 197`,
    `263 → 239, 7211`, and `7 → 29 → 88009573`.
  * `q = 70001`: `q + 1 = 2 · 3^3 · 3889` forces `3`; then `3 → 1093 → 14939 → 197`,
    `7 → 29 → 88009573`, and `7 → 4733 → 69655517`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- One forcing step: an odd prime `r ≠ q` dividing `σ(p^6)` for an exact component `p^6`
divides `N`, hence has exponent six. -/
private lemma forced_six {N q p r : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 6)
    (hp : p.Prime) (hpN : N.factorization p = 6) (hr : r.Prime) (hr2 : r ≠ 2)
    (hdiv : r ∣ Cert.geom p 6) (hrq : r ≠ q) : N.factorization r = 6 := by
  have hrN : r ∣ N := OPNStarter.force_prime h.perfect hp hpN hr hr2
    (by rw [Cert.sigma_eq_geom hp]; exact hdiv)
  exact hexp r (Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩) hrq

/-- The `7`-adic overflow: seven primes `≡ 1 (mod 7)` with exponent six each contribute a
factor `7` to `σ N`, exceeding `v_7(N) = 6`. -/
private lemma overflow_seven {N : ℕ} (h : OddPerfect N) (h7 : N.factorization 7 = 6)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ N.factorization p = 6 ∧ p % 7 = 1)
    (hcard : 6 < S.card) : False := by
  have hN := h.ne_zero
  have p7 : Nat.Prime 7 := by norm_num
  have hsub : S ⊆ N.primeFactors := fun p hp => by
    obtain ⟨hpp, he, -⟩ := hS p hp
    exact Nat.mem_primeFactors.mpr ⟨hpp, Nat.dvd_of_factorization_pos (by omega), hN⟩
  have hone : ∀ p ∈ S, 1 ≤ (σ 1 (p ^ N.factorization p)).factorization 7 := by
    intro p hp
    obtain ⟨hpp, he, h1⟩ := hS p hp
    rw [he, Cert.sigma_eq_geom hpp]
    have hpos : Cert.geom p 6 ≠ 0 := by simp [Cert.geom]
    refine (p7.dvd_iff_one_le_factorization hpos).mp (Nat.dvd_of_mod_eq_zero ?_)
    simp [Cert.geom, Nat.add_mod, Nat.pow_mod, h1]
  have hbal := OPNStarter.valuation_balance h.perfect 7
  have h2 : Nat.factorization 2 7 = 0 := by
    rw [Nat.prime_two.factorization, Finsupp.single_apply, if_neg (by norm_num)]
  have hle := Finset.sum_le_sum_of_subset
    (f := fun p => (σ 1 (p ^ N.factorization p)).factorization 7) hsub
  have hge := Finset.card_nsmul_le_sum S
    (fun p => (σ 1 (p ^ N.factorization p)).factorization 7) 1 hone
  simp only [smul_eq_mul, mul_one] at hge
  omega

/-- `3 ∣ N` and the exponent of `3` is six when `3 ∣ q + 1` for the special prime `q`. -/
private lemma three_of_special {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 6)
    (h3q : 3 ∣ q + 1) (hq3 : q ≠ 3) : N.factorization 3 = 6 := by
  have h3N : 3 ∣ N := by
    have : 3 ∣ 2 * N := (h3q.trans (succ_dvd_sigma_special hq hodd)).trans
      (OPNStarter.component_sigma_dvd h.perfect hq rfl)
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this
  exact hexp 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3N, h.ne_zero⟩) (Ne.symm hq3)

/-- Exponent six, case `7 ∣ N` and the special prime is neither `4733` nor `70001`. -/
theorem not_all_exponents_six_of_seven_dvd_generic {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 6)
    (h7 : 7 ∣ N) (ha : q ≠ 4733) (hb : q ≠ 70001) : False := by
  have hq4 := (special_mod_four h hq hodd).1
  have e7 : N.factorization 7 = 6 :=
    hexp 7 (Nat.mem_primeFactors.mpr ⟨by norm_num, h7, h.ne_zero⟩) (by omega)
  have e4733 := forced_six (r := 4733) h hexp (by norm_num) e7 (by norm_num) (by norm_num)
    (by decide) (Ne.symm ha)
  have e70001 := forced_six (r := 70001) h hexp (by norm_num) e4733 (by norm_num)
    (by norm_num) (by decide) (Ne.symm hb)
  have e50359 := forced_six (r := 50359) h hexp (by norm_num) e70001 (by norm_num)
    (by norm_num) (by decide) (by omega)
  have e71 := forced_six (r := 71) h hexp (by norm_num) e50359 (by norm_num)
    (by norm_num) (by decide) (by omega)
  have e883 := forced_six (r := 883) h hexp (by norm_num) e71 (by norm_num)
    (by norm_num) (by decide) (by omega)
  have e379 := forced_six (r := 379) h hexp (by norm_num) e883 (by norm_num)
    (by norm_num) (by decide) (by omega)
  have e43 := forced_six (r := 43) h hexp (by norm_num) e379 (by norm_num)
    (by norm_num) (by decide) (by omega)
  refine overflow_seven h e7 {4733, 70001, 50359, 71, 883, 379, 43} ?_ (by decide)
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, e4733, by norm_num⟩
  · exact ⟨by norm_num, e70001, by norm_num⟩
  · exact ⟨by norm_num, e50359, by norm_num⟩
  · exact ⟨by norm_num, e71, by norm_num⟩
  · exact ⟨by norm_num, e883, by norm_num⟩
  · exact ⟨by norm_num, e379, by norm_num⟩
  · exact ⟨by norm_num, e43, by norm_num⟩

/-- Exponent six, case `7 ∣ N` and the special prime is `4733`. -/
theorem not_all_exponents_six_of_special_4733 {N : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 4733))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 4733 → N.factorization p = 6)
    (h7 : 7 ∣ N) : False := by
  have hq : Nat.Prime 4733 := by norm_num
  have e7 : N.factorization 7 = 6 :=
    hexp 7 (Nat.mem_primeFactors.mpr ⟨by norm_num, h7, h.ne_zero⟩) (by norm_num)
  have e3 := three_of_special h hq hodd hexp (by norm_num) (by norm_num)
  have h263 : 263 ∣ N := by
    have : 263 ∣ 2 * N := ((by norm_num : 263 ∣ 4733 + 1).trans
      (succ_dvd_sigma_special hq hodd)).trans (OPNStarter.component_sigma_dvd h.perfect hq rfl)
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this
  have e263 : N.factorization 263 = 6 :=
    hexp 263 (Nat.mem_primeFactors.mpr ⟨by norm_num, h263, h.ne_zero⟩) (by norm_num)
  have e29 := forced_six (r := 29) h hexp (by norm_num) e7 (by norm_num) (by norm_num)
    (by decide) (by norm_num)
  have e88009573 := forced_six (r := 88009573) h hexp (by norm_num) e29 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have e1093 := forced_six (r := 1093) h hexp Nat.prime_three e3 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have e14939 := forced_six (r := 14939) h hexp (by norm_num) e1093 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have e197 := forced_six (r := 197) h hexp (by norm_num) e14939 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have e239 := forced_six (r := 239) h hexp (by norm_num) e263 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have e7211 := forced_six (r := 7211) h hexp (by norm_num) e263 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  refine overflow_seven h e7 {29, 88009573, 1093, 14939, 197, 239, 7211} ?_ (by decide)
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, e29, by norm_num⟩
  · exact ⟨by norm_num, e88009573, by norm_num⟩
  · exact ⟨by norm_num, e1093, by norm_num⟩
  · exact ⟨by norm_num, e14939, by norm_num⟩
  · exact ⟨by norm_num, e197, by norm_num⟩
  · exact ⟨by norm_num, e239, by norm_num⟩
  · exact ⟨by norm_num, e7211, by norm_num⟩

/-- Exponent six, case `7 ∣ N` and the special prime is `70001`. -/
theorem not_all_exponents_six_of_special_70001 {N : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 70001))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 70001 → N.factorization p = 6)
    (h7 : 7 ∣ N) : False := by
  have hq : Nat.Prime 70001 := by norm_num
  have e7 : N.factorization 7 = 6 :=
    hexp 7 (Nat.mem_primeFactors.mpr ⟨by norm_num, h7, h.ne_zero⟩) (by norm_num)
  have e3 := three_of_special h hq hodd hexp (by norm_num) (by norm_num)
  have e29 := forced_six (r := 29) h hexp (by norm_num) e7 (by norm_num) (by norm_num)
    (by decide) (by norm_num)
  have e4733 := forced_six (r := 4733) h hexp (by norm_num) e7 (by norm_num) (by norm_num)
    (by decide) (by norm_num)
  have e88009573 := forced_six (r := 88009573) h hexp (by norm_num) e29 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have e69655517 := forced_six (r := 69655517) h hexp (by norm_num) e4733 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have e1093 := forced_six (r := 1093) h hexp Nat.prime_three e3 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have e14939 := forced_six (r := 14939) h hexp (by norm_num) e1093 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have e197 := forced_six (r := 197) h hexp (by norm_num) e14939 (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  refine overflow_seven h e7 {29, 4733, 88009573, 69655517, 1093, 14939, 197} ?_ (by decide)
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, e29, by norm_num⟩
  · exact ⟨by norm_num, e4733, by norm_num⟩
  · exact ⟨by norm_num, e88009573, by norm_num⟩
  · exact ⟨by norm_num, e69655517, by norm_num⟩
  · exact ⟨by norm_num, e1093, by norm_num⟩
  · exact ⟨by norm_num, e14939, by norm_num⟩
  · exact ⟨by norm_num, e197, by norm_num⟩

/-- Hagis and McDaniel (1972): in an odd perfect number the exponents of the primes other
than the special prime cannot all equal six. -/
theorem not_all_exponents_six {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 6) : False := by
  by_cases h7 : 7 ∣ N
  · by_cases ha : q = 4733
    · subst ha
      exact not_all_exponents_six_of_special_4733 h hodd hexp h7
    by_cases hb : q = 70001
    · subst hb
      exact not_all_exponents_six_of_special_70001 h hodd hexp h7
    exact not_all_exponents_six_of_seven_dvd_generic h hq hodd hexp h7 ha hb
  · exact not_all_exponents_eq_pred_prime h hq hodd (l := 7) (by norm_num) (by norm_num) h7 hexp

end OddPerfect

#print axioms OddPerfect.not_all_exponents_six_of_seven_dvd_generic
#print axioms OddPerfect.not_all_exponents_six_of_special_4733
#print axioms OddPerfect.not_all_exponents_six_of_special_70001
#print axioms OddPerfect.not_all_exponents_six
