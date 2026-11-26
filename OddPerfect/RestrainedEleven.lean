import OddPerfect.RestrainedTen
import OddPerfect.RestrainedElevenData1
import OddPerfect.RestrainedElevenData2
import OddPerfect.RestrainedElevenData3
import OddPerfect.RestrainedElevenData4
import OddPerfect.RestrainedElevenData5
import OddPerfect.RestrainedElevenData6
import OddPerfect.RestrainedElevenData7

/-!
# Restrained odd perfect numbers: a reciprocal sum sieve for the exponent of 3

Setting of `restrained_not_dvd_of_lt`: `N` is an odd perfect number with special prime `q`,
`r ≠ q` is a further prime, and every prime factor other than `q` and `r` has exponent exactly
2. The landed results give `r = 3`, and every prime factor other than 3 is at least
`B = 132257`. Let `R` be the prime factors other than `3` and `q`.

* A prime `r ∈ R` is `Good`: no `w` with `2 ≤ w < B`, `w` odd and `3 ∤ w`, divides
  `r ^ 2 + r + 1 = σ(r ^ 2)`, since `σ(r ^ 2) ∣ 2N` and the least prime factor of `w` would be
  a prime `5 ≤ p < B` dividing `N` (`good_of_mem`).
* The sieve data (`RestrainedElevenData*`, checked by `RestrainedElevenCheck.runL`) gives a set
  `T` in `[B, 10 ^ 6]` (9063 numbers by the generator's count) that contains every prime
  `Good` number of that range,
  with `2 ^ 64 ∏_{n ∈ T} n X / ((n - 1) (X + 1)) ≤ aF`, `X = 10 ^ 6`, `aF` an explicit
  integer (`cert_all`).
* With `y = (X + 1) / X`: `4/3 < ∏_{p ≠ 3} σ(p ^ e)/p ^ e < (B/(B - 1)) y ^ #R ∏_T (…)`, since
  `r/(r - 1) = y · n X / ((n - 1) (X + 1))` at `n = r`, the factor is at most 1 for `r > X`
  and at least 1 for `n ∈ T` (`card_gt_of_cert`). One kernel comparison
  (`final_ineq`) then gives `#R ≥ 275249`.
* Consequences: `ω(N) ≥ 275251` (`restrained_omega_ge_sieve`), `v_3(N) ≥ 137624` by
  `ω(N) ≤ 2 v_3(N) + 3` (`restrained_sieve_le_three`), and `Ω(N) ≥ 688123`
  (`restrained_Omega_ge_sieve`).

Relation to the literature. Ochem and Zelinsky (arXiv 2607.19746) state a far larger lower
bound for this exponent, obtained by a long computation; that bound is not proved here. The
theorems of this file are conditional family results checked by the kernel; no novelty is
claimed. The odd perfect number conjecture is open and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

namespace RestrainedEleven

open RestrainedSeven RestrainedEight RestrainedElevenCheck

/-- The certificate of the whole range `132257 ≤ n ≤ 10 ^ 6`. -/
theorem cert_all : Cert 1000000 132257 1000001 18446744073709551616 18677387639328032348 :=
  cert_trans (cert_trans (cert_trans (cert_trans (cert_trans (cert_trans cert1 cert2) cert3)
    cert4) cert5) cert6) cert7

/-- The one large comparison, on numbers of about 1,650,000 digits. -/
theorem final_ineq : 3 * 132257 * 18677387639328032348 * 1000001 ^ 275248 ≤
    4 * 132256 * 18446744073709551616 * 1000000 ^ 275248 := by
  decide +kernel

/-- `r / (r - 1) = y · fac X r` with `y = (X + 1) / X`. -/
theorem div_pred_eq {X r : ℕ} (hX : 1 ≤ X) (hr : 2 ≤ r) :
    (r : ℚ) / (r - 1) = ((X + 1 : ℚ) / X) * fac X r := by
  unfold fac
  have h1 : ((r - 1 : ℕ) : ℚ) = (r : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  push_cast
  rw [h1]
  have hX0 : (X : ℚ) ≠ 0 := by positivity
  have hr1 : (r : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ r := by exact_mod_cast hr
    linarith
  have hX1 : (X : ℚ) + 1 ≠ 0 := by positivity
  field_simp

/-- `fac X n ≤ 1` for `n ≥ X + 1`. -/
theorem fac_le_one {X n : ℕ} (hX : 1 ≤ X) (hn : X + 1 ≤ n) : fac X n ≤ 1 := by
  unfold fac
  have hb : 0 < (n - 1) * (X + 1) := Nat.mul_pos (by omega) (by omega)
  rw [div_le_one (by exact_mod_cast hb)]
  have : n * X ≤ (n - 1) * (X + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  exact_mod_cast this

/-- `1 ≤ fac X n` for `2 ≤ n ≤ X + 1`. -/
theorem one_le_fac {X n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ X + 1) : 1 ≤ fac X n := by
  unfold fac
  have hb : 0 < (n - 1) * (X + 1) := Nat.mul_pos (by omega) (by omega)
  rw [one_le_div (by exact_mod_cast hb)]
  have : (n - 1) * (X + 1) ≤ n * X := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  exact_mod_cast this

/-- **The counting step.** Let `N` be an odd perfect number with `3 ∣ N`, `q ≠ 3` a prime factor
with `B ≤ q`, and `R` the prime factors other than 3 and `q`, each `Good` and at least `B`. If
`Cert X B X₁ a b` and `3 B b X₁ ^ K ≤ 4 (B - 1) a X ^ K` (with `B = c + 1`, `X₁ = X + 1`), then
`K < #R`. -/
theorem card_gt_of_cert {N q X X₁ B c a b K : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (hqN : q ∈ N.primeFactors) (hq3 : q ≠ 3) (hBc : B = c + 1) (hc : 1 ≤ c) (hqB : B ≤ q)
    (hR : ∀ r ∈ (N.primeFactors.erase 3).erase q, Good r ∧ B ≤ r) (hX : 1 ≤ X)
    (hX₁ : X₁ = X + 1) (hcert : Cert X B X₁ a b) (ha : 0 < a)
    (hineq : 3 * B * b * X₁ ^ K ≤ 4 * c * a * X ^ K) :
    K < ((N.primeFactors.erase 3).erase q).card := by
  classical
  subst hBc hX₁
  set R := (N.primeFactors.erase 3).erase q with hRdef
  obtain ⟨-, T, hT, hcov, hprod⟩ := hcert
  have hgt := prod_erase_three_gt h h3
  have hqm : q ∈ N.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨hq3, hqN⟩
  rw [← Finset.mul_prod_erase _ _ hqm] at hgt
  have hrp : ∀ r ∈ R, r.Prime := fun r hr =>
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
  set y : ℚ := ((X + 1 : ℚ) / X) with hy
  have hy1 : 1 ≤ y := by
    rw [hy, le_div_iff₀ (by exact_mod_cast hX)]
    linarith
  -- the component of `q`
  have hAq : abundancy (q ^ N.factorization q) ≤ ((c + 1 : ℕ) : ℚ) / c :=
    (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hqN) _).le.trans
      (div_pred_le hc hqB)
  have hAq0 : 0 ≤ abundancy (q ^ N.factorization q) :=
    (abundancy_pos (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hqN).ne_zero)).le
  -- the components of `R`
  have hP0 : 0 ≤ ∏ r ∈ R, abundancy (r ^ N.factorization r) :=
    Finset.prod_nonneg fun r hr => (abundancy_pos (pow_ne_zero _ (hrp r hr).ne_zero)).le
  have hP1 : ∏ r ∈ R, abundancy (r ^ N.factorization r) ≤ ∏ r ∈ R, y * fac X r := by
    refine Finset.prod_le_prod₀ (fun r hr => (abundancy_pos (pow_ne_zero _
      (hrp r hr).ne_zero)).le) fun r hr => ?_
    rw [hy, ← div_pred_eq hX (hrp r hr).two_le]
    exact (abundancy_prime_pow_lt (hrp r hr) _).le
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hP1
  have hF0 : ∀ n, 0 ≤ fac X n := fac_nonneg X
  have hsub1 : ∏ r ∈ R, fac X r ≤ ∏ r ∈ R ∩ T, fac X r := by
    refine Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_left
      (fun r _ => hF0 r) fun r hr hrT => fac_le_one hX ?_
    by_contra hlt
    exact hrT (Finset.mem_inter.mpr ⟨hr, hcov r (hR r hr).2 (by omega) (hrp r hr) (hR r hr).1⟩)
  have hsub2 : ∏ r ∈ R ∩ T, fac X r ≤ ∏ n ∈ T, fac X n := by
    refine Finset.prod_le_prod_of_subset_of_one_le₀ Finset.inter_subset_right
      (fun r _ => hF0 r) fun n hn _ => ?_
    have := hT n hn
    exact one_le_fac (by omega) (by omega)
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hTb : ∏ n ∈ T, fac X n ≤ (b : ℚ) / a := by
    rw [le_div_iff₀ ha', mul_comm]
    exact hprod
  by_contra hK
  have hRK : R.card ≤ K := by omega
  have hyK : y ^ R.card ≤ y ^ K := pow_le_pow_right₀ hy1 hRK
  have hy0 : 0 ≤ y ^ K := pow_nonneg (by linarith) K
  have hfin : (4 : ℚ) / 3 < ((c + 1 : ℕ) : ℚ) / c * (y ^ K * ((b : ℚ) / a)) := by
    refine lt_of_lt_of_le hgt (mul_le_mul hAq ?_ hP0 (by positivity))
    calc ∏ r ∈ R, abundancy (r ^ N.factorization r) ≤ y ^ R.card * ∏ r ∈ R, fac X r := hP1
      _ ≤ y ^ K * ((b : ℚ) / a) :=
        mul_le_mul hyK ((hsub1.trans hsub2).trans hTb)
          (Finset.prod_nonneg fun r _ => hF0 r) hy0
  have hq : ((3 * (c + 1) * b * (X + 1) ^ K : ℕ) : ℚ) ≤ ((4 * c * a * X ^ K : ℕ) : ℚ) := by
    exact_mod_cast hineq
  push_cast at hq
  have hc' : (0 : ℚ) < c := by exact_mod_cast hc
  have hX' : (0 : ℚ) < X := by exact_mod_cast hX
  have hXK : (0 : ℚ) < (X : ℚ) ^ K := pow_pos hX' K
  rw [hy, div_pow] at hfin
  have ha'' : (0 : ℚ) < a := ha'
  have hkey : ((c + 1 : ℕ) : ℚ) / c * (((X : ℚ) + 1) ^ K / (X : ℚ) ^ K * ((b : ℚ) / a)) =
      (((c : ℚ) + 1) * b * ((X : ℚ) + 1) ^ K) / (c * a * (X : ℚ) ^ K) := by
    push_cast
    ring
  rw [hkey, lt_div_iff₀ (by positivity)] at hfin
  linarith

/-- In the restrained family, every prime factor other than `q` and `3` is `Good`. -/
theorem good_of_mem {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t ∈ N.primeFactors) (htq : t ≠ q) (ht3 : t ≠ 3) : Good t := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  intro w h2 hlt hw2 hw3 hdvd
  have htp := Nat.prime_of_mem_primeFactors ht
  have he := F.sq t ht htq ht3
  have hd := OPNStarter.component_sigma_dvd F.perf.perfect htp he
  rw [sigma_prime_sq htp, show phi3 t = t * t + t + 1 by unfold phi3; ring] at hd
  have hwN : w ∣ N := dvd_of_dvd_two_mul hw2 (hdvd.trans hd)
  have hp := Nat.minFac_prime (show w ≠ 1 by omega)
  have hpw := Nat.minFac_dvd w
  have hple := Nat.minFac_le (show 0 < w by omega)
  have hp2 : w.minFac ≠ 2 := fun he2 => by
    rw [he2] at hpw
    omega
  have hp3 : w.minFac ≠ 3 := fun he3 => by
    rw [he3] at hpw
    omega
  have h5 : 5 ≤ w.minFac := by
    have := hp.two_le
    rcases (by omega : w.minFac = 2 ∨ w.minFac = 3 ∨ w.minFac = 4 ∨ 5 ≤ w.minFac) with
      h' | h' | h' | h'
    · exact absurd h' hp2
    · exact absurd h' hp3
    · exact absurd (h' ▸ hp) (by norm_num)
    · exact h'
  exact restrained_not_dvd_of_lt h hq hodd hr hrq hsq hp h5 (by omega) (hpw.trans hwN)

end RestrainedEleven

open RestrainedSeven RestrainedEleven

/-- **Restrained family: `ω(N) ≥ 275251`.** With the hypotheses of `restrained_not_dvd_of_lt`,
a kernel checked sieve over the odd numbers up to `10 ^ 6` (witness data in
`RestrainedElevenData*`) and the abundancy `4/3 < ∏_{p ≠ 3} σ(p ^ e)/p ^ e` force at least
275249 prime factors other than 3 and `q`.
Conditional family result checked by the kernel; no novelty is claimed. -/
theorem restrained_omega_ge_sieve {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    275251 ≤ ω N := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have h3 := restrained_three_dvd h hq hodd hr hrq hsq
  have hq3 : q ≠ 3 := by have := F.mod12; omega
  have hqN : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, ?_, h.ne_zero⟩
    obtain ⟨k, hk⟩ := hodd
    exact Nat.dvd_of_factorization_pos (by omega)
  have hlt := card_gt_of_cert (B := 132257) (c := 132256) (X := 1000000) (X₁ := 1000001)
    (K := 275248) h h3
    hqN hq3 rfl (by norm_num) (restrained_le_of_ne_three h hq hodd hr hrq hsq hqN hq3)
    (fun t ht => by
      obtain ⟨htq, ht'⟩ := Finset.mem_erase.mp ht
      obtain ⟨ht3, htN⟩ := Finset.mem_erase.mp ht'
      exact ⟨good_of_mem h hq hodd hr hrq hsq htN htq ht3,
        restrained_le_of_ne_three h hq hodd hr hrq hsq htN ht3⟩)
    (by norm_num) rfl cert_all (by norm_num) final_ineq
  have h3m : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have hqm : q ∈ N.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨hq3, hqN⟩
  rw [Finset.card_erase_of_mem hqm, Finset.card_erase_of_mem h3m] at hlt
  rw [cardDistinctFactors_eq_card_primeFactors]
  omega

/-- **Restrained family: `v_3(N) ≥ 137624`.** From `ω(N) ≥ 275251` and
`ω(N) ≤ 2 v_3(N) + 3` (`restrained_omega_le`). Ochem and Zelinsky (arXiv 2607.19746) state a
far larger bound for this exponent, obtained by a long computation; it is not proved here.
Conditional family result checked by the kernel; no novelty is claimed. -/
theorem restrained_sieve_le_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    137624 ≤ N.factorization 3 := by
  have h1 := restrained_omega_ge_sieve h hq hodd hr hrq hsq
  have h2 := restrained_omega_le h hq hodd hr hrq hsq
  omega

/-- **Restrained family: `Ω(N) ≥ 688123`.** From `ω(N) ≥ 275251`, `v_3(N) ≥ 137624` and
`2 ω(N) + v_3(N) ≤ Ω(N) + 3`.
Conditional family result checked by the kernel; no novelty is claimed. -/
theorem restrained_Omega_ge_sieve {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    688123 ≤ Ω N := by
  have h1 := restrained_omega_ge_sieve h hq hodd hr hrq hsq
  have h2 := restrained_sieve_le_three h hq hodd hr hrq hsq
  have h3 := two_mul_card_add_factorization_three_le h
  omega

end OddPerfect

#print axioms OddPerfect.RestrainedEleven.cert_all
#print axioms OddPerfect.RestrainedEleven.final_ineq
#print axioms OddPerfect.RestrainedEleven.div_pred_eq
#print axioms OddPerfect.RestrainedEleven.fac_le_one
#print axioms OddPerfect.RestrainedEleven.one_le_fac
#print axioms OddPerfect.RestrainedEleven.card_gt_of_cert
#print axioms OddPerfect.RestrainedEleven.good_of_mem
#print axioms OddPerfect.restrained_omega_ge_sieve
#print axioms OddPerfect.restrained_sieve_le_three
#print axioms OddPerfect.restrained_Omega_ge_sieve
