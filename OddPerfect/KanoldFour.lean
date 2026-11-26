import OddPerfect.Certificate
import OddPerfect.Steuerwald
import OddPerfect.Valuation
import OddPerfect.SpecialPrime

/-!
# Kanold's theorem for exponent four

Kanold (1941): in an odd perfect number the primes other than the special prime cannot all
have exponent exactly four.

* `5 ∤ N`: Steuerwald's prime length argument with `l = 5`.
* `5 ∣ N` and `5` ordinary: the `5`-adic ledger is `v_5(N) = 4`. The forcing chain
  `σ(5^4) = 11 · 71`, `σ(11^4) = 5 · 3221`, `σ(71^4) = 5 · 11 · 211 · 2221`,
  `σ(211^4) = 5 · 1361 · 292661` gives the primes `11, 71, 211` (all `≡ 3 (mod 4)`, so
  ordinary) and `1361, 2221, 3221`, at most one of which is special. Five ordinary
  components `σ(p^4)` with `p ≡ 1 (mod 5)` each contribute a factor `5`: overflow.
* `5` special with exponent `k`: `6 ∣ σ(5^k)` forces `3 ∣ N`. No `σ(p^4)` is divisible by
  `3`, so the `3`-adic ledger gives `4 = v_3(σ(5^k)) = 1 + v_3(k + 1)`, hence `6 ∣ k + 1`,
  `σ(5^5) = 2 · 3^2 · 7 · 31 ∣ σ(5^k)` and `7 ∣ N`. Then `3^4 · 5 · 7^4` is abundant.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- One forcing step: an odd prime `r ≠ q` dividing `σ(p^4)` for an exact component `p^4`
divides `N`, hence has exponent four. -/
private lemma forced_four {N q p r : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 4)
    (hp : p.Prime) (hpN : N.factorization p = 4) (hr : r.Prime) (hr2 : r ≠ 2)
    (hdiv : r ∣ Cert.geom p 4) (hrq : r ≠ q) : N.factorization r = 4 := by
  have hrN : r ∣ N := OPNStarter.force_prime h.perfect hp hpN hr hr2
    (by rw [Cert.sigma_eq_geom hp]; exact hdiv)
  exact hexp r (Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩) hrq

/-- Kanold, case `5 ∣ N` with `5` not the special prime. -/
theorem not_all_exponents_four_of_five_ordinary {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 4)
    (h5 : 5 ∣ N) (h5q : (5 : ℕ) ≠ q) : False := by
  have hq4 := (special_mod_four h hq hodd).1
  have e5 : N.factorization 5 = 4 :=
    hexp 5 (Nat.mem_primeFactors.mpr ⟨by norm_num, h5, h.ne_zero⟩) h5q
  have e11 := forced_four (r := 11) h hexp (by norm_num) e5 (by norm_num) (by norm_num)
    (by decide) (by omega)
  have e71 := forced_four (r := 71) h hexp (by norm_num) e5 (by norm_num) (by norm_num)
    (by decide) (by omega)
  have e211 := forced_four (r := 211) h hexp (by norm_num) e71 (by norm_num) (by norm_num)
    (by decide) (by omega)
  have f1361 := fun hne => forced_four (r := 1361) h hexp (by norm_num) e211 (by norm_num)
    (by norm_num) (by decide) hne
  have f2221 := fun hne => forced_four (r := 2221) h hexp (by norm_num) e71 (by norm_num)
    (by norm_num) (by decide) hne
  have f3221 := fun hne => forced_four (r := 3221) h hexp (by norm_num) e11 (by norm_num)
    (by norm_num) (by decide) hne
  by_cases a : q = 1361
  · have e2221 := f2221 (by omega)
    have e3221 := f3221 (by omega)
    exact Cert.check_sound
      (s := [.exact 5 4, .exact 11 4, .exact 71 4, .exact 211 4, .exact 2221 4, .exact 3221 4])
      (c := .overflow 5 4 [(11, 4, 1), (71, 4, 1), (211, 4, 1), (2221, 4, 1), (3221, 4, 1)])
      (by decide +kernel) N h
      (by simp [Cert.State.Holds, Cert.Fact.Holds, e5, e11, e71, e211, e2221, e3221])
  by_cases b : q = 2221
  · have e1361 := f1361 (by omega)
    have e3221 := f3221 (by omega)
    exact Cert.check_sound
      (s := [.exact 5 4, .exact 11 4, .exact 71 4, .exact 211 4, .exact 1361 4, .exact 3221 4])
      (c := .overflow 5 4 [(11, 4, 1), (71, 4, 1), (211, 4, 1), (1361, 4, 1), (3221, 4, 1)])
      (by decide +kernel) N h
      (by simp [Cert.State.Holds, Cert.Fact.Holds, e5, e11, e71, e211, e1361, e3221])
  · have e1361 := f1361 (by omega)
    have e2221 := f2221 (by omega)
    exact Cert.check_sound
      (s := [.exact 5 4, .exact 11 4, .exact 71 4, .exact 211 4, .exact 1361 4, .exact 2221 4])
      (c := .overflow 5 4 [(11, 4, 1), (71, 4, 1), (211, 4, 1), (1361, 4, 1), (2221, 4, 1)])
      (by decide +kernel) N h
      (by simp [Cert.State.Holds, Cert.Fact.Holds, e5, e11, e71, e211, e1361, e2221])

/-- Kanold, case `5` is the special prime. -/
theorem not_all_exponents_four_of_five_special {N : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 → N.factorization p = 4) : False := by
  have hN0 := h.ne_zero
  have p5 : Nat.Prime 5 := by norm_num
  have p7 : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- `3 ∣ N` from `6 ∣ σ(5^k)`
  have h3N : 3 ∣ N := by
    have h6 : 6 ∣ σ 1 (5 ^ N.factorization 5) := succ_dvd_sigma_special p5 hodd
    have : 3 ∣ 2 * N := ((by norm_num : 3 ∣ 6).trans h6).trans
      (OPNStarter.component_sigma_dvd h.perfect p5 rfl)
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
  have e3 : N.factorization 3 = 4 :=
    hexp 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3N, hN0⟩) (by norm_num)
  -- the `3`-adic ledger
  have h5mem : 5 ∈ N.primeFactors := Nat.support_factorization N ▸
    Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  have hled := factorization_three_eq_sum_threeWeight h.perfect
  rw [Finset.sum_eq_single_of_mem 5 h5mem ?_] at hled
  swap
  · intro p hp hp5
    rw [hexp p hp hp5]
    unfold threeWeight
    have h50 : padicValNat 3 5 = 0 := by
      rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd (by norm_num)
    split_ifs with h1 h2 h4
    · rfl
    · exact h50
    · rfl
    · exact absurd (by decide : Even 4) h4
  have h6 : padicValNat 3 6 = 1 := by
    rw [Nat.padicValNat_def, show (6 : ℕ) = 3 * 2 by rfl,
      padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  unfold threeWeight at hled
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (Nat.not_even_iff_odd.mpr hodd),
    e3, show (5 : ℕ) + 1 = 6 by rfl, h6] at hled
  have h3k : 3 ∣ N.factorization 5 + 1 :=
    dvd_of_one_le_multiplicity (by rw [← Nat.padicValNat_def]; omega)
  have h6k : 5 + 1 ∣ N.factorization 5 + 1 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  -- `7 ∣ σ(5^5) ∣ σ(5^k)`
  have h7N : 7 ∣ N := by
    refine OPNStarter.force_prime h.perfect p5 rfl p7 (by norm_num) ?_
    refine Dvd.dvd.trans ?_ (OPNExample.sigma_prime_pow_dvd p5 h6k)
    rw [Cert.sigma_eq_geom p5]
    decide
  have e7 : N.factorization 7 = 4 :=
    hexp 7 (Nat.mem_primeFactors.mpr ⟨p7, h7N, hN0⟩) (by norm_num)
  exact Cert.check_sound (s := [.exact 3 4, .exact 7 4, .powDvd 5 1])
    (c := .abundant [(3, 4), (5, 1), (7, 4)]) (by decide +kernel) N h
    (by simp [Cert.State.Holds, Cert.Fact.Holds, e3, e7, Nat.dvd_of_mem_primeFactors h5mem])

/-- Kanold (1941): in an odd perfect number the exponents of the primes other than the
special prime cannot all equal four. -/
theorem not_all_exponents_four {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 4) : False := by
  by_cases h5 : 5 ∣ N
  · by_cases h5q : q = 5
    · subst h5q
      exact not_all_exponents_four_of_five_special h hodd hexp
    · exact not_all_exponents_four_of_five_ordinary h hq hodd hexp h5 (Ne.symm h5q)
  · exact not_all_exponents_eq_pred_prime h hq hodd (l := 5) (by norm_num) (by norm_num) h5 hexp

end OddPerfect

#print axioms OddPerfect.not_all_exponents_four_of_five_ordinary
#print axioms OddPerfect.not_all_exponents_four_of_five_special
#print axioms OddPerfect.not_all_exponents_four
