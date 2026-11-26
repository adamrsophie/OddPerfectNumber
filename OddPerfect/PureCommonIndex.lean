import OddPerfect.PureRows
import OddPerfect.EulerPart
import OddPerfect.EqualExponents

/-!
# All ordinary rows pure with a common odd prime in every index

Let `N` be an odd perfect number with special prime `q`. This module shows that the following
family is empty: every ordinary row `σ(p ^ e_p)` (with `p ≠ q` a prime factor of `N`) is a
prime power, and one odd prime `l` divides every ordinary index `e_p + 1`. Nothing bounds `l`,
the special exponent, or the ordinary exponents.

This is a restricted subfamily of the open common index family (one odd prime dividing every
ordinary index, with no purity condition). Families with mixed rows (some ordinary rows not
prime powers), and families of pure rows whose index primes differ, are not covered.
Whether this result is new was not verified against the literature. The odd perfect number
conjecture remains open.

Argument. A pure row with even nonzero exponent `e` has prime index `e + 1`, so `e + 1 = l`
for every ordinary prime. The receiver `r` of a pure row satisfies `r ≡ 1 (mod l)` and is a
prime factor of `N`. No ordinary prime is `1` modulo `l`, since then `l ∣ σ(p ^ (l - 1))`
would force the receiver to be `l`. Hence every receiver is `q`, every ordinary row is a power
of `q`, and so every prime factor of `σ(m ^ 2)` in Euler's form `N = q ^ k m ^ 2` is `q`. A
prime factor of the Euler index `i = σ(m ^ 2) / q ^ k ≥ 3` divides both `m ^ 2` and
`σ(m ^ 2)`, so it is `q`, contradicting `q ∤ m`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Under the hypotheses of `not_all_pure_common_index`, every ordinary row is a power of the
special prime: `σ(p ^ e_p) = q ^ w` for each prime factor `p ≠ q`. -/
theorem ordinary_row_pow_special_of_pure_common_index {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hpure : ∀ p ∈ N.primeFactors, p ≠ q →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) :
    ∀ p ∈ N.primeFactors, p ≠ q → ∃ w, σ 1 (p ^ N.factorization p) = q ^ w := by
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  -- Every ordinary index equals `l`.
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p + 1 = l := by
    intro p hp hpq
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
    have he0 : N.factorization p ≠ 0 :=
      (hp'.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)).ne'
    obtain ⟨r, w, hr, hrow⟩ := hpure p hp hpq
    have hpr := prime_succ_of_sigma_prime_pow_eq_prime_pow hp' hp2
      (even_factorization_of_ne h hq hodd hp' hpq) he0 hr hrow
    exact ((Nat.prime_dvd_prime_iff_eq hl hpr).mp (hidx p hp hpq)).symm
  -- No ordinary prime is `1` modulo `l`.
  have hnot : ∀ p ∈ N.primeFactors, p ≠ q → p % l ≠ 1 := by
    intro p hp hpq h1
    have : Fact l.Prime := ⟨hl⟩
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
    have he := hidx' p hp hpq
    obtain ⟨r, w, hr, hrow⟩ := hpure p hp hpq
    have hv := padicValNat_sigma_of_mod_eq_one (a := N.factorization p) hp' hl hl2 h1
    rw [he, Nat.padicValNat_def (p := l) (n := l), Nat.Prime.multiplicity_self,
      Nat.padicValNat_def] at hv
    have hdvd : l ∣ r ^ w := hrow ▸ dvd_of_one_le_multiplicity (by omega)
    have hlr : l = r := (Nat.prime_dvd_prime_iff_eq hl hr).mp (hl.dvd_of_dvd_pow hdvd)
    have hmod := receiver_mod_index_of_pure hp' hp2 (by omega) hr hrow
    rw [he, ← hlr, Nat.mod_self] at hmod
    exact absurd hmod (by norm_num)
  intro p hp hpq
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  have he := hidx' p hp hpq
  obtain ⟨r, w, hr, hrow⟩ := hpure p hp hpq
  obtain ⟨hrP, -, -⟩ := receiver_of_pure_row h hp hr hrow
  have hmod := receiver_mod_index_of_pure hp' hp2 (by omega) hr hrow
  rw [he] at hmod
  by_cases hrq : r = q
  · exact ⟨w, hrq ▸ hrow⟩
  · exact absurd hmod (hnot r hrP hrq)

/-- **No odd perfect number has all ordinary rows pure and a common odd prime in every
ordinary index.** Let `N` be an odd perfect number with special prime `q`. It is impossible
that `σ(p ^ e_p)` is a prime power for every prime factor `p ≠ q` while one odd prime `l`
divides `e_p + 1` for every prime factor `p ≠ q`. There is no bound on `l` or on the exponents.

This is a restricted subfamily of the open common index family: mixed rows (some ordinary row
not a prime power) and pure rows with different index primes are not covered. Whether this
result is new was not verified against the literature. -/
theorem not_all_pure_common_index {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hpure : ∀ p ∈ N.primeFactors, p ≠ q →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : False := by
  have hrows := ordinary_row_pow_special_of_pure_common_index h hq hodd hl hl2 hidx hpure
  obtain ⟨q', k, m, hq', hN, hqm, -, hk4⟩ := exists_euler_form h
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q')
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hqk : q' ^ k ≠ 0 := pow_ne_zero _ hq'.ne_zero
  have hfac : ∀ p, N.factorization p = (q' ^ k).factorization p + (m ^ 2).factorization p := by
    intro p
    rw [hN, Nat.factorization_mul hqk hm2, Finsupp.add_apply]
  -- The prime `q'` of the Euler form is the special prime `q`.
  have hqq : q' = q := by
    have hk : N.factorization q' = k := by
      rw [hfac, Nat.factorization_pow, Finsupp.smul_apply, hq'.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq'.dvd_of_dvd_pow hd))]
      simp
    exact (existsUnique_odd_exponent h).unique ⟨hq', hk ▸ Nat.odd_iff.mpr (by omega)⟩
      ⟨hq, hodd⟩
  subst hqq
  -- A prime factor `t` of the Euler index divides `m ^ 2` and `σ(m ^ 2)`.
  have hi3 := three_le_eulerIndex h hq hN hqm
  obtain ⟨t, ht, hti⟩ := Nat.exists_prime_and_dvd (show eulerIndex q' k m ≠ 1 by omega)
  have htm : t ∣ m := ht.dvd_of_dvd_pow (hti.trans (eulerIndex_dvd_sq h hq hN hqm))
  have htσ : t ∣ σ 1 (m ^ 2) := by
    rw [sigma_sq_eq_mul_eulerIndex h hq hN hqm]
    exact hti.mul_left _
  rw [isMultiplicative_sigma.multiplicative_factorization _ hm2, Finsupp.prod] at htσ
  obtain ⟨p, hp, htp⟩ := (Prime.dvd_finsetProd_iff ht.prime _).mp htσ
  have hp' := Nat.prime_of_mem_primeFactors (Nat.support_factorization (m ^ 2) ▸ hp)
  have hpm : p ∣ m := hp'.dvd_of_dvd_pow
    (Nat.dvd_of_mem_primeFactors (Nat.support_factorization (m ^ 2) ▸ hp))
  have hpq : p ≠ q' := by rintro rfl; exact hqm hpm
  have hpN : p ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp', hN ▸ (hpm.trans (dvd_pow_self m two_ne_zero)).mul_left _,
      h.ne_zero⟩
  have hfp : (m ^ 2).factorization p = N.factorization p := by
    rw [hfac p, Nat.factorization_eq_zero_of_not_dvd fun hd =>
      hpq ((Nat.prime_dvd_prime_iff_eq hp' hq').mp (hp'.dvd_of_dvd_pow hd)), zero_add]
  obtain ⟨w, hw⟩ := hrows p hpN hpq
  rw [hfp, hw] at htp
  have htq : t = q' := (Nat.prime_dvd_prime_iff_eq ht hq').mp (ht.dvd_of_dvd_pow htp)
  exact hqm (htq ▸ htm)

end OddPerfect

#print axioms OddPerfect.ordinary_row_pow_special_of_pure_common_index
#print axioms OddPerfect.not_all_pure_common_index
