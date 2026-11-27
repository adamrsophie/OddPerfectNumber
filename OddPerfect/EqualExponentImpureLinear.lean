import OddPerfect.IndexColumnLower
import OddPerfect.UniformExponents

/-!
# Equal exponents: impure rows grow linearly with the index prime

Let `N` be an odd perfect number with special prime `q` and let every ordinary exponent equal
`l - 1` for an odd prime `l`. A row `σ(p ^ (l - 1))` is called pure when it is a prime power.

* `not_sigma_pow_pred_eq_prime_pow_of_mod_eq_one`: a prime `p` that is `1` modulo `l` has no
  pure row of length `l`. The row `R = σ(p ^ (l - 1))` has `v_l(R) = 1`, so a prime power `R`
  would equal `l`, while `R ≥ p + 1 > l`.
* `two_mul_index_pred_le_three_mul_card_impure`: every set `M` that contains all ordinary
  prime factors with an impure row satisfies `2 (l - 1) ≤ 3 |M|`, since it contains every
  ordinary prime factor that is `1` modulo `l`.
* `index_pred_le_card_impure_of_not_dvd_special_index`: if moreover `l ∤ v_q(N) + 1`, then
  `l - 1 ≤ |M|`.

These are restricted results for the family where all ordinary exponents equal `l - 1`; they
do not apply to the wider family where `l` only divides the indices. They are lower bounds for
a count; no family is excluded. Restricted result; no published source was checked; novelty
not verified. The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- A prime that is `1` modulo an odd prime `l` has no prime power row of length `l`:
`σ(p ^ (l - 1))` is not a prime power. Restricted result; no published source was checked;
novelty not verified. -/
theorem not_sigma_pow_pred_eq_prime_pow_of_mod_eq_one {l p : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hp : p.Prime) (hp1 : p % l = 1) :
    ¬ ∃ r w, r.Prime ∧ σ 1 (p ^ (l - 1)) = r ^ w := by
  rintro ⟨r, w, hr, hrw⟩
  have : Fact l.Prime := ⟨hl⟩
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hv := padicValNat_sigma_of_mod_eq_one hp hl hl2 hp1 (a := l - 1)
  simp only [Nat.padicValNat_def] at hv
  rw [hl1, Nat.Prime.multiplicity_self] at hv
  have hdvd : l ∣ σ 1 (p ^ (l - 1)) := dvd_of_one_le_multiplicity (by rw [hv])
  rw [hrw] at hdvd
  have hlr : l = r := (Nat.prime_dvd_prime_iff_eq hl hr).mp (hl.dvd_of_dvd_pow hdvd)
  rw [← hlr] at hrw
  rw [hrw, Nat.multiplicity_prime_pow] at hv
  have hge : 1 + p ≤ σ 1 (p ^ (l - 1)) := by
    rw [sigma_one_apply_prime_pow hp, hl1]
    calc 1 + p = ∑ i ∈ Finset.range 2, p ^ i := by
          rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
      _ ≤ ∑ i ∈ Finset.range l, p ^ i :=
          Finset.sum_le_sum_of_subset (Finset.range_mono hl.two_le)
  have hlp : l < p := by
    by_contra hlt
    rcases (not_lt.mp hlt).lt_or_eq with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at hp1
      exact hp.one_lt.ne' hp1
    · rw [h', Nat.mod_self] at hp1
      omega
  rw [hrw, hv, pow_one] at hge
  omega

/-- Equal exponents, impure rows. If every ordinary exponent of the odd perfect number `N`
equals `l - 1` for an odd prime `l`, then every set `M` containing all ordinary prime factors
whose row is not a prime power satisfies `2 (l - 1) ≤ 3 |M|`. Restricted result for the family
where all ordinary exponents equal `l - 1`, not for the wider family where `l` only divides the
indices; a lower bound for a count, no family is excluded. Restricted result; no published
source was checked; novelty not verified. -/
theorem two_mul_index_pred_le_three_mul_card_impure {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) :
    2 * (l - 1) ≤ 3 * M.card := by
  have hmain := two_mul_index_pred_le_three_mul_card_of_equal_exponents h hq hodd hl hl2 hexp
  have hsub : (N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1) ⊆ M := by
    intro p hp
    obtain ⟨hpN, hpq, hp1⟩ := Finset.mem_filter.mp hp
    by_contra hpM
    have hrow := hM p hpN hpq hpM
    rw [hexp p hpN hpq] at hrow
    exact not_sigma_pow_pred_eq_prime_pow_of_mod_eq_one hl hl2
      (Nat.prime_of_mem_primeFactors hpN) hp1 hrow
  have hle := Finset.card_le_card hsub
  omega

/-- Equal exponents, impure rows, special index prime to `l`. If every ordinary exponent of
the odd perfect number `N` equals `l - 1` for an odd prime `l` and `l ∤ v_q(N) + 1`, then every
set `M` containing all ordinary prime factors whose row is not a prime power satisfies
`l - 1 ≤ |M|`. Restricted result for the family where all ordinary exponents equal `l - 1`, not
for the wider family where `l` only divides the indices; a lower bound for a count, no family
is excluded. Restricted result; no published source was checked; novelty not verified. -/
theorem index_pred_le_card_impure_of_not_dvd_special_index {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hc : ¬ l ∣ N.factorization q + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) :
    l - 1 ≤ M.card := by
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => ⟨1, by rw [hexp p hp hpq, hl1, pow_one]⟩
  have hlq := LCol.ne_of_prime_pow_index h hl hodd hidx'
  have hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1 :=
    fun p hp hpq => by rw [hexp p hp hpq, hl1]
  have hlN : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl,
    (dvd_pow_self l (by norm_num : (4 : ℕ) ≠ 0)).trans (pow_four_dvd_of_dvd_succ h hq hodd hcomp),
    h.ne_zero⟩
  have hcard := card_congrPrimes_add_padicValNat h hq hodd hl hexp hlN hlq
  simp only [Nat.padicValNat_def] at hcard
  rw [multiplicity_eq_zero_of_not_dvd hc, add_zero] at hcard
  have hsub : congrPrimes N q l ⊆ M := by
    intro p hp
    obtain ⟨hpN, hpq, hp1⟩ := Finset.mem_filter.mp hp
    by_contra hpM
    have hrow := hM p hpN hpq hpM
    rw [hexp p hpN hpq] at hrow
    exact not_sigma_pow_pred_eq_prime_pow_of_mod_eq_one hl hl2
      (Nat.prime_of_mem_primeFactors hpN) hp1 hrow
  have hle := Finset.card_le_card hsub
  omega

end OddPerfect

#print axioms OddPerfect.not_sigma_pow_pred_eq_prime_pow_of_mod_eq_one
#print axioms OddPerfect.two_mul_index_pred_le_three_mul_card_impure
#print axioms OddPerfect.index_pred_le_card_impure_of_not_dvd_special_index
