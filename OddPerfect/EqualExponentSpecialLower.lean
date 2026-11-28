import OddPerfect.UniformExponents
import OddPerfect.EulerPart
import OddPerfect.IndexColumnLower
import OddPerfect.EqualExponents

/-!
# A lower bound for the special prime when the Euler index is small

Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and suppose
every ordinary exponent equals `l - 1` for an odd prime `l` with `l ∤ a + 1`. Write
`J = eulerIndex q a m`. The ordinary prime factors that are `1` modulo `l` number exactly
`l - 1`. If `J` has fewer than `l - 1` prime factors, one of them, say `p`, does not divide
`J`; then `p ≥ 2 l + 1` and `p ^ (l - 1) ∣ σ(q ^ a)` because `σ(q ^ a) J = 2 m ^ 2`
(`exists_congrPrime_pow_dvd_sigma_special`). Comparing sizes, `q` exceeds every `B` with
`∑_{j ≤ A} B ^ j < (2 l + 1) ^ (l - 1)` whenever `a ≤ A` (`special_gt_of_small_eulerIndex`).

These are restricted results for the family where all ordinary exponents equal `l - 1`: when
the Euler index has fewer than `l - 1` prime factors, the special prime is large. Nothing is
excluded, and the odd perfect number conjecture remains open. Restricted result; no published
source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EqExpSpecLower

/-- The Euler frame: `m ≠ 0`, `v_q(N) = a`, `a` odd, and `v_p(N) = v_p(m ^ 2)` for `p ≠ q`. -/
private lemma frame {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) :
    m ≠ 0 ∧ N.factorization q = a ∧ Odd a ∧
      ∀ p, p ≠ q → N.factorization p = (m ^ 2).factorization p := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : ∀ p, N.factorization p = (q ^ a).factorization p + (m ^ 2).factorization p := by
    intro p
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply]
  have hqa : N.factorization q = a := by
    rw [hfac, hq.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd)), add_zero]
  refine ⟨hm, hqa, ?_, fun p hp => ?_⟩
  · rcases Nat.even_or_odd a with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  · rw [hfac, hq.factorization_pow, Finsupp.single_apply, ite_eq_right (Ne.symm hp), zero_add]

/-- Members of `S` are at least `2 l + 1`. -/
private lemma two_mul_add_one_le {N q l s : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hl2 : l ≠ 2) (hs : s ∈ congrPrimes N q l) : 2 * l + 1 ≤ s := by
  obtain ⟨hsN, -, hs1⟩ := Finset.mem_filter.mp hs
  have hsp := Nat.prime_of_mem_primeFactors hsN
  have hs2 : s ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hsN)
  have hsodd : s % 2 = 1 := Nat.odd_iff.mp (hsp.odd_of_ne_two hs2)
  have h1 : 1 ≤ s := hsp.one_lt.le
  have hld : l ∣ s - 1 := (Nat.modEq_iff_dvd' h1).mp
    (by rw [Nat.ModEq, hs1, Nat.mod_eq_of_lt hl.one_lt])
  have h2d : 2 ∣ s - 1 := by omega
  have hd : 2 * l ∣ s - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2)) h2d hld
  have := Nat.le_of_dvd (by have := hsp.two_le; omega) hd
  omega

end EqExpSpecLower

open EqExpSpecLower in
/-- Equal exponents, small Euler index. Let `N = q ^ a * m ^ 2` be an odd perfect number with
special prime `q`, `q ∤ m`, every ordinary exponent equal to `l - 1` for an odd prime `l`, and
`l ∤ a + 1`. If the Euler index `J = eulerIndex q a m` has fewer than `l - 1` prime factors,
then some prime `p ≥ 2 l + 1` has `p ^ (l - 1) ∣ σ(q ^ a)`. Restricted result for the family
where all ordinary exponents equal `l - 1`; nothing is excluded. Restricted result; no
published source was checked; novelty not verified. -/
theorem exists_congrPrime_pow_dvd_sigma_special {N q a m l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hla : ¬ l ∣ a + 1) (hJ : (eulerIndex q a m).primeFactors.card < l - 1) :
    ∃ p, p.Prime ∧ 2 * l + 1 ≤ p ∧ p ^ (l - 1) ∣ σ 1 (q ^ a) := by
  obtain ⟨hm, hqa, hao, hfm⟩ := frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
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
  rw [hqa] at hcard
  have : Fact l.Prime := ⟨hl⟩
  simp only [Nat.padicValNat_def] at hcard
  rw [multiplicity_eq_zero_of_not_dvd hla, add_zero] at hcard
  -- some member of `S` does not divide `J`
  obtain ⟨p, hpS, hpJ⟩ : ∃ p ∈ congrPrimes N q l, p ∉ (eulerIndex q a m).primeFactors := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card (show congrPrimes N q l ⊆ (eulerIndex q a m).primeFactors from
      fun p hp => hcon p hp)
    omega
  obtain ⟨hpN, hpq, -⟩ := Finset.mem_filter.mp hpS
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hJ0 : eulerIndex q a m ≠ 0 := by
    have := three_le_eulerIndex h hq hN hqm
    omega
  have hpJ' : ¬ p ∣ eulerIndex q a m := fun hd =>
    hpJ (Nat.mem_primeFactors.mpr ⟨hpp, hd, hJ0⟩)
  have hpm : p ^ (l - 1) ∣ m ^ 2 := by
    have he : (m ^ 2).factorization p = l - 1 := by rw [← hfm p hpq, hexp p hpN hpq]
    exact he ▸ Nat.ordProj_dvd (m ^ 2) p
  have hdiv : p ^ (l - 1) ∣ σ 1 (q ^ a) * eulerIndex q a m := by
    rw [sigma_special_mul_eulerIndex h hq hN hqm]
    exact hpm.mul_left 2
  refine ⟨p, hpp, two_mul_add_one_le h hl hl2 hpS, ?_⟩
  exact Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpJ')) hdiv

/-- Equal exponents, small Euler index, size of the special prime. Under the hypotheses of
`exists_congrPrime_pow_dvd_sigma_special`, if `a ≤ A` and
`∑_{j ≤ A} B ^ j < (2 l + 1) ^ (l - 1)`, then `B < q`. Restricted result for the family where
all ordinary exponents equal `l - 1`: when the Euler index has fewer than `l - 1` prime
factors, the special prime is large; nothing is excluded. Restricted result; no published
source was checked; novelty not verified. -/
theorem special_gt_of_small_eulerIndex {N q a m l A B : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hla : ¬ l ∣ a + 1) (hJ : (eulerIndex q a m).primeFactors.card < l - 1) (haA : a ≤ A)
    (hB : ∑ j ∈ Finset.range (A + 1), B ^ j < (2 * l + 1) ^ (l - 1)) : B < q := by
  obtain ⟨p, -, hp, hdvd⟩ :=
    exists_congrPrime_pow_dvd_sigma_special h hq hN hqm hl hl2 hexp hla hJ
  by_contra hqB
  push Not at hqB
  have hσ0 : 0 < σ 1 (q ^ a) := sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)
  have h1 : (2 * l + 1) ^ (l - 1) ≤ p ^ (l - 1) := Nat.pow_le_pow_left hp _
  have h2 : p ^ (l - 1) ≤ σ 1 (q ^ a) := Nat.le_of_dvd hσ0 hdvd
  have h3 : σ 1 (q ^ a) ≤ ∑ j ∈ Finset.range (A + 1), B ^ j := by
    rw [sigma_one_apply_prime_pow hq]
    calc ∑ j ∈ Finset.range (a + 1), q ^ j
        ≤ ∑ j ∈ Finset.range (a + 1), B ^ j :=
          Finset.sum_le_sum fun j _ => Nat.pow_le_pow_left hqB j
      _ ≤ ∑ j ∈ Finset.range (A + 1), B ^ j :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
  omega

end OddPerfect

#print axioms OddPerfect.exists_congrPrime_pow_dvd_sigma_special
#print axioms OddPerfect.special_gt_of_small_eulerIndex
