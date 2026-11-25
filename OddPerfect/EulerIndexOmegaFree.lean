import OddPerfect.EulerIndexOmega
import OddPerfect.OddValuationCountFree

/-!
# More primes of odd valuation in the Euler index

Let `N = q ^ a * m ^ 2` be an odd perfect number in Euler's form, with `q` the special prime and
`q ∤ m`, let `J = eulerIndex q a m` and `L = (a + 1) / 2`. Since `J σ(q ^ a) / 2 = m ^ 2`, the
primes of odd valuation in `J` are those of `σ(q ^ a) / 2`, so
`OddPerfect.cardFactors_add_free_le_card_odd_valuation_half_sigma` gives at least
`Ω(L) + Ω_free(L)` primes of odd valuation in `J`, where `Ω_free(L)` counts with multiplicity
the prime factors of `L` that do not divide `q ^ 2 - 1`. The hypotheses `hpos` and `hneg` of
that theorem are discharged as in `OddPerfect.EulerIndexOmega`, by
`OddPerfect.geom_sum_prime_pow_ne_sq` and `OddPerfect.alternating_sum_prime_pow_ne_sq`.

This strengthens `OddPerfect.cardFactors_half_succ_le_card_odd_valuation_eulerIndex`. For
`a = 1` the bound is empty. Published context: Y. Hirakawa (2024) proves that two primes have
odd valuation in the Euler index for a special exponent above one. The novelty of the count is
not verified. The odd perfect number conjecture stays open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N q a m : ℕ}

/-- The special prime is `1 (mod 4)` and so is its exponent. -/
private lemma eiof_special_facts (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) : q % 4 = 1 ∧ a % 4 = 1 := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : N.factorization q = a := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have ha : Odd a := by
    rcases Nat.even_or_odd a with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  have h4 := special_mod_four h hq (hfac ▸ ha)
  rwa [hfac] at h4

/-- A prime of odd valuation is a prime factor. -/
private lemma eiof_mem_of_odd {n t : ℕ} (ho : Odd (n.factorization t)) :
    t ∈ n.primeFactors := by
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  intro h0
  rw [h0] at ho
  exact Nat.not_odd_zero ho

/-- If `J H = M ^ 2`, then `J` and `H` have the same primes of odd valuation. -/
private lemma eiof_odd_iff {J H M t : ℕ} (hJ : J ≠ 0) (hH : H ≠ 0) (he : J * H = M ^ 2) :
    Odd (J.factorization t) ↔ Odd (H.factorization t) := by
  have h2 := congrArg (fun n => n.factorization t) he
  simp only [Nat.factorization_mul hJ hH, Nat.factorization_pow, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul] at h2
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

/-- For every odd perfect number `q ^ a * m ^ 2` with special prime `q` and `q ∤ m`, put
`L = (a + 1) / 2`. Then at least `Ω(L) + Ω_free(L)` primes have odd valuation in the Euler
index, where `Ω(L)` counts the prime factors of `L` with multiplicity and `Ω_free(L)` counts,
with multiplicity, those that do not divide `q ^ 2 - 1`. The bound is empty for `a = 1`.
Published context: Y. Hirakawa (2024) proves two odd valuations for `a > 1`; the novelty of
this count is not verified. -/
theorem cardFactors_add_free_le_card_odd_valuation_eulerIndex (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) :
    ArithmeticFunction.cardFactors ((a + 1) / 2) +
        ∑ p ∈ ((a + 1) / 2).primeFactors.filter (fun p => ¬ p ∣ q ^ 2 - 1),
          ((a + 1) / 2).factorization p ≤
      ((eulerIndex q a m).primeFactors.filter
        fun t => Odd ((eulerIndex q a m).factorization t)).card := by
  obtain ⟨hq4, ha4⟩ := eiof_special_facts h hq hN hqm
  have hq5 : 5 ≤ q := by
    have h2 := hq.two_le
    omega
  have hL : Odd ((a + 1) / 2) := ⟨a / 4, by omega⟩
  have hmain := cardFactors_add_free_le_card_odd_valuation_half_sigma hq hq4 hL
    (fun _ _ _ hh hn hn3 => geom_sum_prime_pow_ne_sq hq hq5 hh hn hn3)
    (fun _ _ _ hh hu hn hn3 => alternating_sum_prime_pow_ne_sq hq hq5 hh hu hn hn3)
  rw [show 2 * ((a + 1) / 2) - 1 = a by omega] at hmain
  have hJ3 := three_le_eulerIndex h hq hN hqm
  have he : eulerIndex q a m * (σ 1 (q ^ a) / 2) = m ^ 2 := by
    rw [sigma_special_div_two h hq hN hqm, mul_comm]
    exact Nat.div_mul_cancel (eulerIndex_dvd_sq h hq hN hqm)
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hm2 : 0 < m ^ 2 := pow_pos (Nat.pos_of_ne_zero hm) 2
  have hH : σ 1 (q ^ a) / 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at he
    omega
  have hJ : eulerIndex q a m ≠ 0 := by omega
  refine hmain.trans (le_of_eq (congrArg Finset.card ?_))
  ext t
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨-, ho⟩
    have ho' := (eiof_odd_iff hJ hH he).mpr ho
    exact ⟨eiof_mem_of_odd ho', ho'⟩
  · rintro ⟨-, ho⟩
    have ho' := (eiof_odd_iff hJ hH he).mp ho
    exact ⟨eiof_mem_of_odd ho', ho'⟩

end OddPerfect

#print axioms OddPerfect.cardFactors_add_free_le_card_odd_valuation_eulerIndex
