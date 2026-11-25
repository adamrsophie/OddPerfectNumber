import OddPerfect.EulerIndexSupport
import OddPerfect.OddValuationCount

/-!
# Primes of odd valuation in the Euler index, counted by the special exponent

Let `N = q ^ a * m ^ 2` be an odd perfect number in Euler's form, with `q` the special prime and
`q ∤ m`, and let `J = eulerIndex q a m`. With `L = (a + 1) / 2` and `H = σ(q ^ a) / 2` we have
`J H = m ^ 2`, so `J` and `H` have the same primes of odd valuation. By
`OddPerfect.cardFactors_le_card_odd_valuation_half_sigma`, at least `Ω((a + 1) / 2)` primes
(counted with multiplicity in `(a + 1) / 2`) have odd valuation in `J`, under the two
hypotheses `hpos` and `hneg` of that module, which stay explicit arguments here and are not
proved in this library.

Published context: Y. Hirakawa (2024) proves that two primes have odd valuation in the Euler
index for a special exponent above one. The novelty of the count in this module is not
verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N q a m : ℕ}

/-- The special prime is `1 (mod 4)` and so is its exponent. -/
private lemma eio_special_facts (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
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
private lemma eio_mem_of_odd {n t : ℕ} (ho : Odd (n.factorization t)) : t ∈ n.primeFactors := by
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  intro h0
  rw [h0] at ho
  exact Nat.not_odd_zero ho

/-- If `J H = M ^ 2`, then `J` and `H` have the same primes of odd valuation. -/
private lemma eio_odd_iff {J H M t : ℕ} (hJ : J ≠ 0) (hH : H ≠ 0) (he : J * H = M ^ 2) :
    Odd (J.factorization t) ↔ Odd (H.factorization t) := by
  have h2 := congrArg (fun n => n.factorization t) he
  simp only [Nat.factorization_mul hJ hH, Nat.factorization_pow, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul] at h2
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

/-- For an odd perfect number `q ^ a * m ^ 2` with special prime `q` and `q ∤ m`, under the
hypotheses `hpos` and `hneg` (explicit arguments, not proved here), at least `Ω((a + 1) / 2)`
primes have odd valuation in the Euler index. Published context: Y. Hirakawa (2024) proves two
odd valuations for `a > 1`; the novelty of this count is not verified. -/
theorem cardFactors_le_card_odd_valuation_eulerIndex (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hpos : ∀ h n y : ℕ, Odd h → Odd n → 3 ≤ n → ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2)
    (hneg : ∀ h n y : ℕ, h ≠ 0 → q ^ h % 4 = 1 → Odd n → 3 ≤ n →
      (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2) :
    ArithmeticFunction.cardFactors ((a + 1) / 2) ≤
      ((eulerIndex q a m).primeFactors.filter
        fun t => Odd ((eulerIndex q a m).factorization t)).card := by
  obtain ⟨hq4, ha4⟩ := eio_special_facts h hq hN hqm
  have hL : Odd ((a + 1) / 2) := ⟨a / 4, by omega⟩
  have hmain := cardFactors_le_card_odd_valuation_half_sigma hq hq4 hL hpos hneg
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
    have ho' := (eio_odd_iff hJ hH he).mpr ho
    exact ⟨eio_mem_of_odd ho', ho'⟩
  · rintro ⟨-, ho⟩
    have ho' := (eio_odd_iff hJ hH he).mp ho
    exact ⟨eio_mem_of_odd ho', ho'⟩

/-- Corollary: under the same hypotheses, the Euler index has at least `Ω((a + 1) / 2)`
distinct prime factors. The novelty of this count is not verified. -/
theorem cardFactors_le_card_primeFactors_eulerIndex (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hpos : ∀ h n y : ℕ, Odd h → Odd n → 3 ≤ n → ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2)
    (hneg : ∀ h n y : ℕ, h ≠ 0 → q ^ h % 4 = 1 → Odd n → 3 ≤ n →
      (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2) :
    ArithmeticFunction.cardFactors ((a + 1) / 2) ≤ (eulerIndex q a m).primeFactors.card :=
  (cardFactors_le_card_odd_valuation_eulerIndex h hq hN hqm hpos hneg).trans
    (Finset.card_filter_le _ _)

end OddPerfect

#print axioms OddPerfect.cardFactors_le_card_odd_valuation_eulerIndex
#print axioms OddPerfect.cardFactors_le_card_primeFactors_eulerIndex
