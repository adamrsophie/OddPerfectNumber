import OddPerfect.EulerIndexPairEmitterSix
import OddPerfect.EulerIndexSupport

/-!
# Exponents 2 or 4 and special exponent 1: the Euler index has at least three prime factors

Restricted result; no published source was checked; novelty not verified.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and let every other prime factor of `N` have exponent `2` or `4`.

* `three_le_card_primeFactors_eulerIndex_of_palette`: the Euler index
  `J = σ(m ^ 2) / q` has at least three distinct prime factors. It has at least two
  (`two_le_card_primeFactors_eulerIndex_of_exponent_one`); if it had exactly two, both would
  be prime factors of `N` other than `q`, with exponent `2` or `4`, against
  `eulerIndex_pair_not_palette`.

The family is not excluded by this. The odd perfect number conjecture is open, and nothing
here decides it.
-/

namespace OddPerfect

variable {N q m : ℕ}

/-- In the family with special exponent 1 and ordinary exponents `2` or `4`, the Euler index
has at least three distinct prime factors. Restricted family result; no published source was
checked; novelty not verified. -/
theorem three_le_card_primeFactors_eulerIndex_of_palette (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    3 ≤ (eulerIndex q 1 m).primeFactors.card := by
  have h2 := two_le_card_primeFactors_eulerIndex_of_exponent_one h hq hN hqm
  by_contra h3
  have hc : (eulerIndex q 1 m).primeFactors.card = 2 := by omega
  obtain ⟨r, s, hrs, hJ⟩ := Finset.card_eq_two.mp hc
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have key : ∀ p ∈ (eulerIndex q 1 m).primeFactors, p ∈ N.primeFactors ∧ p ≠ q := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpm : p ∣ m := hpp.dvd_of_dvd_pow
      ((Nat.dvd_of_mem_primeFactors hp).trans (eulerIndex_dvd_sq h hq hN1 hqm))
    refine ⟨Nat.mem_primeFactors.mpr ⟨hpp, ?_, h.pos.ne'⟩, fun e => hqm (e ▸ hpm)⟩
    rw [hN]
    exact (hpm.trans (dvd_pow_self m two_ne_zero)).mul_left q
  have hrJ : r ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ]; simp
  have hsJ : s ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ]; simp
  exact eulerIndex_pair_not_palette h hq hN hqm (Nat.prime_of_mem_primeFactors hrJ)
    (Nat.prime_of_mem_primeFactors hsJ) hrs hJ
    ⟨hexp r (key r hrJ).1 (key r hrJ).2, hexp s (key s hsJ).1 (key s hsJ).2⟩

end OddPerfect

#print axioms OddPerfect.three_le_card_primeFactors_eulerIndex_of_palette
