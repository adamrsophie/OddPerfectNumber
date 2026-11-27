import OddPerfect.EulerIndexPairSmallCap
import OddPerfect.EulerIndexPairExponentTwelve

/-!
# Ordinary exponents at most 10: the Euler index has at least three prime factors

Restricted result; no published source was checked; novelty not verified.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and let every other prime factor of `N` have exponent at most `10`.

* `three_le_card_primeFactors_eulerIndex_of_exponent_le_ten`: the Euler index
  `J = σ(m ^ 2) / q` has at least three distinct prime factors. It has at least two
  (`two_le_card_primeFactors_eulerIndex_of_exponent_one`); if it had exactly two, the emitter
  `t` would be a prime factor of `N` other than `q` with exponent at least `12`
  (`eulerIndex_pair_exponent_twelve`). The cap 8 statement
  `three_le_card_primeFactors_eulerIndex_of_exponent_le_eight` is a special case.

This excludes only the support size two of the Euler index under the cap; the family itself
is not excluded. The odd perfect number conjecture is open, and nothing here decides it.
-/

namespace OddPerfect

/-- In the family with special exponent 1 and ordinary exponents at most `10`, the Euler index
has at least three distinct prime factors. The cap 8 theorem is a special case. Restricted
family result; no published source was checked; novelty not verified. -/
theorem three_le_card_primeFactors_eulerIndex_of_exponent_le_ten {N q m : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p ≤ 10) :
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
  obtain ⟨t, u, htu, -, -, h12⟩ :=
    eulerIndex_pair_exponent_twelve h hq hN hqm (Nat.prime_of_mem_primeFactors hrJ)
      (Nat.prime_of_mem_primeFactors hsJ) hrs hJ
  have htJ : t ∈ (eulerIndex q 1 m).primeFactors := by
    rw [hJ, ← htu]; simp
  have := hexp t (key t htJ).1 (key t htJ).2
  omega

end OddPerfect

#print axioms OddPerfect.three_le_card_primeFactors_eulerIndex_of_exponent_le_ten
