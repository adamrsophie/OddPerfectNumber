import OddPerfect.SignedRepunit
import OddPerfect.EulerIndexOmegaOf

/-!
# Primes of odd valuation in the Euler index, without extra hypotheses

Let `N = q ^ a * m ^ 2` be an odd perfect number in Euler's form, with `q` the special prime and
`q ∤ m`, and let `J = eulerIndex q a m`. This module removes the two explicit hypotheses of
`OddPerfect.cardFactors_le_card_odd_valuation_eulerIndex` using
`OddPerfect.geom_sum_prime_pow_ne_sq` and `OddPerfect.alternating_sum_prime_pow_ne_sq`, which
are reported to be special cases of Ljunggren's theorem (the alternating case, a negative base,
was not page checked). So for every odd perfect number in Euler form, with no
restriction on `q` or `a`, at least `Ω((a + 1) / 2)` primes (counted with multiplicity in
`(a + 1) / 2`) have odd valuation in `J`.

Scope. For `a = 1` the bound is empty, since `Ω(1) = 0`. When `(a + 1) / 2` is prime it gives
one prime, which is weaker than the published two odd valuations (Y. Hirakawa, 2024) and than
the landed conditional results. It is stronger than those only when `(a + 1) / 2` has at least
three prime factors counted with multiplicity. The novelty of the count is not verified. The
odd perfect number conjecture stays open.
-/

namespace OddPerfect

variable {N q a m : ℕ}

/-- The special prime is `1 (mod 4)`. -/
private lemma eiom_special_mod_four (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) : q % 4 = 1 := by
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
  exact (special_mod_four h hq (hfac ▸ ha)).1

/-- For every odd perfect number `q ^ a * m ^ 2` with special prime `q` and `q ∤ m`, at least
`Ω((a + 1) / 2)` primes have odd valuation in the Euler index. The bound is empty for `a = 1`
and gives one prime when `(a + 1) / 2` is prime, weaker there than the published two odd
valuations (Y. Hirakawa, 2024); it is stronger only when `(a + 1) / 2` has at least three prime
factors counted with multiplicity. Novelty of the count not verified. -/
theorem cardFactors_half_succ_le_card_odd_valuation_eulerIndex (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) :
    ArithmeticFunction.cardFactors ((a + 1) / 2) ≤
      ((eulerIndex q a m).primeFactors.filter
        fun t => Odd ((eulerIndex q a m).factorization t)).card := by
  have hq5 : 5 ≤ q := by
    have h4 := eiom_special_mod_four h hq hN hqm
    have h2 := hq.two_le
    omega
  exact cardFactors_le_card_odd_valuation_eulerIndex h hq hN hqm
    (fun _ _ _ hh hn hn3 => geom_sum_prime_pow_ne_sq hq hq5 hh hn hn3)
    (fun _ _ _ hh hu hn hn3 => alternating_sum_prime_pow_ne_sq hq hq5 hh hu hn hn3)

/-- For every odd perfect number `q ^ a * m ^ 2` with special prime `q` and `q ∤ m`, the Euler
index has at least `Ω((a + 1) / 2)` distinct prime factors. Novelty of the count not
verified. -/
theorem cardFactors_half_succ_le_card_primeFactors_eulerIndex (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) :
    ArithmeticFunction.cardFactors ((a + 1) / 2) ≤ (eulerIndex q a m).primeFactors.card :=
  (cardFactors_half_succ_le_card_odd_valuation_eulerIndex h hq hN hqm).trans
    (Finset.card_filter_le _ _)

/-- If the Euler index of an odd perfect number `q ^ a * m ^ 2` (special prime `q`, `q ∤ m`) has
exactly two distinct prime factors, then `(a + 1) / 2` has at most two prime factors counted
with multiplicity. Novelty not verified. -/
theorem cardFactors_half_succ_le_two_of_eulerIndex_pair (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hJ : (eulerIndex q a m).primeFactors.card = 2) :
    ArithmeticFunction.cardFactors ((a + 1) / 2) ≤ 2 :=
  hJ ▸ cardFactors_half_succ_le_card_primeFactors_eulerIndex h hq hN hqm

end OddPerfect

#print axioms OddPerfect.cardFactors_half_succ_le_card_odd_valuation_eulerIndex
#print axioms OddPerfect.cardFactors_half_succ_le_card_primeFactors_eulerIndex
#print axioms OddPerfect.cardFactors_half_succ_le_two_of_eulerIndex_pair
