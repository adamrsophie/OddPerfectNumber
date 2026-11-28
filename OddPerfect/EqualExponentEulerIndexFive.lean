import OddPerfect.EqualExponentRowBudget
import OddPerfect.EqualExponentEulerIndex

/-!
# Six prime factors of the Euler index at special exponent at most five

Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, `a ≤ 5`, and
suppose every ordinary exponent equals `l - 1` for an odd prime `l`. Then the Euler index
`eulerIndex q a m` has at least six prime factors
(`six_le_card_primeFactors_eulerIndex_of_special_le_five`). This closes the case `l = 131`
left open by `six_le_card_primeFactors_eulerIndex_or_eq_of_special_le_five`: there the special
exponent is `1` or `5`, and `index_le_of_special_eq_five` excludes `a = 5`.

This is a restricted result for the family where all ordinary exponents equal `l - 1`. The
family is not excluded; the number of prime factors of the Euler index is not bounded, and `l`
is bounded only through it. The odd perfect number conjecture remains open. Restricted result;
no published source was checked; novelty not verified.
-/

namespace OddPerfect

/-- For special exponent `a ≤ 5` and equal ordinary exponents `l - 1` (`l` an odd prime), the
Euler index has at least six prime factors. Restricted result: the family is not excluded.
Restricted result; no published source was checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_of_special_le_five {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 5)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card := by
  rcases six_le_card_primeFactors_eulerIndex_or_eq_of_special_le_five h hq hN hqm ha hl hl2
    hexp with hk | hl131
  · exact hk
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hqa : N.factorization q = a := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd)), add_zero]
  have hodd : Odd (N.factorization q) := by
    rcases Nat.even_or_odd (N.factorization q) with ⟨j, hj⟩ | ho
    · rw [hqa] at hj
      exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  have ha4 := (special_mod_four h hq hodd).2
  rw [hqa] at ha4
  rcases (by omega : a = 1 ∨ a = 5) with rfl | rfl
  · exact six_le_card_primeFactors_eulerIndex_of_equal_exponents h hq
      (by rw [hN, pow_one]) hqm hl hl2 hexp
  · by_contra hk
    have := index_le_of_special_eq_five h hq hN hqm hl (by omega) hexp (by omega)
    omega

end OddPerfect

#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_of_special_le_five
