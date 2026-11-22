import OddPerfect.EqualExponentsBound
import OddPerfect.UpperBound

/-!
# Equal ordinary exponents: an explicit upper bound for the number itself

T. Yamada, "Odd perfect numbers of a special form", Colloq. Math. 103 (2005), Theorem 1.1,
part (2): an odd perfect number `N` in which every ordinary exponent equals `2 β` satisfies
`N < 2 ^ (4 ^ (4 β ^ 2 + 2 β + 3))`. It follows from part (1)
(`card_primeFactors_le_of_equal_exponents`) and Nielsen's bound `N < 2 ^ (4 ^ ω(N))`
(`lt_two_pow_four_pow`). So for each `β` only finitely many numbers are candidates. This is
known mathematics; the file only formalizes it.
-/

namespace OddPerfect

/-- Yamada (Colloq. Math. 103 (2005), Theorem 1.1, part (2)): if every prime factor of the odd
perfect number `N` other than the special prime `q` has exponent exactly `2 β`, then
`N < 2 ^ (4 ^ (4 β ^ 2 + 2 β + 3))`. Known mathematics. -/
theorem lt_two_pow_four_pow_of_equal_exponents {N q β : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β) :
    N < 2 ^ (4 ^ (4 * β ^ 2 + 2 * β + 3)) :=
  lt_of_lt_of_le (lt_two_pow_four_pow h)
    (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (card_primeFactors_le_of_equal_exponents h hq hodd hexp)))

/-- For each `β` the odd perfect numbers with all ordinary exponents equal to `2 β` form a
finite set. Known mathematics (a consequence of the explicit bound). -/
theorem finite_setOf_equal_exponents (β : ℕ) :
    {N : ℕ | OddPerfect N ∧ ∃ q, q.Prime ∧ Odd (N.factorization q) ∧
      ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β}.Finite :=
  (Set.finite_lt_nat (2 ^ (4 ^ (4 * β ^ 2 + 2 * β + 3)))).subset
    fun _ ⟨h, _, hq, hodd, hexp⟩ => lt_two_pow_four_pow_of_equal_exponents h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.lt_two_pow_four_pow_of_equal_exponents
#print axioms OddPerfect.finite_setOf_equal_exponents
