import OddPerfect.ExcessSupportSharp
import OddPerfect.EscapeRowUnique

/-!
# The second support bound with the constant 11

`OddPerfect/ExcessSupportSharp.lean` proves, for an odd perfect number `N` with special prime `q`
of exponent `a` and total excess `T`,
`2 * ω(N) + 3 * v_3(σ(q ^ a)) ≤ 7 * T + 13 + #(rows through q)`, from at most two escape rows.
`OddPerfect/EscapeRowUnique.lean` has since shown that there is at most one escape row. The
same count then gives the constant 11.

The total excess is not bounded and the rows through `q` are not capped here, so this decides
nothing about the existence of odd perfect numbers, which is open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- For every special prime `q` of an odd perfect number `N` with exponent `a`, and `T` the
total excess, `2 * ω(N) + 3 * v_3(σ(q ^ a)) ≤ 7 * T + 11 + #(rows through q)`. -/
theorem two_mul_card_primeFactors_add_three_mul_le_eleven {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    2 * N.primeFactors.card + 3 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      7 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 11 +
        (throughRows N q).card := by
  have hD := card_primeFactors_le_split h hq hodd
  have hK := two_mul_card_squarePrimes_le (q := q) h
  have hI := card_freeRows_le (N := N) (q := q) h
  have hP := receivers_add_le h hq hodd
  have hB := card_squarePrimes_one_add_le h hq hodd
  have hE := card_escapeRows_le_one_all h hq hodd
  have h3q : (3 : ℕ) ≠ q := by
    rintro rfl
    have := (special_mod_four h hq hodd).1
    omega
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd Nat.prime_three h3q
  split_ifs at hP <;> omega

/-- For every special prime, `2 * ω(N) ≤ 7 * T + 11 + #(rows through q)`. -/
theorem two_mul_card_primeFactors_le_seven_excess_add_eleven {N q : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    2 * N.primeFactors.card ≤
      7 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 11 +
        (throughRows N q).card := by
  have := two_mul_card_primeFactors_add_three_mul_le_eleven h hq hodd
  omega

end OddPerfect

#print axioms OddPerfect.two_mul_card_primeFactors_add_three_mul_le_eleven
#print axioms OddPerfect.two_mul_card_primeFactors_le_seven_excess_add_eleven
