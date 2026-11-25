import OddPerfect.LargestPrimeSignedMore

/-!
# Exponent parity sharpens the capacity bounds of the largest prime

By Euler (`exists_special_prime`), every prime factor of an odd perfect number `N` has an even
exponent except the special prime, whose exponent is `1` modulo `4`. So no exponent of `N` is
`3` modulo `4`, and a bound `v_P(N) ≤ c` with `c ≡ 3 (mod 4)` improves to `v_P(N) ≤ c - 1`.

* `factorization_mod_four_ne_three`: `v_p(N) % 4 ≠ 3` for every `p`.
* `factorization_le_pred_of_mod_four_eq_three`: `v_p(N) ≤ c` and `c ≡ 3 (mod 4)` give
  `v_p(N) ≤ c - 1`.
* Applied to the landed signed capacity bounds for the largest prime factor `P`, with odd part
  `m` of `P - 1`: `v_P(N) ≤ 10, 18, 22, 34, 46` for `m = 7, 11, 15, 21, 25` (the landed bounds
  are `11, 19, 23, 35, 47`).

These hold for every odd perfect number whose largest prime factor `P` has the stated odd part
of `P - 1`. The odd part is not bounded by these results, and nothing is excluded. Novelty was
not verified.
-/

namespace OddPerfect

variable {N : ℕ}

/-- No exponent of an odd perfect number is `3` modulo `4`: the special prime has exponent
`1` modulo `4`, every other prime has an even exponent, and a nonprime has exponent `0`. -/
theorem factorization_mod_four_ne_three (h : OddPerfect N) (p : ℕ) :
    N.factorization p % 4 ≠ 3 := by
  obtain ⟨q, -, -, -, hq4, hev⟩ := exists_special_prime h
  by_cases hpq : p = q
  · subst hpq; omega
  by_cases hp : p.Prime
  · obtain ⟨k, hk⟩ := hev p hp hpq
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime N hp]; omega

/-- A bound `v_p(N) ≤ c` with `c ≡ 3 (mod 4)` improves by one for an odd perfect number. -/
theorem factorization_le_pred_of_mod_four_eq_three (h : OddPerfect N) {p c : ℕ}
    (he : N.factorization p ≤ c) (hc : c % 4 = 3) : N.factorization p ≤ c - 1 := by
  have := factorization_mod_four_ne_three h p
  omega

/-- If the odd part of `P - 1` is `7`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 10`. -/
theorem factorization_largest_le_ten_of_odd_part_seven (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 7) : N.factorization P ≤ 10 :=
  factorization_le_pred_of_mod_four_eq_three h
    (factorization_largest_le_eleven_of_odd_part_seven h hP hmax hm) (by decide)

/-- If the odd part of `P - 1` is `11`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 18`. -/
theorem factorization_largest_le_eighteen_of_odd_part_eleven (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 11) : N.factorization P ≤ 18 :=
  factorization_le_pred_of_mod_four_eq_three h
    (factorization_largest_le_nineteen_of_odd_part_eleven h hP hmax hm) (by decide)

/-- If the odd part of `P - 1` is `15`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 22`. -/
theorem factorization_largest_le_twentytwo_of_odd_part_fifteen (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 15) : N.factorization P ≤ 22 :=
  factorization_le_pred_of_mod_four_eq_three h
    (factorization_largest_le_twentythree_of_odd_part_fifteen h hP hmax hm) (by decide)

/-- If the odd part of `P - 1` is `21`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 34`. -/
theorem factorization_largest_le_thirtyfour_of_odd_part_twentyone (h : OddPerfect N)
    {P a : ℕ} (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 21) : N.factorization P ≤ 34 :=
  factorization_le_pred_of_mod_four_eq_three h
    (factorization_largest_le_thirtyfive_of_odd_part_twentyone h hP hmax hm) (by decide)

/-- If the odd part of `P - 1` is `25`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 46`. -/
theorem factorization_largest_le_fortysix_of_odd_part_twentyfive (h : OddPerfect N)
    {P a : ℕ} (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 25) : N.factorization P ≤ 46 :=
  factorization_le_pred_of_mod_four_eq_three h
    (factorization_largest_le_fortyseven_of_odd_part_twentyfive h hP hmax hm) (by decide)

end OddPerfect

#print axioms OddPerfect.factorization_mod_four_ne_three
#print axioms OddPerfect.factorization_le_pred_of_mod_four_eq_three
#print axioms OddPerfect.factorization_largest_le_ten_of_odd_part_seven
#print axioms OddPerfect.factorization_largest_le_eighteen_of_odd_part_eleven
#print axioms OddPerfect.factorization_largest_le_twentytwo_of_odd_part_fifteen
#print axioms OddPerfect.factorization_largest_le_thirtyfour_of_odd_part_twentyone
#print axioms OddPerfect.factorization_largest_le_fortysix_of_odd_part_twentyfive
