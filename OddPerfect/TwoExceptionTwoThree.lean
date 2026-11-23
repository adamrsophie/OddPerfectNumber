import OddPerfect.TwoExceptionTwo

/-!
# Two exceptional primes: one of them is 3

Let `N` be an odd perfect number with special prime `q` in which every prime factor other than
`q`, `r₁` and `r₂` has exponent exactly 2. Then `r₁ = 3` or `r₂ = 3`
(`two_exceptions_three_exceptional`): the prime 3 divides `N` (`three_dvd_of_two_exceptions`),
it is not the special prime, and its exponent is at least 6 (`two_exceptions_six_le_three`), so
it cannot be one of the primes of exponent 2.

For a single exceptional prime the corresponding statement is `restrained_exception_eq_three`.
This concerns only this restricted family, not odd perfect numbers in general. Whether the
statement is new was not verified against the literature.
-/

namespace OddPerfect

/-- With at most two exceptional primes `r₁` and `r₂` (every other prime factor except the
special prime has exponent 2), one of the two is 3. -/
theorem two_exceptions_three_exceptional {N q r₁ r₂ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    r₁ = 3 ∨ r₂ = 3 := by
  by_contra hne
  rw [not_or] at hne
  have h6 := two_exceptions_six_le_three h hq hodd hsq
  have h3 : 3 ∣ N := three_dvd_of_two_exceptions h hq hodd hsq
  have hq3 : (3 : ℕ) ≠ q := by
    rintro rfl
    have := (special_mod_four h hq hodd).1
    omega
  have hm : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have := hsq 3 hm hq3 (Ne.symm hne.1) (Ne.symm hne.2)
  omega

end OddPerfect

#print axioms OddPerfect.two_exceptions_three_exceptional
