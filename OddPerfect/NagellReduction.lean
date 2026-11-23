import OddPerfect.ClassicalInputs
import OddPerfect.Phi3Algebra

/-!
# An elementary reduction of `NagellPrimePower` to prime exponents at least 5

The classical theorem behind `NagellPrimePower` (see `OddPerfect.ClassicalInputs`) is NOT proved
in this library. This module proves only an elementary reduction, in the shape used by a 1943
paper on odd perfect numbers: if `p ^ 2 + p + 1 = r ^ a` with `p`, `r` prime and `a ≥ 2`, pick a
prime `ℓ ∣ a`; then `p ^ 2 + p + 1 = (r ^ (a / ℓ)) ^ ℓ`. The case `ℓ = 2` is impossible because
`p ^ 2 + p + 1` lies strictly between two consecutive squares (`not_isSquare_phi3`), and the case
`ℓ = 3` is impossible for prime `p` (`phi3_ne_cube_of_prime`). So only prime exponents `ℓ ≥ 5`
remain, which is the hypothesis `NagellHighPrimeExponent`.
-/

namespace OddPerfect

/-- The part of the classical theorem that the library does not prove: no prime `p` has
`p ^ 2 + p + 1 = y ^ ℓ` with `ℓ ≥ 5` prime. A hypothesis, not proved here. -/
def NagellHighPrimeExponent : Prop :=
  ∀ p y ℓ : ℕ, p.Prime → ℓ.Prime → 5 ≤ ℓ → p ^ 2 + p + 1 ≠ y ^ ℓ

/-- For a prime `p`, if `p ^ 2 + p + 1` is a perfect `ℓ`th power with `ℓ` prime, then `ℓ ≥ 5`:
it is not a square, and not a cube. An elementary step of the reduction. -/
theorem five_le_of_phi3_eq_prime_pow {p y ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (h : p ^ 2 + p + 1 = y ^ ℓ) : 5 ≤ ℓ := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  interval_cases ℓ
  · exact absurd hℓ Nat.not_prime_zero
  · exact absurd hℓ Nat.not_prime_one
  · exact not_isSquare_phi3 hp.one_lt.le ⟨y, by rw [phi3, h, sq]⟩
  · exact phi3_ne_cube_of_prime hp y h
  · exact absurd hℓ (by norm_num)

/-- The classical hypothesis `NagellPrimePower` follows from its part `NagellHighPrimeExponent`
on prime exponents at least 5. An elementary reduction; the classical theorem itself is not
proved in this library. -/
theorem nagellPrimePower_of_highPrimeExponent (H : NagellHighPrimeExponent) :
    NagellPrimePower := by
  intro p r a hp _hr _ha h
  by_contra hne
  obtain ⟨ℓ, hℓ, m, rfl⟩ := Nat.exists_prime_and_dvd hne
  have h' : p ^ 2 + p + 1 = (r ^ m) ^ ℓ := by rw [h, ← pow_mul, mul_comm]
  exact H p (r ^ m) ℓ hp hℓ (five_le_of_phi3_eq_prime_pow hp hℓ h') h'

/-- Unconditional: for primes `p`, `r`, if `p ^ 2 + p + 1 = r ^ a` then `a = 1`, or every prime
factor of `a` is at least 5 (so `a ≥ 5`, `a` is odd and `3 ∤ a`). This does not prove the
classical theorem, which would give `a = 1`. -/
theorem phi3_prime_pow_exponent {p r a : ℕ} (hp : p.Prime) (_hr : r.Prime)
    (h : p ^ 2 + p + 1 = r ^ a) : a = 1 ∨ (5 ≤ a ∧ ∀ ℓ, ℓ.Prime → ℓ ∣ a → 5 ≤ ℓ) := by
  have hpf : ∀ ℓ, ℓ.Prime → ℓ ∣ a → 5 ≤ ℓ := by
    rintro ℓ hℓ ⟨m, rfl⟩
    exact five_le_of_phi3_eq_prime_pow hp hℓ (y := r ^ m) (by rw [h, ← pow_mul, mul_comm])
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := hp.two_le
    rw [pow_zero] at h
    nlinarith
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  · obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd ha1
    exact Or.inr ⟨(hpf ℓ hℓ hdvd).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hdvd), hpf⟩

end OddPerfect

#print axioms OddPerfect.five_le_of_phi3_eq_prime_pow
#print axioms OddPerfect.nagellPrimePower_of_highPrimeExponent
#print axioms OddPerfect.phi3_prime_pow_exponent
