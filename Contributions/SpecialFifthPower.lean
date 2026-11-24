import OddPerfect.Steps
import OddPerfect.SpecialPrime
import OddPerfect.ClosedLoop

/-!
Proof of the step `SpecialFifthPower`: in Euler's form `N = q ^ k * m ^ 2` with `q ∤ m`, a
special exponent `k ≠ 1` forces `q ^ 5 < 2 * m ^ 2`. The exponent `k` is odd (otherwise `N` is
a square) and `k % 4 = 1` by Euler, so `k ≥ 5`; the Dris type inequality
`3 σ(q ^ k) ≤ 2 m ^ 2` and `q ^ k < σ(q ^ k)` then give the bound.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.Proofs

theorem SpecialFifthPower : OddPerfect.Steps.SpecialFifthPower := by
  intro N q k m h hq hN hqm hk1
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : N.factorization q = k := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have hk : Odd k := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (OddPerfect.not_isSquare h)
    · exact ho
  have h4 := OddPerfect.special_mod_four h hq (hfac ▸ hk)
  rw [hfac] at h4
  have hk5 : 5 ≤ k := by omega
  have hpow := OddPerfect.special_pow_lt_sq h hq hN hqm hk
  have hle : q ^ 5 ≤ q ^ k := Nat.pow_le_pow_right hq.pos hk5
  omega

end OddPerfect.Proofs
