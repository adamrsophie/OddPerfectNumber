import OddPerfect.Steps
import OddPerfect.Zsigmondy

/-!
Proof of the step `PureRowBase`: if `σ(q ^ k)` is a power of an odd prime `p`, then `p ∤ q - 1`.
For `k ≥ 2` a prime divisor of `σ(q ^ k)` for which `q` has order `k + 1` must be `p`, and
`p ∣ q - 1` would give order 1; `k = 1` is a direct computation.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.Proofs

theorem PureRowBase : OddPerfect.Steps.PureRowBase := by
  intro p q k s hp hp2 hq hk hs hrow hpred
  have hqpos := hq.one_lt
  by_cases hq2 : q = 2
  · subst q
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpred)
  by_cases hk1 : k = 1
  · subst k
    have hd : p ∣ σ 1 (q ^ 1) := hrow ▸ dvd_pow_self p (by omega)
    rw [sigma_one_apply_prime_pow hq] at hd
    have hplus : p ∣ q + 1 := by simpa [Finset.sum_range_succ, add_comm] using hd
    have htwo : p ∣ 2 := by
      simpa only [show q + 1 - (q - 1) = 2 by omega] using Nat.dvd_sub hplus hpred
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp htwo)
  obtain ⟨r, hr, hrdiv, hord, -⟩ :=
    exists_prime_dvd_sigma_orderOf_eq hq (by omega) (show 3 ≤ k + 1 by omega) (dvd_refl _)
  rw [hrow] at hrdiv
  have heq := (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hrdiv)
  subst r
  have hz := (ZMod.natCast_eq_zero_iff (q - 1) p).mpr hpred
  rw [Nat.cast_sub hqpos.le, Nat.cast_one, sub_eq_zero] at hz
  rw [hz, orderOf_one] at hord
  omega

end OddPerfect.Proofs
