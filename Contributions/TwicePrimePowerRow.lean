import OddPerfect.Steps
import OddPerfect.Zsigmondy
import OddPerfect.Seed.Example

/-!
Proof of the step `TwicePrimePowerRow`: if `σ(q ^ k) = 2 * p ^ s` with `p` an odd prime, then
`k = 1` and `2 * p ≤ q + 1`. The index `k + 1` is even, so `q + 1` divides the divisor sum and
`p ∣ q + 1`; for `k > 1` a prime divisor for which `q` has order `k + 1 ≥ 3` must be `p`, but
`q ≡ -1 (mod p)` has order at most 2.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.Proofs

theorem TwicePrimePowerRow : OddPerfect.Steps.TwicePrimePowerRow := by
  intro p q k s hp hp2 hq hk hrow
  have h2s : 2 ∣ σ 1 (q ^ k) := hrow ▸ dvd_mul_right 2 _
  obtain ⟨h2q, hlen⟩ := prime_dvd_sigma_prime_pow hq Nat.prime_two h2s
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd : 2 ∣ k + 1 := by
    rcases hlen with ⟨-, h⟩ | ⟨hlt, -, h⟩
    · exact h
    · have := Nat.dvd_one.mp h
      omega
  have hdiv := OPNExample.sigma_prime_pow_dvd hq (show 1 + 1 ∣ k + 1 from hd)
  have hrow1 : σ 1 (q ^ 1) = q + 1 := by
    rw [sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ, add_comm]
  rw [hrow1, hrow] at hdiv
  have hqodd := Nat.odd_iff.mp (hq.odd_of_ne_two h2q.symm)
  have hdhalf : (q + 1) / 2 ∣ p ^ s := by
    apply Nat.dvd_of_mul_dvd_mul_left two_pos
    simpa only [show 2 * ((q + 1) / 2) = q + 1 by omega] using hdiv
  obtain ⟨t, ht, htd⟩ := Nat.exists_prime_and_dvd (show (q + 1) / 2 ≠ 1 by omega)
  have heqt := (Nat.prime_dvd_prime_iff_eq ht hp).mp (ht.dvd_of_dvd_pow (htd.trans hdhalf))
  subst t
  have hpd : p ∣ q + 1 := htd.trans ⟨2, by omega⟩
  have hsize := Nat.le_of_dvd (show 0 < (q + 1) / 2 by omega) htd
  refine ⟨?_, by omega⟩
  by_contra hk1
  obtain ⟨r, hr, hrdiv, hord, hmod⟩ :=
    exists_prime_dvd_sigma_orderOf_eq hq hq3 (show 3 ≤ k + 1 by omega) (dvd_refl _)
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [Nat.mod_eq_of_lt (by omega : 2 < k + 1)] at hmod
    omega
  rw [hrow] at hrdiv
  have hrp : r ∣ p ^ s := (hr.dvd_mul.mp hrdiv).resolve_left
    fun hh => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hh)
  have heqr := (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hrp)
  subst r
  have hz := (ZMod.natCast_eq_zero_iff (q + 1) p).mpr hpd
  have hm : (q : ZMod p) = -1 := by push_cast at hz; linear_combination hz
  have hpow : (q : ZMod p) ^ 2 = 1 := by rw [hm]; ring
  have hle := Nat.le_of_dvd (by decide : 0 < 2) (orderOf_dvd_of_pow_eq_one hpow)
  rw [hord] at hle
  omega

end OddPerfect.Proofs
