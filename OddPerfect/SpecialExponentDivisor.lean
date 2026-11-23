import OddPerfect.Basic
import OddPerfect.SpecialPrime

/-!
# A divisor from the special exponent

If `a + 2` is prime and divides neither `q` nor `q - 1`, it divides the divisor sum of `q ^ a`.
When `a` is the exponent of the special prime `q` of an odd perfect number, the predecessor
condition implies that `(a + 2) ^ 2` divides the number.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Let `q` be a prime, `a` a natural number and `d = a + 2` a prime that divides neither `q`
nor `q - 1`. Then `d` divides the divisor sum of `q ^ a`. -/
theorem add_two_dvd_sigma_prime_pow {q a : ℕ} (hq : q.Prime) (hd : (a + 2).Prime)
    (hdq : a + 2 ≠ q) (hd1 : ¬ (a + 2) ∣ q - 1) : (a + 2) ∣ σ 1 (q ^ a) := by
  have hcop : q.Coprime (a + 2) :=
    (hd.coprime_iff_not_dvd.mpr fun hdiv => hdq ((Nat.prime_dvd_prime_iff_eq hd hq).mp hdiv)).symm
  have hexp : a + 2 - 1 = a + 1 := by omega
  have hpow : (a + 2) ∣ q ^ (a + 1) - 1 := by
    simpa only [hexp] using
      Nat.dvd_of_mod_eq_zero (Nat.pow_card_sub_one_sub_one_mod_card hd hcop)
  have hgeom : σ 1 (q ^ a) * (q - 1) + 1 = q ^ (a + 1) := by
    rw [sigma_one_apply_prime_pow hq]
    simpa only [Nat.sub_add_cancel hq.one_lt.le] using geom_sum_mul_add (q - 1) (a + 1)
  rw [← hgeom, Nat.add_sub_cancel] at hpow
  exact (hd.dvd_mul.mp hpow).resolve_right hd1

/-- Let `a` be the exponent of the special prime `q` of an odd perfect number `N`. If `a + 2` is
a prime that does not divide `q - 1`, then `(a + 2) ^ 2` divides `N`. -/
theorem special_exponent_add_two_sq_dvd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hd : (N.factorization q + 2).Prime)
    (hd1 : ¬ (N.factorization q + 2) ∣ q - 1) : (N.factorization q + 2) ^ 2 ∣ N := by
  obtain ⟨hq4, ha4⟩ := special_mod_four h hq hodd
  have hd4 : (N.factorization q + 2) % 4 = 3 := by omega
  have hdq : N.factorization q + 2 ≠ q := by
    intro heq
    rw [heq, hq4] at hd4
    omega
  have hd2 : N.factorization q + 2 ≠ 2 := by omega
  have hdN : (N.factorization q + 2) ∣ N :=
    OPNStarter.force_prime h.perfect hq rfl hd hd2 (add_two_dvd_sigma_prime_pow hq hd hdq hd1)
  exact sq_dvd_of_ne_special h hq hodd hd hdq hdN

end OddPerfect

#print axioms OddPerfect.add_two_dvd_sigma_prime_pow
#print axioms OddPerfect.special_exponent_add_two_sq_dvd
