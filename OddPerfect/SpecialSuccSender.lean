import OddPerfect.Reciprocity

/-!
# Divisor sums and prime factors of the special prime plus one

Quadratic reciprocity constrains which prime factors of `q + 1` can have an even power
whose divisor sum is divisible by `q`. This excludes factors congruent to `3` modulo `4`
from sending to the special prime of an odd perfect number.

Proof: if `q` divides the divisor sum of an even power of `r`, then `r` is a square modulo `q`
(`legendreSym_eq_one_of_dvd_sigma_even`). As `q` is 1 modulo 4, reciprocity makes `q` a square
modulo `r`; and `q` is `-1` modulo `r`, so `-1` is a square modulo `r`. An elementary remark;
whether it is stated in the literature has not been checked. Note that every prime factor of
`(q + 1) / 2` divides an odd perfect number with special prime `q`.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Let `q` be a prime that is 1 modulo 4 and `r` an odd prime factor of `q + 1`. If `q`
divides the divisor sum of an even power of `r`, then `r` is 1 modulo 4. -/
theorem mod_four_eq_one_of_dvd_succ_of_dvd_sigma_even {q r e : ℕ} (hq : q.Prime)
    (hr : r.Prime) (hq4 : q % 4 = 1) (hr2 : r ≠ 2) (hrq : r ∣ q + 1) (he : Even e)
    (h : q ∣ σ 1 (r ^ e)) : r % 4 = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact r.Prime := ⟨hr⟩
  have hqr : legendreSym r q = 1 := by
    rw [legendreSym.quadratic_reciprocity_one_mod_four hq4 hr2]
    exact legendreSym_eq_one_of_dvd_sigma_even hr he h
  have hz := (ZMod.natCast_eq_zero_iff (q + 1) r).mpr hrq
  push_cast at hz
  have hneg : ((q : ℤ) : ZMod r) = ((-1 : ℤ) : ZMod r) := by
    rw [Int.cast_natCast, Int.cast_neg, Int.cast_one]
    exact eq_neg_of_add_eq_zero_left hz
  have hsym : legendreSym r q = legendreSym r (-1) := by
    rw [legendreSym, legendreSym, hneg]
  have hodd : r % 2 = 1 := (hr.mod_two_eq_one_iff_ne_two).mpr hr2
  by_contra hr4
  have hr3 : r % 4 = 3 := by omega
  rw [hsym, legendreSym.at_neg_one hr2, ZMod.χ₄_nat_three_mod_four hr3] at hqr
  norm_num at hqr

/-- In an odd perfect number with special prime `q`, a prime factor `r` of `q + 1` that is
3 modulo 4 does not send to `q`: `q` does not divide the divisor sum of the component of `r`. -/
theorem not_dvd_sigma_of_dvd_special_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hr4 : r % 4 = 3) (hrq : r ∣ q + 1) :
    ¬ q ∣ σ 1 (r ^ N.factorization r) := by
  intro hdvd
  have hq4 := (special_mod_four h hq hodd).1
  have hrne : r ≠ q := by rintro rfl; omega
  have hr2 : r ≠ 2 := by rintro rfl; omega
  have he := even_factorization_of_ne h hq hodd hr hrne
  have hr1 := mod_four_eq_one_of_dvd_succ_of_dvd_sigma_even hq hr hq4 hr2 hrq he hdvd
  omega

#print axioms mod_four_eq_one_of_dvd_succ_of_dvd_sigma_even
#print axioms not_dvd_sigma_of_dvd_special_succ

end OddPerfect
