import OddPerfect.EqualExponentCount
import OddPerfect.EqualExponentCount103Data

/-!
# Equal exponents `102`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 103` has a main case and 4 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 16069` for `l = 103` is accepted. -/
theorem case103_2_ok : checkCase 103 pc103 (some 16069) [] case103_2 = true := by
  decide +kernel

/-- The case `q = 224129` for `l = 103` is accepted. -/
theorem case103_3_ok : checkCase 103 pc103 (some 224129) [] case103_3 = true := by
  decide +kernel

/-- The certificate for `l = 103` is accepted. -/
theorem check103 : checkCert 103 pc103 main103 cases103 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc103_ok main103_ok fun c hc => ?_
  simp only [cases103, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  exacts [case103_0_ok,
    case103_1_ok,
    case103_2_ok,
    case103_3_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `102`. -/
theorem not_all_exponents_eq_one_hundred_two {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 102) : False :=
  EqCount.checkCert_sound_of_mod_four EqCount.check103 (by norm_num) h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case103_2_ok
#print axioms OddPerfect.EqCount.case103_3_ok
#print axioms OddPerfect.EqCount.check103
#print axioms OddPerfect.not_all_exponents_eq_one_hundred_two
