import OddPerfect.EqualExponentCountGeneral
import OddPerfect.EqualExponentCount113Data

/-!
# Equal exponents `112`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 113` has a main case and no case `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The certificate for `l = 113` is accepted. -/
theorem check113 : checkCert 113 pc113 main113 cases113 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc113_ok main113_ok fun c hc => ?_
  simp [cases113] at hc

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `112`. -/
theorem not_all_exponents_eq_one_hundred_twelve {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 112) : False :=
  EqCount.checkCert_sound EqCount.check113 h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.check113
#print axioms OddPerfect.not_all_exponents_eq_one_hundred_twelve
