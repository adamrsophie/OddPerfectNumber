import OddPerfect.EqualExponentCountGeneral
import OddPerfect.EqualExponentCount89Data

/-!
# Equal exponents `88`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 89` has a main case and 3 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 2900333` for `l = 89` is accepted. -/
theorem case89_2_ok : checkCase 89 pc89 (some 2900333) [] case89_2 = true := by
  decide +kernel

/-- The certificate for `l = 89` is accepted. -/
theorem check89 : checkCert 89 pc89 main89 cases89 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc89_ok main89_ok fun c hc => ?_
  simp only [cases89, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  exacts [case89_0_ok,
    case89_1_ok,
    case89_2_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `88`. -/
theorem not_all_exponents_eq_eighty_eight {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 88) : False :=
  EqCount.checkCert_sound EqCount.check89 h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case89_2_ok
#print axioms OddPerfect.EqCount.check89
#print axioms OddPerfect.not_all_exponents_eq_eighty_eight
