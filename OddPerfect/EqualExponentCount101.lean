import OddPerfect.EqualExponentCountGeneral
import OddPerfect.EqualExponentCount101Data

/-!
# Equal exponents `100`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 101` has a main case and 3 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 5657` for `l = 101` is accepted. -/
theorem case101_1_ok : checkCase 101 pc101 (some 5657) [] case101_1 = true := by
  decide +kernel

/-- The case `q = 157561` for `l = 101` is accepted. -/
theorem case101_2_ok : checkCase 101 pc101 (some 157561) [] case101_2 = true := by
  decide +kernel

/-- The certificate for `l = 101` is accepted. -/
theorem check101 : checkCert 101 pc101 main101 cases101 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc101_ok main101_ok fun c hc => ?_
  simp only [cases101, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  exacts [case101_0_ok,
    case101_1_ok,
    case101_2_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `100`. -/
theorem not_all_exponents_eq_one_hundred {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 100) : False :=
  EqCount.checkCert_sound EqCount.check101 h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case101_1_ok
#print axioms OddPerfect.EqCount.case101_2_ok
#print axioms OddPerfect.EqCount.check101
#print axioms OddPerfect.not_all_exponents_eq_one_hundred
