import OddPerfect.EqualExponentCount
import OddPerfect.EqualExponentCount79Data

/-!
# Equal exponents `78`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 79` has a main case and 4 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 14221` for `l = 79` is accepted. -/
theorem case79_2_ok : checkCase 79 pc79 (some 14221) [] case79_2 = true := by
  decide +kernel

/-- The case `q = 213077537` for `l = 79` is accepted. -/
theorem case79_3_ok : checkCase 79 pc79 (some 213077537) [] case79_3 = true := by
  decide +kernel

/-- The certificate for `l = 79` is accepted. -/
theorem check79 : checkCert 79 pc79 main79 cases79 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc79_ok main79_ok fun c hc => ?_
  simp only [cases79, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  exacts [case79_0_ok,
    case79_1_ok,
    case79_2_ok,
    case79_3_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `78`. -/
theorem not_all_exponents_eq_seventy_eight {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 78) : False :=
  EqCount.checkCert_sound_of_mod_four EqCount.check79 (by norm_num) h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case79_2_ok
#print axioms OddPerfect.EqCount.case79_3_ok
#print axioms OddPerfect.EqCount.check79
#print axioms OddPerfect.not_all_exponents_eq_seventy_eight
