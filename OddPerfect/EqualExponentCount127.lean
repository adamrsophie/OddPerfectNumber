import OddPerfect.EqualExponentCount
import OddPerfect.EqualExponentCount127Data

/-!
# Equal exponents `126`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 127` has a main case and 6 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 1320675600886906675359917` for `l = 127` is accepted. -/
theorem case127_2_ok :
    checkCase 127 pc127 (some 1320675600886906675359917) [] case127_2 = true := by
  decide +kernel

/-- The case `q = 35053` for `l = 127` is accepted. -/
theorem case127_3_ok : checkCase 127 pc127 (some 35053) [] case127_3 = true := by
  decide +kernel

/-- The case `q = 922251274621` for `l = 127` is accepted. -/
theorem case127_4_ok : checkCase 127 pc127 (some 922251274621) [] case127_4 = true := by
  decide +kernel

/-- The case `q = 549149` for `l = 127` is accepted. -/
theorem case127_5_ok : checkCase 127 pc127 (some 549149) [] case127_5 = true := by
  decide +kernel

/-- The certificate for `l = 127` is accepted. -/
theorem check127 : checkCert 127 pc127 main127 cases127 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc127_ok main127_ok fun c hc => ?_
  simp only [cases127, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [case127_0_ok,
    case127_1_ok,
    case127_2_ok,
    case127_3_ok,
    case127_4_ok,
    case127_5_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `126`. -/
theorem not_all_exponents_eq_one_hundred_twenty_six {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 126) : False :=
  EqCount.checkCert_sound_of_mod_four EqCount.check127 (by norm_num) h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case127_2_ok
#print axioms OddPerfect.EqCount.case127_3_ok
#print axioms OddPerfect.EqCount.case127_4_ok
#print axioms OddPerfect.EqCount.case127_5_ok
#print axioms OddPerfect.EqCount.check127
#print axioms OddPerfect.not_all_exponents_eq_one_hundred_twenty_six
