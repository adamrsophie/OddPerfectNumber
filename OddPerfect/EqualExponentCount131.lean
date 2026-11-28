import OddPerfect.EqualExponentCount
import OddPerfect.EqualExponentCount131Data

/-!
# Equal exponents `130`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 131` has a main case and 13 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 17293` for `l = 131` is accepted. -/
theorem case131_7_ok : checkCase 131 pc131 (some 17293) [] case131_7 = true := by
  decide +kernel

/-- The case `q = 6032828370809` for `l = 131` is accepted. -/
theorem case131_8_ok : checkCase 131 pc131 (some 6032828370809) [] case131_8 = true := by
  decide +kernel

/-- The case `q = 315449` for `l = 131` is accepted. -/
theorem case131_9_ok : checkCase 131 pc131 (some 315449) [] case131_9 = true := by
  decide +kernel

/-- The case `q = 184637689` for `l = 131` is accepted. -/
theorem case131_10_ok : checkCase 131 pc131 (some 184637689) [] case131_10 = true := by
  decide +kernel

/-- The case `q = 193357` for `l = 131` is accepted. -/
theorem case131_11_ok : checkCase 131 pc131 (some 193357) [] case131_11 = true := by
  decide +kernel

/-- The case `q = 667577` for `l = 131` is accepted. -/
theorem case131_12_ok : checkCase 131 pc131 (some 667577) [] case131_12 = true := by
  decide +kernel

/-- The certificate for `l = 131` is accepted. -/
theorem check131 : checkCert 131 pc131 main131 cases131 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc131_ok main131_ok fun c hc => ?_
  simp only [cases131, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [case131_0_ok,
    case131_1_ok,
    case131_2_ok,
    case131_3_ok,
    case131_4_ok,
    case131_5_ok,
    case131_6_ok,
    case131_7_ok,
    case131_8_ok,
    case131_9_ok,
    case131_10_ok,
    case131_11_ok,
    case131_12_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `130`. -/
theorem not_all_exponents_eq_one_hundred_thirty {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 130) : False :=
  EqCount.checkCert_sound_of_mod_four EqCount.check131 (by norm_num) h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case131_7_ok
#print axioms OddPerfect.EqCount.case131_8_ok
#print axioms OddPerfect.EqCount.case131_9_ok
#print axioms OddPerfect.EqCount.case131_10_ok
#print axioms OddPerfect.EqCount.case131_11_ok
#print axioms OddPerfect.EqCount.case131_12_ok
#print axioms OddPerfect.EqCount.check131
#print axioms OddPerfect.not_all_exponents_eq_one_hundred_thirty
