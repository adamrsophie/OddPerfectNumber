import OddPerfect.EqualExponentCountGeneral
import OddPerfect.EqualExponentCount109Data

/-!
# Equal exponents `108`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 109` has a main case and 14 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 762578407877147569` for `l = 109` is accepted. -/
theorem case109_7_ok : checkCase 109 pc109 (some 762578407877147569) [] case109_7 = true := by
  decide +kernel

/-- The case `q = 32944814873` for `l = 109` is accepted. -/
theorem case109_8_ok : checkCase 109 pc109 (some 32944814873) [] case109_8 = true := by
  decide +kernel

/-- The case `q = 10552017937` for `l = 109` is accepted. -/
theorem case109_9_ok : checkCase 109 pc109 (some 10552017937) [] case109_9 = true := by
  decide +kernel

/-- The case `q = 297976547596577` for `l = 109` is accepted. -/
theorem case109_10_ok : checkCase 109 pc109 (some 297976547596577) [] case109_10 = true := by
  decide +kernel

/-- The case `q = 6977` for `l = 109` is accepted. -/
theorem case109_11_ok : checkCase 109 pc109 (some 6977) [] case109_11 = true := by
  decide +kernel

/-- The case `q = 2060807952821` for `l = 109` is accepted. -/
theorem case109_12_ok : checkCase 109 pc109 (some 2060807952821) [] case109_12 = true := by
  decide +kernel

/-- The case `q = 18749` for `l = 109` is accepted. -/
theorem case109_13_ok : checkCase 109 pc109 (some 18749) [] case109_13 = true := by
  decide +kernel

/-- The certificate for `l = 109` is accepted. -/
theorem check109 : checkCert 109 pc109 main109 cases109 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc109_ok main109_ok fun c hc => ?_
  simp only [cases109, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [case109_0_ok,
    case109_1_ok,
    case109_2_ok,
    case109_3_ok,
    case109_4_ok,
    case109_5_ok,
    case109_6_ok,
    case109_7_ok,
    case109_8_ok,
    case109_9_ok,
    case109_10_ok,
    case109_11_ok,
    case109_12_ok,
    case109_13_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `108`. -/
theorem not_all_exponents_eq_one_hundred_eight {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 108) : False :=
  EqCount.checkCert_sound EqCount.check109 h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case109_7_ok
#print axioms OddPerfect.EqCount.case109_8_ok
#print axioms OddPerfect.EqCount.case109_9_ok
#print axioms OddPerfect.EqCount.case109_10_ok
#print axioms OddPerfect.EqCount.case109_11_ok
#print axioms OddPerfect.EqCount.case109_12_ok
#print axioms OddPerfect.EqCount.case109_13_ok
#print axioms OddPerfect.EqCount.check109
#print axioms OddPerfect.not_all_exponents_eq_one_hundred_eight
