import OddPerfect.EqualExponentCountGeneral
import OddPerfect.EqualExponentCount73Data

/-!
# Equal exponents `72`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 73` has a main case and 7 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 1192167517020392933` for `l = 73` is accepted. -/
theorem case73_3_ok : checkCase 73 pc73 (some 1192167517020392933) [] case73_3 = true := by
  decide +kernel

/-- The case `q = 543997` for `l = 73` is accepted. -/
theorem case73_4_ok : checkCase 73 pc73 (some 543997) [] case73_4 = true := by
  decide +kernel

/-- The case `q = 122446987417` for `l = 73` is accepted. -/
theorem case73_5_ok : checkCase 73 pc73 (some 122446987417) [] case73_5 = true := by
  decide +kernel

/-- The case `q = 119429` for `l = 73` is accepted. -/
theorem case73_6_ok : checkCase 73 pc73 (some 119429) [] case73_6 = true := by
  decide +kernel

/-- The certificate for `l = 73` is accepted. -/
theorem check73 : checkCert 73 pc73 main73 cases73 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc73_ok main73_ok fun c hc => ?_
  simp only [cases73, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [case73_0_ok,
    case73_1_ok,
    case73_2_ok,
    case73_3_ok,
    case73_4_ok,
    case73_5_ok,
    case73_6_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `72`. -/
theorem not_all_exponents_eq_seventy_two {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 72) : False :=
  EqCount.checkCert_sound EqCount.check73 h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case73_3_ok
#print axioms OddPerfect.EqCount.case73_4_ok
#print axioms OddPerfect.EqCount.case73_5_ok
#print axioms OddPerfect.EqCount.case73_6_ok
#print axioms OddPerfect.EqCount.check73
#print axioms OddPerfect.not_all_exponents_eq_seventy_two
