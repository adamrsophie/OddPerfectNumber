import OddPerfect.EqualExponentCount
import OddPerfect.EqualExponentCount107Data

/-!
# Equal exponents `106`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 107` has a main case and 4 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 2141` for `l = 107` is accepted. -/
theorem case107_2_ok : checkCase 107 pc107 (some 2141) [] case107_2 = true := by
  decide +kernel

/-- The case `q = 13991749` for `l = 107` is accepted. -/
theorem case107_3_ok : checkCase 107 pc107 (some 13991749) [] case107_3 = true := by
  decide +kernel

/-- The certificate for `l = 107` is accepted. -/
theorem check107 : checkCert 107 pc107 main107 cases107 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc107_ok main107_ok fun c hc => ?_
  simp only [cases107, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  exacts [case107_0_ok,
    case107_1_ok,
    case107_2_ok,
    case107_3_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `106`. -/
theorem not_all_exponents_eq_one_hundred_six {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 106) : False :=
  EqCount.checkCert_sound_of_mod_four EqCount.check107 (by norm_num) h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case107_2_ok
#print axioms OddPerfect.EqCount.case107_3_ok
#print axioms OddPerfect.EqCount.check107
#print axioms OddPerfect.not_all_exponents_eq_one_hundred_six
