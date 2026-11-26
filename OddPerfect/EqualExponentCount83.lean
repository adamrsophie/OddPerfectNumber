import OddPerfect.EqualExponentCount
import OddPerfect.EqualExponentCount83Data

/-!
# Equal exponents `82`: a counting certificate

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The certificate for `l = 83` has a main case and 3 case(s) `q = Q`; it is checked by
`EqCount.checkCert` (see `OddPerfect.EqualExponentCount`).
-/

namespace OddPerfect.EqCount

/-- The case `q = 42829` for `l = 83` is accepted. -/
theorem case83_2_ok : checkCase 83 pc83 (some 42829) [] case83_2 = true := by
  decide +kernel

/-- The certificate for `l = 83` is accepted. -/
theorem check83 : checkCert 83 pc83 main83 cases83 = true := by
  refine checkCert_of (by decide +kernel) (by norm_num) pc83_ok main83_ok fun c hc => ?_
  simp only [cases83, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  exacts [case83_0_ok,
    case83_1_ok,
    case83_2_ok]

end OddPerfect.EqCount

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `82`. -/
theorem not_all_exponents_eq_eighty_two {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 82) : False :=
  EqCount.checkCert_sound_of_mod_four EqCount.check83 (by norm_num) h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqCount.case83_2_ok
#print axioms OddPerfect.EqCount.check83
#print axioms OddPerfect.not_all_exponents_eq_eighty_two
