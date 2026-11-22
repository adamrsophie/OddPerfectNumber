import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the reach checks of the common `95` table, part 7

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- Reach checks for the blocked source nodes, part 60. -/
theorem reach95_60 :
    src95_60.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 61. -/
theorem reach95_61 :
    src95_61.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 62. -/
theorem reach95_62 :
    src95_62.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 63. -/
theorem reach95_63 :
    src95_63.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach check with no source blocked. -/
theorem reach95_none : reach nodes95 rows95 2 tm95 3 0 = true := by decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.reach95_60
#print axioms OddPerfect.FamInst.reach95_61
#print axioms OddPerfect.FamInst.reach95_62
#print axioms OddPerfect.FamInst.reach95_63
#print axioms OddPerfect.FamInst.reach95_none
