import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the reach checks of the common `95` table, part 5

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- Reach checks for the blocked source nodes, part 37. -/
theorem reach95_37 :
    src95_37.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 38. -/
theorem reach95_38 :
    src95_38.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 39. -/
theorem reach95_39 :
    src95_39.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 40. -/
theorem reach95_40 :
    src95_40.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 41. -/
theorem reach95_41 :
    src95_41.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 42. -/
theorem reach95_42 :
    src95_42.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 43. -/
theorem reach95_43 :
    src95_43.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 44. -/
theorem reach95_44 :
    src95_44.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 45. -/
theorem reach95_45 :
    src95_45.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 46. -/
theorem reach95_46 :
    src95_46.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.reach95_37
#print axioms OddPerfect.FamInst.reach95_38
#print axioms OddPerfect.FamInst.reach95_39
#print axioms OddPerfect.FamInst.reach95_40
#print axioms OddPerfect.FamInst.reach95_41
#print axioms OddPerfect.FamInst.reach95_42
#print axioms OddPerfect.FamInst.reach95_43
#print axioms OddPerfect.FamInst.reach95_44
#print axioms OddPerfect.FamInst.reach95_45
#print axioms OddPerfect.FamInst.reach95_46
