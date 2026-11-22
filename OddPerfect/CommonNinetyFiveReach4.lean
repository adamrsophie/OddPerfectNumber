import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the reach checks of the common `95` table, part 4

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- Reach checks for the blocked source nodes, part 28. -/
theorem reach95_28 :
    src95_28.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 29. -/
theorem reach95_29 :
    src95_29.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 30. -/
theorem reach95_30 :
    src95_30.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 31. -/
theorem reach95_31 :
    src95_31.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 32. -/
theorem reach95_32 :
    src95_32.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 33. -/
theorem reach95_33 :
    src95_33.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 34. -/
theorem reach95_34 :
    src95_34.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 35. -/
theorem reach95_35 :
    src95_35.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 36. -/
theorem reach95_36 :
    src95_36.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.reach95_28
#print axioms OddPerfect.FamInst.reach95_29
#print axioms OddPerfect.FamInst.reach95_30
#print axioms OddPerfect.FamInst.reach95_31
#print axioms OddPerfect.FamInst.reach95_32
#print axioms OddPerfect.FamInst.reach95_33
#print axioms OddPerfect.FamInst.reach95_34
#print axioms OddPerfect.FamInst.reach95_35
#print axioms OddPerfect.FamInst.reach95_36
