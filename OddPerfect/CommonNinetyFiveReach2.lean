import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the reach checks of the common `95` table, part 2

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- Reach checks for the blocked source nodes, part 9. -/
theorem reach95_9 :
    src95_9.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 10. -/
theorem reach95_10 :
    src95_10.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 11. -/
theorem reach95_11 :
    src95_11.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 12. -/
theorem reach95_12 :
    src95_12.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 13. -/
theorem reach95_13 :
    src95_13.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 14. -/
theorem reach95_14 :
    src95_14.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 15. -/
theorem reach95_15 :
    src95_15.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 16. -/
theorem reach95_16 :
    src95_16.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 17. -/
theorem reach95_17 :
    src95_17.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 18. -/
theorem reach95_18 :
    src95_18.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.reach95_9
#print axioms OddPerfect.FamInst.reach95_10
#print axioms OddPerfect.FamInst.reach95_11
#print axioms OddPerfect.FamInst.reach95_12
#print axioms OddPerfect.FamInst.reach95_13
#print axioms OddPerfect.FamInst.reach95_14
#print axioms OddPerfect.FamInst.reach95_15
#print axioms OddPerfect.FamInst.reach95_16
#print axioms OddPerfect.FamInst.reach95_17
#print axioms OddPerfect.FamInst.reach95_18
