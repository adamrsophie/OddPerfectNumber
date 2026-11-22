import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the reach checks of the common `95` table, part 1

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- Reach checks for the blocked source nodes, part 0. -/
theorem reach95_0 :
    src95_0.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 1. -/
theorem reach95_1 :
    src95_1.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 2. -/
theorem reach95_2 :
    src95_2.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 3. -/
theorem reach95_3 :
    src95_3.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 4. -/
theorem reach95_4 :
    src95_4.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 5. -/
theorem reach95_5 :
    src95_5.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 6. -/
theorem reach95_6 :
    src95_6.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 7. -/
theorem reach95_7 :
    src95_7.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 8. -/
theorem reach95_8 :
    src95_8.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.reach95_0
#print axioms OddPerfect.FamInst.reach95_1
#print axioms OddPerfect.FamInst.reach95_2
#print axioms OddPerfect.FamInst.reach95_3
#print axioms OddPerfect.FamInst.reach95_4
#print axioms OddPerfect.FamInst.reach95_5
#print axioms OddPerfect.FamInst.reach95_6
#print axioms OddPerfect.FamInst.reach95_7
#print axioms OddPerfect.FamInst.reach95_8
