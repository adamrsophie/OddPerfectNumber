import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the reach checks of the common `95` table, part 3

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- Reach checks for the blocked source nodes, part 19. -/
theorem reach95_19 :
    src95_19.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 20. -/
theorem reach95_20 :
    src95_20.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 21. -/
theorem reach95_21 :
    src95_21.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 22. -/
theorem reach95_22 :
    src95_22.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 23. -/
theorem reach95_23 :
    src95_23.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 24. -/
theorem reach95_24 :
    src95_24.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 25. -/
theorem reach95_25 :
    src95_25.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 26. -/
theorem reach95_26 :
    src95_26.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 27. -/
theorem reach95_27 :
    src95_27.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.reach95_19
#print axioms OddPerfect.FamInst.reach95_20
#print axioms OddPerfect.FamInst.reach95_21
#print axioms OddPerfect.FamInst.reach95_22
#print axioms OddPerfect.FamInst.reach95_23
#print axioms OddPerfect.FamInst.reach95_24
#print axioms OddPerfect.FamInst.reach95_25
#print axioms OddPerfect.FamInst.reach95_26
#print axioms OddPerfect.FamInst.reach95_27
