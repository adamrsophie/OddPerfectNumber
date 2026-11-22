import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the reach checks of the common `95` table, part 6

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- Reach checks for the blocked source nodes, part 47. -/
theorem reach95_47 :
    src95_47.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 48. -/
theorem reach95_48 :
    src95_48.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 49. -/
theorem reach95_49 :
    src95_49.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 50. -/
theorem reach95_50 :
    src95_50.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 51. -/
theorem reach95_51 :
    src95_51.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 52. -/
theorem reach95_52 :
    src95_52.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 53. -/
theorem reach95_53 :
    src95_53.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 54. -/
theorem reach95_54 :
    src95_54.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 55. -/
theorem reach95_55 :
    src95_55.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 56. -/
theorem reach95_56 :
    src95_56.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 57. -/
theorem reach95_57 :
    src95_57.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 58. -/
theorem reach95_58 :
    src95_58.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 59. -/
theorem reach95_59 :
    src95_59.all (fun b => !cand95 b || reach nodes95 rows95 2 tm95 3 b) = true := by
  decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.reach95_47
#print axioms OddPerfect.FamInst.reach95_48
#print axioms OddPerfect.FamInst.reach95_49
#print axioms OddPerfect.FamInst.reach95_50
#print axioms OddPerfect.FamInst.reach95_51
#print axioms OddPerfect.FamInst.reach95_52
#print axioms OddPerfect.FamInst.reach95_53
#print axioms OddPerfect.FamInst.reach95_54
#print axioms OddPerfect.FamInst.reach95_55
#print axioms OddPerfect.FamInst.reach95_56
#print axioms OddPerfect.FamInst.reach95_57
#print axioms OddPerfect.FamInst.reach95_58
#print axioms OddPerfect.FamInst.reach95_59
