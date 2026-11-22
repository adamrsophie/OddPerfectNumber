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

/-- Reach check with the blocked set 0. -/
theorem reach95_0 : reachS nodes95 rows95 2 tm95 3 blk95_0 = true := by
  decide +kernel

/-- Reach check with the blocked set 1. -/
theorem reach95_1 : reachS nodes95 rows95 2 tm95 3 blk95_1 = true := by
  decide +kernel

/-- Reach check with the blocked set 2. -/
theorem reach95_2 : reachS nodes95 rows95 2 tm95 3 blk95_2 = true := by
  decide +kernel

/-- Reach check with the blocked set 3. -/
theorem reach95_3 : reachS nodes95 rows95 2 tm95 3 blk95_3 = true := by
  decide +kernel

/-- Reach check with no source blocked. -/
theorem reach95_none : reach nodes95 rows95 2 tm95 3 0 = true := by decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.reach95_0
#print axioms OddPerfect.FamInst.reach95_1
#print axioms OddPerfect.FamInst.reach95_2
#print axioms OddPerfect.FamInst.reach95_3
#print axioms OddPerfect.FamInst.reach95_none
