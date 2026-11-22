import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the primality checks of the common `95` table, part 2

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The nodes of part 23 are certified. -/
theorem nd95_23_isPS : nd95_23.all (isPS []) = true := by decide +kernel

/-- The nodes of part 24 are certified. -/
theorem nd95_24_isPS : nd95_24.all (isPS []) = true := by decide +kernel

/-- The nodes of part 25 are certified. -/
theorem nd95_25_isPS : nd95_25.all (isPS []) = true := by decide +kernel

/-- The nodes of part 26 are certified. -/
theorem nd95_26_isPS : nd95_26.all (isPS []) = true := by decide +kernel

/-- The nodes of part 27 are certified. -/
theorem nd95_27_isPS : nd95_27.all (isPS []) = true := by decide +kernel

/-- The nodes of part 28 are certified. -/
theorem nd95_28_isPS : nd95_28.all (isPS []) = true := by decide +kernel

/-- The nodes of part 29 are certified. -/
theorem nd95_29_isPS : nd95_29.all (isPS []) = true := by decide +kernel

/-- The nodes of part 30 are certified. -/
theorem nd95_30_isPS : nd95_30.all (isPS []) = true := by decide +kernel

/-- The nodes of part 31 are certified. -/
theorem nd95_31_isPS : nd95_31.all (isPS []) = true := by decide +kernel

/-- The nodes of part 32 are certified. -/
theorem nd95_32_isPS : nd95_32.all (isPS []) = true := by decide +kernel

/-- The nodes of part 33 are certified. -/
theorem nd95_33_isPS : nd95_33.all (isPS []) = true := by decide +kernel

/-- The nodes of part 34 are certified. -/
theorem nd95_34_isPS : nd95_34.all (isPS []) = true := by decide +kernel

/-- The nodes of part 35 are certified. -/
theorem nd95_35_isPS : nd95_35.all (isPS []) = true := by decide +kernel

/-- The nodes of part 36 are certified. -/
theorem nd95_36_isPS : nd95_36.all (isPS []) = true := by decide +kernel

/-- The nodes of part 37 are certified. -/
theorem nd95_37_isPS : nd95_37.all (isPS []) = true := by decide +kernel

/-- The nodes of part 38 are certified. -/
theorem nd95_38_isPS : nd95_38.all (isPS []) = true := by decide +kernel

/-- The nodes of part 39 are certified. -/
theorem nd95_39_isPS : nd95_39.all (isPS []) = true := by decide +kernel

/-- The nodes of part 40 are certified. -/
theorem nd95_40_isPS : nd95_40.all (isPS []) = true := by decide +kernel

/-- The nodes of part 41 are certified. -/
theorem nd95_41_isPS : nd95_41.all (isPS []) = true := by decide +kernel

/-- The nodes of part 42 are certified. -/
theorem nd95_42_isPS : nd95_42.all (isPS []) = true := by decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.nd95_23_isPS
#print axioms OddPerfect.FamInst.nd95_24_isPS
#print axioms OddPerfect.FamInst.nd95_25_isPS
#print axioms OddPerfect.FamInst.nd95_26_isPS
#print axioms OddPerfect.FamInst.nd95_27_isPS
#print axioms OddPerfect.FamInst.nd95_28_isPS
#print axioms OddPerfect.FamInst.nd95_29_isPS
#print axioms OddPerfect.FamInst.nd95_30_isPS
#print axioms OddPerfect.FamInst.nd95_31_isPS
#print axioms OddPerfect.FamInst.nd95_32_isPS
#print axioms OddPerfect.FamInst.nd95_33_isPS
#print axioms OddPerfect.FamInst.nd95_34_isPS
#print axioms OddPerfect.FamInst.nd95_35_isPS
#print axioms OddPerfect.FamInst.nd95_36_isPS
#print axioms OddPerfect.FamInst.nd95_37_isPS
#print axioms OddPerfect.FamInst.nd95_38_isPS
#print axioms OddPerfect.FamInst.nd95_39_isPS
#print axioms OddPerfect.FamInst.nd95_40_isPS
#print axioms OddPerfect.FamInst.nd95_41_isPS
#print axioms OddPerfect.FamInst.nd95_42_isPS
