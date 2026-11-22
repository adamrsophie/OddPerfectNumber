import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the primality checks of the common `95` table, part 3

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The nodes of part 43 are certified. -/
theorem nd95_43_isPS : nd95_43.all (isPS []) = true := by decide +kernel

/-- The nodes of part 44 are certified. -/
theorem nd95_44_isPS : nd95_44.all (isPS []) = true := by decide +kernel

/-- The nodes of part 45 are certified. -/
theorem nd95_45_isPS : nd95_45.all (isPS []) = true := by decide +kernel

/-- The nodes of part 46 are certified. -/
theorem nd95_46_isPS : nd95_46.all (isPS []) = true := by decide +kernel

/-- The nodes of part 47 are certified. -/
theorem nd95_47_isPS : nd95_47.all (isPS []) = true := by decide +kernel

/-- The nodes of part 48 are certified. -/
theorem nd95_48_isPS : nd95_48.all (isPS []) = true := by decide +kernel

/-- The nodes of part 49 are certified. -/
theorem nd95_49_isPS : nd95_49.all (isPS []) = true := by decide +kernel

/-- The nodes of part 50 are certified. -/
theorem nd95_50_isPS : nd95_50.all (isPS []) = true := by decide +kernel

/-- The nodes of part 51 are certified. -/
theorem nd95_51_isPS : nd95_51.all (isPS []) = true := by decide +kernel

/-- The nodes of part 52 are certified. -/
theorem nd95_52_isPS : nd95_52.all (isPS []) = true := by decide +kernel

/-- The nodes of part 53 are certified. -/
theorem nd95_53_isPS : nd95_53.all (isPS []) = true := by decide +kernel

/-- The nodes of part 54 are certified. -/
theorem nd95_54_isPS : nd95_54.all (isPS []) = true := by decide +kernel

/-- The nodes of part 55 are certified. -/
theorem nd95_55_isPS : nd95_55.all (isPS []) = true := by decide +kernel

/-- The nodes of part 56 are certified. -/
theorem nd95_56_isPS : nd95_56.all (isPS []) = true := by decide +kernel

/-- The nodes of part 57 are certified. -/
theorem nd95_57_isPS : nd95_57.all (isPS []) = true := by decide +kernel

/-- The nodes of part 58 are certified. -/
theorem nd95_58_isPS : nd95_58.all (isPS []) = true := by decide +kernel

/-- The nodes of part 59 are certified. -/
theorem nd95_59_isPS : nd95_59.all (isPS []) = true := by decide +kernel

/-- The nodes of part 60 are certified. -/
theorem nd95_60_isPS : nd95_60.all (isPS []) = true := by decide +kernel

/-- The nodes of part 61 are certified. -/
theorem nd95_61_isPS : nd95_61.all (isPS []) = true := by decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.nd95_43_isPS
#print axioms OddPerfect.FamInst.nd95_44_isPS
#print axioms OddPerfect.FamInst.nd95_45_isPS
#print axioms OddPerfect.FamInst.nd95_46_isPS
#print axioms OddPerfect.FamInst.nd95_47_isPS
#print axioms OddPerfect.FamInst.nd95_48_isPS
#print axioms OddPerfect.FamInst.nd95_49_isPS
#print axioms OddPerfect.FamInst.nd95_50_isPS
#print axioms OddPerfect.FamInst.nd95_51_isPS
#print axioms OddPerfect.FamInst.nd95_52_isPS
#print axioms OddPerfect.FamInst.nd95_53_isPS
#print axioms OddPerfect.FamInst.nd95_54_isPS
#print axioms OddPerfect.FamInst.nd95_55_isPS
#print axioms OddPerfect.FamInst.nd95_56_isPS
#print axioms OddPerfect.FamInst.nd95_57_isPS
#print axioms OddPerfect.FamInst.nd95_58_isPS
#print axioms OddPerfect.FamInst.nd95_59_isPS
#print axioms OddPerfect.FamInst.nd95_60_isPS
#print axioms OddPerfect.FamInst.nd95_61_isPS
