import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the primality checks of the common `95` table, part 4

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The nodes of part 62 are prime by trial division. -/
theorem nd95_62_isPS : nd95_62.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 63 are prime by trial division. -/
theorem nd95_63_isPS : nd95_63.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 64 are prime by trial division. -/
theorem nd95_64_isPS : nd95_64.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 65 are prime by trial division. -/
theorem nd95_65_isPS : nd95_65.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 66 are prime by trial division. -/
theorem nd95_66_isPS : nd95_66.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 67 are prime by trial division. -/
theorem nd95_67_isPS : nd95_67.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 68 are prime by trial division. -/
theorem nd95_68_isPS : nd95_68.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 69 are prime by trial division. -/
theorem nd95_69_isPS : nd95_69.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 70 are prime by trial division. -/
theorem nd95_70_isPS : nd95_70.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 71 are prime by trial division. -/
theorem nd95_71_isPS : nd95_71.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 72 are prime by trial division. -/
theorem nd95_72_isPS : nd95_72.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 73 are prime by trial division. -/
theorem nd95_73_isPS : nd95_73.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 74 are prime by trial division. -/
theorem nd95_74_isPS : nd95_74.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 75 are prime by trial division. -/
theorem nd95_75_isPS : nd95_75.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 76 are prime by trial division. -/
theorem nd95_76_isPS : nd95_76.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 77 are prime by trial division. -/
theorem nd95_77_isPS : nd95_77.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 78 are prime by trial division. -/
theorem nd95_78_isPS : nd95_78.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 79 are prime by trial division. -/
theorem nd95_79_isPS : nd95_79.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 80 are prime by trial division. -/
theorem nd95_80_isPS : nd95_80.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 81 are prime by trial division. -/
theorem nd95_81_isPS : nd95_81.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 82 are prime by trial division. -/
theorem nd95_82_isPS : nd95_82.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 83 are prime by trial division. -/
theorem nd95_83_isPS : nd95_83.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 84 are prime by trial division. -/
theorem nd95_84_isPS : nd95_84.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 85 are prime by trial division. -/
theorem nd95_85_isPS : nd95_85.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 86 are prime by trial division. -/
theorem nd95_86_isPS : nd95_86.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 87 are prime by trial division. -/
theorem nd95_87_isPS : nd95_87.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 88 are prime by trial division. -/
theorem nd95_88_isPS : nd95_88.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 89 are prime by trial division. -/
theorem nd95_89_isPS : nd95_89.all (fastPrime oddP) = true := by decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.nd95_62_isPS
#print axioms OddPerfect.FamInst.nd95_63_isPS
#print axioms OddPerfect.FamInst.nd95_64_isPS
#print axioms OddPerfect.FamInst.nd95_65_isPS
#print axioms OddPerfect.FamInst.nd95_66_isPS
#print axioms OddPerfect.FamInst.nd95_67_isPS
#print axioms OddPerfect.FamInst.nd95_68_isPS
#print axioms OddPerfect.FamInst.nd95_69_isPS
#print axioms OddPerfect.FamInst.nd95_70_isPS
#print axioms OddPerfect.FamInst.nd95_71_isPS
#print axioms OddPerfect.FamInst.nd95_72_isPS
#print axioms OddPerfect.FamInst.nd95_73_isPS
#print axioms OddPerfect.FamInst.nd95_74_isPS
#print axioms OddPerfect.FamInst.nd95_75_isPS
#print axioms OddPerfect.FamInst.nd95_76_isPS
#print axioms OddPerfect.FamInst.nd95_77_isPS
#print axioms OddPerfect.FamInst.nd95_78_isPS
#print axioms OddPerfect.FamInst.nd95_79_isPS
#print axioms OddPerfect.FamInst.nd95_80_isPS
#print axioms OddPerfect.FamInst.nd95_81_isPS
#print axioms OddPerfect.FamInst.nd95_82_isPS
#print axioms OddPerfect.FamInst.nd95_83_isPS
#print axioms OddPerfect.FamInst.nd95_84_isPS
#print axioms OddPerfect.FamInst.nd95_85_isPS
#print axioms OddPerfect.FamInst.nd95_86_isPS
#print axioms OddPerfect.FamInst.nd95_87_isPS
#print axioms OddPerfect.FamInst.nd95_88_isPS
#print axioms OddPerfect.FamInst.nd95_89_isPS
