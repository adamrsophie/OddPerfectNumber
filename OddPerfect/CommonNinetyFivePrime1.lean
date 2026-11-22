import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the primality checks of the common `95` table, part 1

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The nodes of part 0 are prime by trial division. -/
theorem nd95_0_isPS : nd95_0.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 1 are prime by trial division. -/
theorem nd95_1_isPS : nd95_1.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 2 are prime by trial division. -/
theorem nd95_2_isPS : nd95_2.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 3 are prime by trial division. -/
theorem nd95_3_isPS : nd95_3.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 4 are prime by trial division. -/
theorem nd95_4_isPS : nd95_4.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 5 are prime by trial division. -/
theorem nd95_5_isPS : nd95_5.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 6 are prime by trial division. -/
theorem nd95_6_isPS : nd95_6.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 7 are prime by trial division. -/
theorem nd95_7_isPS : nd95_7.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 8 are prime by trial division. -/
theorem nd95_8_isPS : nd95_8.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 9 are prime by trial division. -/
theorem nd95_9_isPS : nd95_9.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 10 are prime by trial division. -/
theorem nd95_10_isPS : nd95_10.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 11 are prime by trial division. -/
theorem nd95_11_isPS : nd95_11.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 12 are prime by trial division. -/
theorem nd95_12_isPS : nd95_12.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 13 are prime by trial division. -/
theorem nd95_13_isPS : nd95_13.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 14 are prime by trial division. -/
theorem nd95_14_isPS : nd95_14.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 15 are prime by trial division. -/
theorem nd95_15_isPS : nd95_15.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 16 are prime by trial division. -/
theorem nd95_16_isPS : nd95_16.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 17 are prime by trial division. -/
theorem nd95_17_isPS : nd95_17.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 18 are prime by trial division. -/
theorem nd95_18_isPS : nd95_18.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 19 are prime by trial division. -/
theorem nd95_19_isPS : nd95_19.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 20 are prime by trial division. -/
theorem nd95_20_isPS : nd95_20.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 21 are prime by trial division. -/
theorem nd95_21_isPS : nd95_21.all (fastPrime oddP) = true := by decide +kernel

/-- The nodes of part 22 are prime by trial division. -/
theorem nd95_22_isPS : nd95_22.all (fastPrime oddP) = true := by decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.nd95_0_isPS
#print axioms OddPerfect.FamInst.nd95_1_isPS
#print axioms OddPerfect.FamInst.nd95_2_isPS
#print axioms OddPerfect.FamInst.nd95_3_isPS
#print axioms OddPerfect.FamInst.nd95_4_isPS
#print axioms OddPerfect.FamInst.nd95_5_isPS
#print axioms OddPerfect.FamInst.nd95_6_isPS
#print axioms OddPerfect.FamInst.nd95_7_isPS
#print axioms OddPerfect.FamInst.nd95_8_isPS
#print axioms OddPerfect.FamInst.nd95_9_isPS
#print axioms OddPerfect.FamInst.nd95_10_isPS
#print axioms OddPerfect.FamInst.nd95_11_isPS
#print axioms OddPerfect.FamInst.nd95_12_isPS
#print axioms OddPerfect.FamInst.nd95_13_isPS
#print axioms OddPerfect.FamInst.nd95_14_isPS
#print axioms OddPerfect.FamInst.nd95_15_isPS
#print axioms OddPerfect.FamInst.nd95_16_isPS
#print axioms OddPerfect.FamInst.nd95_17_isPS
#print axioms OddPerfect.FamInst.nd95_18_isPS
#print axioms OddPerfect.FamInst.nd95_19_isPS
#print axioms OddPerfect.FamInst.nd95_20_isPS
#print axioms OddPerfect.FamInst.nd95_21_isPS
#print axioms OddPerfect.FamInst.nd95_22_isPS
