import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: the row divisibility checks of the common `95` table, part 5

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The divisibility checks of the rows, part 114. -/
theorem rows95_114 : zp95_114.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 115. -/
theorem rows95_115 : zp95_115.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 116. -/
theorem rows95_116 : zp95_116.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 117. -/
theorem rows95_117 : zp95_117.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 118. -/
theorem rows95_118 : zp95_118.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 119. -/
theorem rows95_119 : zp95_119.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 120. -/
theorem rows95_120 : zp95_120.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 121. -/
theorem rows95_121 : zp95_121.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 122. -/
theorem rows95_122 : zp95_122.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 123. -/
theorem rows95_123 : zp95_123.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 124. -/
theorem rows95_124 : zp95_124.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 125. -/
theorem rows95_125 : zp95_125.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 126. -/
theorem rows95_126 : zp95_126.all (rowChkP 50 ndp95 95) = true := by decide +kernel

/-- The divisibility checks of the rows, part 127. -/
theorem rows95_127 : zp95_127.all (rowChkP 50 ndp95 95) = true := by decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.rows95_114
#print axioms OddPerfect.FamInst.rows95_115
#print axioms OddPerfect.FamInst.rows95_116
#print axioms OddPerfect.FamInst.rows95_117
#print axioms OddPerfect.FamInst.rows95_118
#print axioms OddPerfect.FamInst.rows95_119
#print axioms OddPerfect.FamInst.rows95_120
#print axioms OddPerfect.FamInst.rows95_121
#print axioms OddPerfect.FamInst.rows95_122
#print axioms OddPerfect.FamInst.rows95_123
#print axioms OddPerfect.FamInst.rows95_124
#print axioms OddPerfect.FamInst.rows95_125
#print axioms OddPerfect.FamInst.rows95_126
#print axioms OddPerfect.FamInst.rows95_127
