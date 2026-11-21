import OddPerfect.CommonOneFifteenData

/-!
# Common exponent families: primality of the `115` table

The nodes of the forcing table of the common `115` family in
`OddPerfect.CommonOneFifteenData` are prime, by trial division over odd numbers up to the
square root, checked in parts.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The nodes of part 0 are certified. -/
theorem nd115_0_isPS : nd115_0.all (isPS []) = true := by decide +kernel

/-- The nodes of part 1 are certified. -/
theorem nd115_1_isPS : nd115_1.all (isPS []) = true := by decide +kernel

/-- The nodes of part 2 are certified. -/
theorem nd115_2_isPS : nd115_2.all (isPS []) = true := by decide +kernel

/-- The nodes of part 3 are certified. -/
theorem nd115_3_isPS : nd115_3.all (isPS []) = true := by decide +kernel

/-- The nodes of part 4 are certified. -/
theorem nd115_4_isPS : nd115_4.all (isPS []) = true := by decide +kernel

/-- The nodes of part 5 are certified. -/
theorem nd115_5_isPS : nd115_5.all (isPS []) = true := by decide +kernel

/-- The nodes of part 6 are certified. -/
theorem nd115_6_isPS : nd115_6.all (isPS []) = true := by decide +kernel

/-- The nodes of part 7 are certified. -/
theorem nd115_7_isPS : nd115_7.all (isPS []) = true := by decide +kernel

/-- The nodes of part 8 are certified. -/
theorem nd115_8_isPS : nd115_8.all (isPS []) = true := by decide +kernel

/-- The nodes of part 9 are certified. -/
theorem nd115_9_isPS : nd115_9.all (isPS []) = true := by decide +kernel

/-- The nodes of part 10 are certified. -/
theorem nd115_10_isPS : nd115_10.all (isPS []) = true := by decide +kernel

/-- The nodes of part 11 are certified. -/
theorem nd115_11_isPS : nd115_11.all (isPS []) = true := by decide +kernel

/-- The nodes of part 12 are certified. -/
theorem nd115_12_isPS : nd115_12.all (isPS []) = true := by decide +kernel

/-- The nodes of part 13 are certified. -/
theorem nd115_13_isPS : nd115_13.all (isPS []) = true := by decide +kernel

/-- The nodes of part 14 are certified. -/
theorem nd115_14_isPS : nd115_14.all (isPS []) = true := by decide +kernel

/-- The nodes of part 15 are certified. -/
theorem nd115_15_isPS : nd115_15.all (isPS []) = true := by decide +kernel

/-- The nodes of part 16 are certified. -/
theorem nd115_16_isPS : nd115_16.all (isPS []) = true := by decide +kernel

/-- The nodes of part 17 are certified. -/
theorem nd115_17_isPS : nd115_17.all (isPS []) = true := by decide +kernel

/-- The nodes of part 18 are certified. -/
theorem nd115_18_isPS : nd115_18.all (isPS []) = true := by decide +kernel

/-- The nodes of part 19 are certified. -/
theorem nd115_19_isPS : nd115_19.all (isPS []) = true := by decide +kernel

/-- The nodes of part 20 are certified. -/
theorem nd115_20_isPS : nd115_20.all (isPS []) = true := by decide +kernel

/-- The nodes of part 21 are certified. -/
theorem nd115_21_isPS : nd115_21.all (isPS []) = true := by decide +kernel

/-- The nodes of part 22 are certified. -/
theorem nd115_22_isPS : nd115_22.all (isPS []) = true := by decide +kernel

/-- The nodes of part 23 are certified. -/
theorem nd115_23_isPS : nd115_23.all (isPS []) = true := by decide +kernel

/-- The nodes of part 24 are certified. -/
theorem nd115_24_isPS : nd115_24.all (isPS []) = true := by decide +kernel

/-- The nodes of part 25 are certified. -/
theorem nd115_25_isPS : nd115_25.all (isPS []) = true := by decide +kernel

/-- The nodes of part 26 are certified. -/
theorem nd115_26_isPS : nd115_26.all (isPS []) = true := by decide +kernel

/-- The nodes of part 27 are certified. -/
theorem nd115_27_isPS : nd115_27.all (isPS []) = true := by decide +kernel

/-- The nodes of the `d = 115` table are prime. -/
theorem nodes115_prime : ∀ t ∈ nodes115, t.Prime := fun t ht =>
  isPS_sound rfl (all_of_parts _ nd115_eq (by
    exact List.forall_mem_cons.mpr ⟨nd115_0_isPS, List.forall_mem_cons.mpr ⟨nd115_1_isPS,
      List.forall_mem_cons.mpr ⟨nd115_2_isPS, List.forall_mem_cons.mpr ⟨nd115_3_isPS,
      List.forall_mem_cons.mpr ⟨nd115_4_isPS, List.forall_mem_cons.mpr ⟨nd115_5_isPS,
      List.forall_mem_cons.mpr ⟨nd115_6_isPS, List.forall_mem_cons.mpr ⟨nd115_7_isPS,
      List.forall_mem_cons.mpr ⟨nd115_8_isPS, List.forall_mem_cons.mpr ⟨nd115_9_isPS,
      List.forall_mem_cons.mpr ⟨nd115_10_isPS, List.forall_mem_cons.mpr ⟨nd115_11_isPS,
      List.forall_mem_cons.mpr ⟨nd115_12_isPS, List.forall_mem_cons.mpr ⟨nd115_13_isPS,
      List.forall_mem_cons.mpr ⟨nd115_14_isPS, List.forall_mem_cons.mpr ⟨nd115_15_isPS,
      List.forall_mem_cons.mpr ⟨nd115_16_isPS, List.forall_mem_cons.mpr ⟨nd115_17_isPS,
      List.forall_mem_cons.mpr ⟨nd115_18_isPS, List.forall_mem_cons.mpr ⟨nd115_19_isPS,
      List.forall_mem_cons.mpr ⟨nd115_20_isPS, List.forall_mem_cons.mpr ⟨nd115_21_isPS,
      List.forall_mem_cons.mpr ⟨nd115_22_isPS, List.forall_mem_cons.mpr ⟨nd115_23_isPS,
      List.forall_mem_cons.mpr ⟨nd115_24_isPS, List.forall_mem_cons.mpr ⟨nd115_25_isPS,
      List.forall_mem_cons.mpr ⟨nd115_26_isPS, List.forall_mem_cons.mpr ⟨nd115_27_isPS, fun _ h =>
      absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) t ht)


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.nd115_0_isPS
#print axioms OddPerfect.FamInst.nd115_1_isPS
#print axioms OddPerfect.FamInst.nd115_2_isPS
#print axioms OddPerfect.FamInst.nd115_3_isPS
#print axioms OddPerfect.FamInst.nd115_4_isPS
#print axioms OddPerfect.FamInst.nd115_5_isPS
#print axioms OddPerfect.FamInst.nd115_6_isPS
#print axioms OddPerfect.FamInst.nd115_7_isPS
#print axioms OddPerfect.FamInst.nd115_8_isPS
#print axioms OddPerfect.FamInst.nd115_9_isPS
#print axioms OddPerfect.FamInst.nd115_10_isPS
#print axioms OddPerfect.FamInst.nd115_11_isPS
#print axioms OddPerfect.FamInst.nd115_12_isPS
#print axioms OddPerfect.FamInst.nd115_13_isPS
#print axioms OddPerfect.FamInst.nd115_14_isPS
#print axioms OddPerfect.FamInst.nd115_15_isPS
#print axioms OddPerfect.FamInst.nd115_16_isPS
#print axioms OddPerfect.FamInst.nd115_17_isPS
#print axioms OddPerfect.FamInst.nd115_18_isPS
#print axioms OddPerfect.FamInst.nd115_19_isPS
#print axioms OddPerfect.FamInst.nd115_20_isPS
#print axioms OddPerfect.FamInst.nd115_21_isPS
#print axioms OddPerfect.FamInst.nd115_22_isPS
#print axioms OddPerfect.FamInst.nd115_23_isPS
#print axioms OddPerfect.FamInst.nd115_24_isPS
#print axioms OddPerfect.FamInst.nd115_25_isPS
#print axioms OddPerfect.FamInst.nd115_26_isPS
#print axioms OddPerfect.FamInst.nd115_27_isPS
#print axioms OddPerfect.FamInst.nodes115_prime
