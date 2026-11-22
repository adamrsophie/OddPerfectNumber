import OddPerfect.CommonNinetyFiveData

/-!
# Common exponent families: facts about the common `95` table: its parts, its nodes are not `2`, its
target primes are selected and distinct, and their full products

Part of the proof that the common `95` family is impossible; the final theorem is in
`OddPerfect.CommonNinetyFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The rows with their sources in parts. -/
theorem zp95_eq : nodes95.zip rows95 =
    [zp95_0, zp95_1, zp95_2, zp95_3, zp95_4, zp95_5, zp95_6, zp95_7, zp95_8, zp95_9,
      zp95_10, zp95_11, zp95_12, zp95_13, zp95_14, zp95_15, zp95_16, zp95_17, zp95_18,
      zp95_19, zp95_20, zp95_21, zp95_22, zp95_23, zp95_24, zp95_25, zp95_26, zp95_27,
      zp95_28, zp95_29, zp95_30, zp95_31, zp95_32, zp95_33, zp95_34, zp95_35, zp95_36,
      zp95_37, zp95_38, zp95_39, zp95_40, zp95_41, zp95_42, zp95_43, zp95_44, zp95_45,
      zp95_46, zp95_47, zp95_48, zp95_49, zp95_50, zp95_51, zp95_52, zp95_53, zp95_54,
      zp95_55, zp95_56, zp95_57, zp95_58, zp95_59, zp95_60, zp95_61, zp95_62, zp95_63,
      zp95_64, zp95_65, zp95_66, zp95_67, zp95_68, zp95_69, zp95_70, zp95_71, zp95_72,
      zp95_73, zp95_74, zp95_75, zp95_76, zp95_77, zp95_78, zp95_79, zp95_80, zp95_81,
      zp95_82, zp95_83, zp95_84, zp95_85, zp95_86, zp95_87, zp95_88, zp95_89, zp95_90,
      zp95_91, zp95_92, zp95_93, zp95_94, zp95_95, zp95_96, zp95_97, zp95_98, zp95_99,
      zp95_100, zp95_101, zp95_102, zp95_103, zp95_104, zp95_105, zp95_106, zp95_107,
      zp95_108, zp95_109, zp95_110, zp95_111, zp95_112, zp95_113, zp95_114, zp95_115,
      zp95_116, zp95_117, zp95_118, zp95_119, zp95_120, zp95_121, zp95_122, zp95_123,
      zp95_124, zp95_125, zp95_126, zp95_127].flatten := by
  decide +kernel

/-- No node is `2`. -/
theorem nodes95_ne2 : ∀ t ∈ nodes95, t ≠ 2 := by
  have : nodes95.all (· != 2) = true := by decide +kernel
  intro t ht
  simpa using List.all_eq_true.mp this t ht

/-- The source nodes in parts. -/
theorem src95_eq : nodes95.take rows95.length =
    [src95_0, src95_1, src95_2, src95_3, src95_4, src95_5, src95_6, src95_7, src95_8,
      src95_9, src95_10, src95_11, src95_12, src95_13, src95_14, src95_15, src95_16,
      src95_17, src95_18, src95_19, src95_20, src95_21, src95_22, src95_23, src95_24,
      src95_25, src95_26, src95_27, src95_28, src95_29, src95_30, src95_31, src95_32,
      src95_33, src95_34, src95_35, src95_36, src95_37, src95_38, src95_39, src95_40,
      src95_41, src95_42, src95_43, src95_44, src95_45, src95_46, src95_47, src95_48,
      src95_49, src95_50, src95_51, src95_52, src95_53, src95_54, src95_55, src95_56,
      src95_57, src95_58, src95_59, src95_60, src95_61, src95_62, src95_63].flatten := by
  decide +kernel

/-- The nodes in parts. -/
theorem nd95_eq : nodes95 =
    [nd95_0, nd95_1, nd95_2, nd95_3, nd95_4, nd95_5, nd95_6, nd95_7, nd95_8, nd95_9,
      nd95_10, nd95_11, nd95_12, nd95_13, nd95_14, nd95_15, nd95_16, nd95_17, nd95_18,
      nd95_19, nd95_20, nd95_21, nd95_22, nd95_23, nd95_24, nd95_25, nd95_26, nd95_27,
      nd95_28, nd95_29, nd95_30, nd95_31, nd95_32, nd95_33, nd95_34, nd95_35, nd95_36,
      nd95_37, nd95_38, nd95_39, nd95_40, nd95_41, nd95_42, nd95_43, nd95_44, nd95_45,
      nd95_46, nd95_47, nd95_48, nd95_49, nd95_50, nd95_51, nd95_52, nd95_53, nd95_54,
      nd95_55, nd95_56, nd95_57, nd95_58, nd95_59, nd95_60, nd95_61, nd95_62, nd95_63,
      nd95_64, nd95_65, nd95_66, nd95_67, nd95_68, nd95_69, nd95_70, nd95_71, nd95_72,
      nd95_73, nd95_74, nd95_75, nd95_76, nd95_77, nd95_78, nd95_79, nd95_80, nd95_81,
      nd95_82, nd95_83, nd95_84, nd95_85, nd95_86, nd95_87, nd95_88, nd95_89].flatten := by
  rfl

/-- The target primes are the nodes selected by the target mask. -/
theorem vals95_sel : CommonChain.sel 0 tm95 0 nodes95 = vals95 := by decide +kernel

/-- The target primes are distinct. -/
theorem vals95_nodup : vals95.Nodup :=
  (nodup_of_ndM (M := 0) (by decide +kernel)).1

/-- The two full products over the target primes. -/
theorem PG95 : pPow (expL vals95 0) = P95 ∧ pSig (expL vals95 0) = G95 := by
  decide +kernel


end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.zp95_eq
#print axioms OddPerfect.FamInst.nodes95_ne2
#print axioms OddPerfect.FamInst.src95_eq
#print axioms OddPerfect.FamInst.nd95_eq
#print axioms OddPerfect.FamInst.vals95_sel
#print axioms OddPerfect.FamInst.vals95_nodup
#print axioms OddPerfect.FamInst.PG95
