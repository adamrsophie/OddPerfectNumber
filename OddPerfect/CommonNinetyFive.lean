import OddPerfect.CommonNinetyFiveFacts
import OddPerfect.CommonNinetyFiveRows1
import OddPerfect.CommonNinetyFiveRows2
import OddPerfect.CommonNinetyFiveRows3
import OddPerfect.CommonNinetyFiveRows4
import OddPerfect.CommonNinetyFiveRows5
import OddPerfect.CommonNinetyFivePrime1
import OddPerfect.CommonNinetyFivePrime2
import OddPerfect.CommonNinetyFivePrime3
import OddPerfect.CommonNinetyFivePrime4
import OddPerfect.CommonNinetyFiveReach1

/-!
# Common exponent families: the common `95` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves that the common `95`
family is impossible, from the table and checks of the modules `OddPerfect.CommonNinetyFiveData` and
`OddPerfect.CommonNinetyFiveRows1` onward, with the reach and abundance checkers of
`OddPerfect.CommonFiveSeven`. Known: the statement follows from the Main Theorem of Fletcher,
Nielsen and Ochem (Math. Comp. 81, 2012) together with Kanold's theorem
(`OddPerfect.dvd_of_dvd_succ`); the proof here is an independent certificate checked by the kernel.
The primality, row and reach checks use the cheaper checkers of `OddPerfect.CommonFastChecks`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The divisibility checks of all rows. -/
theorem hrows95 : ∀ e ∈ nodes95.zip rows95, rowChk 95 nodes95 e = true := fun e he =>
  rowChk_of_rowChkP (K := 50) (parts := ndp95) (by decide) nd95_eq ndp95_lens
    (all_of_parts _ zp95_eq (by
    exact List.forall_mem_cons.mpr ⟨rows95_0, List.forall_mem_cons.mpr ⟨rows95_1,
      List.forall_mem_cons.mpr ⟨rows95_2, List.forall_mem_cons.mpr ⟨rows95_3,
      List.forall_mem_cons.mpr ⟨rows95_4, List.forall_mem_cons.mpr ⟨rows95_5,
      List.forall_mem_cons.mpr ⟨rows95_6, List.forall_mem_cons.mpr ⟨rows95_7,
      List.forall_mem_cons.mpr ⟨rows95_8, List.forall_mem_cons.mpr ⟨rows95_9,
      List.forall_mem_cons.mpr ⟨rows95_10, List.forall_mem_cons.mpr ⟨rows95_11,
      List.forall_mem_cons.mpr ⟨rows95_12, List.forall_mem_cons.mpr ⟨rows95_13,
      List.forall_mem_cons.mpr ⟨rows95_14, List.forall_mem_cons.mpr ⟨rows95_15,
      List.forall_mem_cons.mpr ⟨rows95_16, List.forall_mem_cons.mpr ⟨rows95_17,
      List.forall_mem_cons.mpr ⟨rows95_18, List.forall_mem_cons.mpr ⟨rows95_19,
      List.forall_mem_cons.mpr ⟨rows95_20, List.forall_mem_cons.mpr ⟨rows95_21,
      List.forall_mem_cons.mpr ⟨rows95_22, List.forall_mem_cons.mpr ⟨rows95_23,
      List.forall_mem_cons.mpr ⟨rows95_24, List.forall_mem_cons.mpr ⟨rows95_25,
      List.forall_mem_cons.mpr ⟨rows95_26, List.forall_mem_cons.mpr ⟨rows95_27,
      List.forall_mem_cons.mpr ⟨rows95_28, List.forall_mem_cons.mpr ⟨rows95_29,
      List.forall_mem_cons.mpr ⟨rows95_30, List.forall_mem_cons.mpr ⟨rows95_31,
      List.forall_mem_cons.mpr ⟨rows95_32, List.forall_mem_cons.mpr ⟨rows95_33,
      List.forall_mem_cons.mpr ⟨rows95_34, List.forall_mem_cons.mpr ⟨rows95_35,
      List.forall_mem_cons.mpr ⟨rows95_36, List.forall_mem_cons.mpr ⟨rows95_37,
      List.forall_mem_cons.mpr ⟨rows95_38, List.forall_mem_cons.mpr ⟨rows95_39,
      List.forall_mem_cons.mpr ⟨rows95_40, List.forall_mem_cons.mpr ⟨rows95_41,
      List.forall_mem_cons.mpr ⟨rows95_42, List.forall_mem_cons.mpr ⟨rows95_43,
      List.forall_mem_cons.mpr ⟨rows95_44, List.forall_mem_cons.mpr ⟨rows95_45,
      List.forall_mem_cons.mpr ⟨rows95_46, List.forall_mem_cons.mpr ⟨rows95_47,
      List.forall_mem_cons.mpr ⟨rows95_48, List.forall_mem_cons.mpr ⟨rows95_49,
      List.forall_mem_cons.mpr ⟨rows95_50, List.forall_mem_cons.mpr ⟨rows95_51,
      List.forall_mem_cons.mpr ⟨rows95_52, List.forall_mem_cons.mpr ⟨rows95_53,
      List.forall_mem_cons.mpr ⟨rows95_54, List.forall_mem_cons.mpr ⟨rows95_55,
      List.forall_mem_cons.mpr ⟨rows95_56, List.forall_mem_cons.mpr ⟨rows95_57,
      List.forall_mem_cons.mpr ⟨rows95_58, List.forall_mem_cons.mpr ⟨rows95_59,
      List.forall_mem_cons.mpr ⟨rows95_60, List.forall_mem_cons.mpr ⟨rows95_61,
      List.forall_mem_cons.mpr ⟨rows95_62, List.forall_mem_cons.mpr ⟨rows95_63,
      List.forall_mem_cons.mpr ⟨rows95_64, List.forall_mem_cons.mpr ⟨rows95_65,
      List.forall_mem_cons.mpr ⟨rows95_66, List.forall_mem_cons.mpr ⟨rows95_67,
      List.forall_mem_cons.mpr ⟨rows95_68, List.forall_mem_cons.mpr ⟨rows95_69,
      List.forall_mem_cons.mpr ⟨rows95_70, List.forall_mem_cons.mpr ⟨rows95_71,
      List.forall_mem_cons.mpr ⟨rows95_72, List.forall_mem_cons.mpr ⟨rows95_73,
      List.forall_mem_cons.mpr ⟨rows95_74, List.forall_mem_cons.mpr ⟨rows95_75,
      List.forall_mem_cons.mpr ⟨rows95_76, List.forall_mem_cons.mpr ⟨rows95_77,
      List.forall_mem_cons.mpr ⟨rows95_78, List.forall_mem_cons.mpr ⟨rows95_79,
      List.forall_mem_cons.mpr ⟨rows95_80, List.forall_mem_cons.mpr ⟨rows95_81,
      List.forall_mem_cons.mpr ⟨rows95_82, List.forall_mem_cons.mpr ⟨rows95_83,
      List.forall_mem_cons.mpr ⟨rows95_84, List.forall_mem_cons.mpr ⟨rows95_85,
      List.forall_mem_cons.mpr ⟨rows95_86, List.forall_mem_cons.mpr ⟨rows95_87,
      List.forall_mem_cons.mpr ⟨rows95_88, List.forall_mem_cons.mpr ⟨rows95_89,
      List.forall_mem_cons.mpr ⟨rows95_90, List.forall_mem_cons.mpr ⟨rows95_91,
      List.forall_mem_cons.mpr ⟨rows95_92, List.forall_mem_cons.mpr ⟨rows95_93,
      List.forall_mem_cons.mpr ⟨rows95_94, List.forall_mem_cons.mpr ⟨rows95_95,
      List.forall_mem_cons.mpr ⟨rows95_96, List.forall_mem_cons.mpr ⟨rows95_97,
      List.forall_mem_cons.mpr ⟨rows95_98, List.forall_mem_cons.mpr ⟨rows95_99,
      List.forall_mem_cons.mpr ⟨rows95_100, List.forall_mem_cons.mpr ⟨rows95_101,
      List.forall_mem_cons.mpr ⟨rows95_102, List.forall_mem_cons.mpr ⟨rows95_103,
      List.forall_mem_cons.mpr ⟨rows95_104, List.forall_mem_cons.mpr ⟨rows95_105,
      List.forall_mem_cons.mpr ⟨rows95_106, List.forall_mem_cons.mpr ⟨rows95_107,
      List.forall_mem_cons.mpr ⟨rows95_108, List.forall_mem_cons.mpr ⟨rows95_109,
      List.forall_mem_cons.mpr ⟨rows95_110, List.forall_mem_cons.mpr ⟨rows95_111,
      List.forall_mem_cons.mpr ⟨rows95_112, List.forall_mem_cons.mpr ⟨rows95_113,
      List.forall_mem_cons.mpr ⟨rows95_114, List.forall_mem_cons.mpr ⟨rows95_115,
      List.forall_mem_cons.mpr ⟨rows95_116, List.forall_mem_cons.mpr ⟨rows95_117,
      List.forall_mem_cons.mpr ⟨rows95_118, List.forall_mem_cons.mpr ⟨rows95_119,
      List.forall_mem_cons.mpr ⟨rows95_120, List.forall_mem_cons.mpr ⟨rows95_121,
      List.forall_mem_cons.mpr ⟨rows95_122, List.forall_mem_cons.mpr ⟨rows95_123,
      List.forall_mem_cons.mpr ⟨rows95_124, List.forall_mem_cons.mpr ⟨rows95_125,
      List.forall_mem_cons.mpr ⟨rows95_126, List.forall_mem_cons.mpr ⟨rows95_127, fun _ h =>
      absurd h
      List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) e he)

/-- Every blocked source node passes the reach check. -/
theorem hcand95 : ∀ b ∈ nodes95.take rows95.length, cand95 b = true →
    reach nodes95 rows95 2 tm95 3 b = true :=
  hcand_of_groups [blk95_0, blk95_1, blk95_2, blk95_3] (by
    exact List.forall_mem_cons.mpr ⟨reach95_0, List.forall_mem_cons.mpr ⟨reach95_1,
      List.forall_mem_cons.mpr ⟨reach95_2, List.forall_mem_cons.mpr ⟨reach95_3, fun _ h => absurd
      h List.not_mem_nil⟩⟩⟩⟩) blk95_cover

/-- The nodes of the `d = 95` table are prime. -/
theorem nodes95_prime : ∀ t ∈ nodes95, t.Prime := fun t ht =>
  prime_of_fastPrime (all_of_parts _ nd95_eq (by
    exact List.forall_mem_cons.mpr ⟨nd95_0_isPS, List.forall_mem_cons.mpr ⟨nd95_1_isPS,
      List.forall_mem_cons.mpr ⟨nd95_2_isPS, List.forall_mem_cons.mpr ⟨nd95_3_isPS,
      List.forall_mem_cons.mpr ⟨nd95_4_isPS, List.forall_mem_cons.mpr ⟨nd95_5_isPS,
      List.forall_mem_cons.mpr ⟨nd95_6_isPS, List.forall_mem_cons.mpr ⟨nd95_7_isPS,
      List.forall_mem_cons.mpr ⟨nd95_8_isPS, List.forall_mem_cons.mpr ⟨nd95_9_isPS,
      List.forall_mem_cons.mpr ⟨nd95_10_isPS, List.forall_mem_cons.mpr ⟨nd95_11_isPS,
      List.forall_mem_cons.mpr ⟨nd95_12_isPS, List.forall_mem_cons.mpr ⟨nd95_13_isPS,
      List.forall_mem_cons.mpr ⟨nd95_14_isPS, List.forall_mem_cons.mpr ⟨nd95_15_isPS,
      List.forall_mem_cons.mpr ⟨nd95_16_isPS, List.forall_mem_cons.mpr ⟨nd95_17_isPS,
      List.forall_mem_cons.mpr ⟨nd95_18_isPS, List.forall_mem_cons.mpr ⟨nd95_19_isPS,
      List.forall_mem_cons.mpr ⟨nd95_20_isPS, List.forall_mem_cons.mpr ⟨nd95_21_isPS,
      List.forall_mem_cons.mpr ⟨nd95_22_isPS, List.forall_mem_cons.mpr ⟨nd95_23_isPS,
      List.forall_mem_cons.mpr ⟨nd95_24_isPS, List.forall_mem_cons.mpr ⟨nd95_25_isPS,
      List.forall_mem_cons.mpr ⟨nd95_26_isPS, List.forall_mem_cons.mpr ⟨nd95_27_isPS,
      List.forall_mem_cons.mpr ⟨nd95_28_isPS, List.forall_mem_cons.mpr ⟨nd95_29_isPS,
      List.forall_mem_cons.mpr ⟨nd95_30_isPS, List.forall_mem_cons.mpr ⟨nd95_31_isPS,
      List.forall_mem_cons.mpr ⟨nd95_32_isPS, List.forall_mem_cons.mpr ⟨nd95_33_isPS,
      List.forall_mem_cons.mpr ⟨nd95_34_isPS, List.forall_mem_cons.mpr ⟨nd95_35_isPS,
      List.forall_mem_cons.mpr ⟨nd95_36_isPS, List.forall_mem_cons.mpr ⟨nd95_37_isPS,
      List.forall_mem_cons.mpr ⟨nd95_38_isPS, List.forall_mem_cons.mpr ⟨nd95_39_isPS,
      List.forall_mem_cons.mpr ⟨nd95_40_isPS, List.forall_mem_cons.mpr ⟨nd95_41_isPS,
      List.forall_mem_cons.mpr ⟨nd95_42_isPS, List.forall_mem_cons.mpr ⟨nd95_43_isPS,
      List.forall_mem_cons.mpr ⟨nd95_44_isPS, List.forall_mem_cons.mpr ⟨nd95_45_isPS,
      List.forall_mem_cons.mpr ⟨nd95_46_isPS, List.forall_mem_cons.mpr ⟨nd95_47_isPS,
      List.forall_mem_cons.mpr ⟨nd95_48_isPS, List.forall_mem_cons.mpr ⟨nd95_49_isPS,
      List.forall_mem_cons.mpr ⟨nd95_50_isPS, List.forall_mem_cons.mpr ⟨nd95_51_isPS,
      List.forall_mem_cons.mpr ⟨nd95_52_isPS, List.forall_mem_cons.mpr ⟨nd95_53_isPS,
      List.forall_mem_cons.mpr ⟨nd95_54_isPS, List.forall_mem_cons.mpr ⟨nd95_55_isPS,
      List.forall_mem_cons.mpr ⟨nd95_56_isPS, List.forall_mem_cons.mpr ⟨nd95_57_isPS,
      List.forall_mem_cons.mpr ⟨nd95_58_isPS, List.forall_mem_cons.mpr ⟨nd95_59_isPS,
      List.forall_mem_cons.mpr ⟨nd95_60_isPS, List.forall_mem_cons.mpr ⟨nd95_61_isPS,
      List.forall_mem_cons.mpr ⟨nd95_62_isPS, List.forall_mem_cons.mpr ⟨nd95_63_isPS,
      List.forall_mem_cons.mpr ⟨nd95_64_isPS, List.forall_mem_cons.mpr ⟨nd95_65_isPS,
      List.forall_mem_cons.mpr ⟨nd95_66_isPS, List.forall_mem_cons.mpr ⟨nd95_67_isPS,
      List.forall_mem_cons.mpr ⟨nd95_68_isPS, List.forall_mem_cons.mpr ⟨nd95_69_isPS,
      List.forall_mem_cons.mpr ⟨nd95_70_isPS, List.forall_mem_cons.mpr ⟨nd95_71_isPS,
      List.forall_mem_cons.mpr ⟨nd95_72_isPS, List.forall_mem_cons.mpr ⟨nd95_73_isPS,
      List.forall_mem_cons.mpr ⟨nd95_74_isPS, List.forall_mem_cons.mpr ⟨nd95_75_isPS,
      List.forall_mem_cons.mpr ⟨nd95_76_isPS, List.forall_mem_cons.mpr ⟨nd95_77_isPS,
      List.forall_mem_cons.mpr ⟨nd95_78_isPS, List.forall_mem_cons.mpr ⟨nd95_79_isPS,
      List.forall_mem_cons.mpr ⟨nd95_80_isPS, List.forall_mem_cons.mpr ⟨nd95_81_isPS,
      List.forall_mem_cons.mpr ⟨nd95_82_isPS, List.forall_mem_cons.mpr ⟨nd95_83_isPS,
      List.forall_mem_cons.mpr ⟨nd95_84_isPS, List.forall_mem_cons.mpr ⟨nd95_85_isPS,
      List.forall_mem_cons.mpr ⟨nd95_86_isPS, List.forall_mem_cons.mpr ⟨nd95_87_isPS,
      List.forall_mem_cons.mpr ⟨nd95_88_isPS, List.forall_mem_cons.mpr ⟨nd95_89_isPS, fun _ h =>
      absurd h
      List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) t ht)

/-- Abundance: the target primes with fourth powers, and with any one of them `≡ 1 (mod 12)` to
the first power. -/
theorem ab95 : abOK2 vals95 (fun b : ℕ => b % 12 == 1) P95 G95 = true := by decide +kernel


end FamInst

open FamInst in
/-- The common `95` family is impossible. Let `N` be an odd perfect number with special prime
`q`. Then `95 ∣ v_p(N) + 1` cannot hold for every ordinary prime `p`. Here `5 ∣ N`, `19 ∣ N`
and `q ≡ 1 (mod 12)`; the forcing table from the seeds `5, 19` reaches all target primes
whichever source node `≡ 1 (mod 12)` is special, and they give an abundant divisor. Known: the
statement follows from the Main Theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81, 2012)
together with Kanold's theorem (`OddPerfect.dvd_of_dvd_succ`); the proof here is an independent
certificate checked by the kernel. -/
theorem not_common_ninety_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 95 ∣ N.factorization p + 1) : False := by
  have hexp5 : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 5 ∣ 95).trans (hexp p hp hpq)
  have hexp19 : ∀ p ∈ N.primeFactors, p ≠ q → 19 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 19 ∣ 95).trans (hexp p hp hpq)
  have h5N := (five_dvd_and_ne_special_of_common h hq hodd hexp5).1
  have h19N := dvd_of_dvd_succ h hq hodd (by norm_num) (by norm_num) hexp19
  have hq12 := special_mod_twelve_of_common_five h hq hodd hexp5
  have hcq : cand95 q = true := by simp [cand95, hq12]
  have hcq' : (fun b : ℕ => b % 12 == 1) q = true := by simp [hq12]
  have hseed : ∀ t ∈ nodes95.take 2, t ∣ N := by
    intro t ht
    have : nodes95.take 2 = [5, 19] := by decide +kernel
    rw [this] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h5N
    · exact h19N
  exact false_of_reach h hexp (by norm_num) hcq hcq' nodes95_prime nodes95_ne2 hseed
    (by decide +kernel) hrows95 hcand95 reach95_none vals95_sel vals95_nodup PG95 ab95

/-- The ordinary exponents of an odd perfect number cannot all equal one `E` with
`95 ∣ E + 1`. -/
theorem not_all_exponents_eq_of_ninety_five_dvd_succ {N q E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : 95 ∣ E + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = E) : False :=
  not_common_ninety_five h hq hodd fun p hp hpq => hexp p hp hpq ▸ hE

end OddPerfect

#print axioms OddPerfect.FamInst.hrows95
#print axioms OddPerfect.FamInst.hcand95
#print axioms OddPerfect.FamInst.nodes95_prime
#print axioms OddPerfect.FamInst.ab95
#print axioms OddPerfect.not_common_ninety_five
#print axioms OddPerfect.not_all_exponents_eq_of_ninety_five_dvd_succ
