import OddPerfect.ThreeFreeThreeData01
import OddPerfect.ThreeFreeThreeData02
import OddPerfect.ThreeFreeThreeData03
import OddPerfect.ThreeFreeThreeData04
import OddPerfect.ThreeFreeThreeData05
import OddPerfect.ThreeFreeThreeData06
import OddPerfect.ThreeFreeThreeData07
import OddPerfect.ThreeFreeThreeData08
import OddPerfect.ThreeFreeThreeData09
import OddPerfect.ThreeFreeThreeData10
import OddPerfect.ThreeFreeThreeData11

/-!
# Odd perfect numbers with three exceptional primes are divisible by 3

Let `N` be an odd perfect number with special prime `q`, and suppose every prime factor `p`
of `N` except `q`, `r₁`, `r₂` and `r₃` has an exponent `e` with `3 ∣ e + 1` (for example
`e = 2`). We show `3 ∣ N` (`three_dvd_of_three_mod_exceptions`). The case of exponents
exactly 2 is `three_dvd_of_three_exceptions`, which extends `three_dvd_of_two_exceptions` to
three exceptions, and `four_le_card_mod_exceptions` is the counting form: if `3 ∤ N`, at
least four prime factors of `N` other than `q` have an exponent `e` with `3 ∤ e + 1`.

For context only (the literature was not screened): Ochem and Zelinsky (arXiv 2607.19746)
treat one exception with exact squares, and Fletcher, Nielsen and Ochem (Math. Comp. 81,
2012) bound the least prime factor when every ordinary exponent `e` has `3 ∣ e + 1` or
`5 ∣ e + 1`, with no exception.

Assume `3 ∤ N`. The labels are replaced by three distinct prime factors of `N` other than `q`
(`ThreeFreeThree.ctx4_of_not_three_dvd`). The three primes are then relabeled so
that their classes are sorted (`ThreeFreeThree.Ctx4.cover`), and for each of the 102 sorted
class triples a binary split tree of constraints is checked by `ThreeFreeThree.treeOK`,
whose soundness is `ThreeFreeThree.treeOK_sound`. The 1223 leaves of the trees were found by
a search outside Lean and are rechecked by the kernel in the modules
`OddPerfect.ThreeFreeThreeData01` to `OddPerfect.ThreeFreeThreeData11`.
-/

namespace OddPerfect

namespace ThreeFreeThree

/-- The tree of the class triple `(5, 7, 13)`. -/
def tree0 : Tree := u0_0

/-- The tree of the class triple `(5, 7, 13)` passes the check. -/
theorem tree0_ok : treeOK (.c5, .c7, .c13) (rootNode (.c5, .c7, .c13)) tree0 = true :=
  u0_0_ok

/-- The tree of the class triple `(5, 7, 19)`. -/
def tree1 : Tree := u1_0

/-- The tree of the class triple `(5, 7, 19)` passes the check. -/
theorem tree1_ok : treeOK (.c5, .c7, .c19) (rootNode (.c5, .c7, .c19)) tree1 = true :=
  u1_0_ok

/-- The tree of the class triple `(5, 7, 31)`. -/
def tree2 : Tree := u2_0

/-- The tree of the class triple `(5, 7, 31)` passes the check. -/
theorem tree2_ok : treeOK (.c5, .c7, .c31) (rootNode (.c5, .c7, .c31)) tree2 = true :=
  u2_0_ok

/-- The tree of the class triple `(5, 7, 37)`. -/
def tree3 : Tree := u3_0

/-- The tree of the class triple `(5, 7, 37)` passes the check. -/
theorem tree3_ok : treeOK (.c5, .c7, .c37) (rootNode (.c5, .c7, .c37)) tree3 = true :=
  u3_0_ok

/-- The tree of the class triple `(5, 7, 43)`. -/
def tree4 : Tree := u4_0

/-- The tree of the class triple `(5, 7, 43)` passes the check. -/
theorem tree4_ok : treeOK (.c5, .c7, .c43) (rootNode (.c5, .c7, .c43)) tree4 = true :=
  u4_0_ok

/-- The tree of the class triple `(5, 7, n2)`. -/
def tree5 : Tree := u5_0

/-- The tree of the class triple `(5, 7, n2)` passes the check. -/
theorem tree5_ok : treeOK (.c5, .c7, .n2) (rootNode (.c5, .c7, .n2)) tree5 = true :=
  u5_0_ok

/-- The tree of the class triple `(5, 7, big)`. -/
def tree6 : Tree := u6_0

/-- The tree of the class triple `(5, 7, big)` passes the check. -/
theorem tree6_ok : treeOK (.c5, .c7, .big) (rootNode (.c5, .c7, .big)) tree6 = true :=
  u6_0_ok

/-- The tree of the class triple `(5, 13, 19)`. -/
def tree7 : Tree := u7_0

/-- The tree of the class triple `(5, 13, 19)` passes the check. -/
theorem tree7_ok : treeOK (.c5, .c13, .c19) (rootNode (.c5, .c13, .c19)) tree7 = true :=
  u7_0_ok

/-- The tree of the class triple `(5, 13, 31)`. -/
def tree8 : Tree := u8_0

/-- The tree of the class triple `(5, 13, 31)` passes the check. -/
theorem tree8_ok : treeOK (.c5, .c13, .c31) (rootNode (.c5, .c13, .c31)) tree8 = true :=
  u8_0_ok

/-- The tree of the class triple `(5, 13, 37)`. -/
def tree9 : Tree := u9_0

/-- The tree of the class triple `(5, 13, 37)` passes the check. -/
theorem tree9_ok : treeOK (.c5, .c13, .c37) (rootNode (.c5, .c13, .c37)) tree9 = true :=
  u9_0_ok

/-- The tree of the class triple `(5, 13, 43)`. -/
def tree10 : Tree := u10_0

/-- The tree of the class triple `(5, 13, 43)` passes the check. -/
theorem tree10_ok : treeOK (.c5, .c13, .c43) (rootNode (.c5, .c13, .c43)) tree10 = true :=
  u10_0_ok

/-- The tree of the class triple `(5, 13, n2)`. -/
def tree11 : Tree := u11_0

/-- The tree of the class triple `(5, 13, n2)` passes the check. -/
theorem tree11_ok : treeOK (.c5, .c13, .n2) (rootNode (.c5, .c13, .n2)) tree11 = true :=
  u11_0_ok

/-- The tree of the class triple `(5, 13, big)`. -/
def tree12 : Tree := u12_0

/-- The tree of the class triple `(5, 13, big)` passes the check. -/
theorem tree12_ok : treeOK (.c5, .c13, .big) (rootNode (.c5, .c13, .big)) tree12 = true :=
  u12_0_ok

/-- The tree of the class triple `(5, 19, 31)`. -/
def tree13 : Tree := u13_0

/-- The tree of the class triple `(5, 19, 31)` passes the check. -/
theorem tree13_ok : treeOK (.c5, .c19, .c31) (rootNode (.c5, .c19, .c31)) tree13 = true :=
  u13_0_ok

/-- The tree of the class triple `(5, 19, 37)`. -/
def tree14 : Tree := u14_0

/-- The tree of the class triple `(5, 19, 37)` passes the check. -/
theorem tree14_ok : treeOK (.c5, .c19, .c37) (rootNode (.c5, .c19, .c37)) tree14 = true :=
  u14_0_ok

/-- The tree of the class triple `(5, 19, 43)`. -/
def tree15 : Tree := u15_0

/-- The tree of the class triple `(5, 19, 43)` passes the check. -/
theorem tree15_ok : treeOK (.c5, .c19, .c43) (rootNode (.c5, .c19, .c43)) tree15 = true :=
  u15_0_ok

/-- The tree of the class triple `(5, 19, n2)`. -/
def tree16 : Tree := u16_0

/-- The tree of the class triple `(5, 19, n2)` passes the check. -/
theorem tree16_ok : treeOK (.c5, .c19, .n2) (rootNode (.c5, .c19, .n2)) tree16 = true :=
  u16_0_ok

/-- The tree of the class triple `(5, 19, big)`. -/
def tree17 : Tree := u17_0

/-- The tree of the class triple `(5, 19, big)` passes the check. -/
theorem tree17_ok : treeOK (.c5, .c19, .big) (rootNode (.c5, .c19, .big)) tree17 = true :=
  u17_0_ok

/-- The tree of the class triple `(5, 31, 37)`. -/
def tree18 : Tree := u18_0

/-- The tree of the class triple `(5, 31, 37)` passes the check. -/
theorem tree18_ok : treeOK (.c5, .c31, .c37) (rootNode (.c5, .c31, .c37)) tree18 = true :=
  u18_0_ok

/-- The tree of the class triple `(5, 31, 43)`. -/
def tree19 : Tree := u19_0

/-- The tree of the class triple `(5, 31, 43)` passes the check. -/
theorem tree19_ok : treeOK (.c5, .c31, .c43) (rootNode (.c5, .c31, .c43)) tree19 = true :=
  u19_0_ok

/-- The tree of the class triple `(5, 31, n2)`. -/
def tree20 : Tree := u20_0

/-- The tree of the class triple `(5, 31, n2)` passes the check. -/
theorem tree20_ok : treeOK (.c5, .c31, .n2) (rootNode (.c5, .c31, .n2)) tree20 = true :=
  u20_0_ok

/-- The tree of the class triple `(5, 31, big)`. -/
def tree21 : Tree := u21_0

/-- The tree of the class triple `(5, 31, big)` passes the check. -/
theorem tree21_ok : treeOK (.c5, .c31, .big) (rootNode (.c5, .c31, .big)) tree21 = true :=
  u21_0_ok

/-- The tree of the class triple `(5, 37, 43)`. -/
def tree22 : Tree := u22_0

/-- The tree of the class triple `(5, 37, 43)` passes the check. -/
theorem tree22_ok : treeOK (.c5, .c37, .c43) (rootNode (.c5, .c37, .c43)) tree22 = true :=
  u22_0_ok

/-- The tree of the class triple `(5, 37, n2)`. -/
def tree23 : Tree := u23_0

/-- The tree of the class triple `(5, 37, n2)` passes the check. -/
theorem tree23_ok : treeOK (.c5, .c37, .n2) (rootNode (.c5, .c37, .n2)) tree23 = true :=
  u23_0_ok

/-- The tree of the class triple `(5, 37, big)`. -/
def tree24 : Tree := u24_0

/-- The tree of the class triple `(5, 37, big)` passes the check. -/
theorem tree24_ok : treeOK (.c5, .c37, .big) (rootNode (.c5, .c37, .big)) tree24 = true :=
  u24_0_ok

/-- The tree of the class triple `(5, 43, n2)`. -/
def tree25 : Tree := u25_0

/-- The tree of the class triple `(5, 43, n2)` passes the check. -/
theorem tree25_ok : treeOK (.c5, .c43, .n2) (rootNode (.c5, .c43, .n2)) tree25 = true :=
  u25_0_ok

/-- The tree of the class triple `(5, 43, big)`. -/
def tree26 : Tree := u26_0

/-- The tree of the class triple `(5, 43, big)` passes the check. -/
theorem tree26_ok : treeOK (.c5, .c43, .big) (rootNode (.c5, .c43, .big)) tree26 = true :=
  u26_0_ok

/-- The tree of the class triple `(5, n2, n2)`. -/
def tree27 : Tree := u27_0

/-- The tree of the class triple `(5, n2, n2)` passes the check. -/
theorem tree27_ok : treeOK (.c5, .n2, .n2) (rootNode (.c5, .n2, .n2)) tree27 = true :=
  u27_0_ok

/-- The tree of the class triple `(5, n2, big)`. -/
def tree28 : Tree := u28_0

/-- The tree of the class triple `(5, n2, big)` passes the check. -/
theorem tree28_ok : treeOK (.c5, .n2, .big) (rootNode (.c5, .n2, .big)) tree28 = true :=
  u28_0_ok

/-- The tree of the class triple `(5, big, big)`. -/
def tree29 : Tree := u29_0

/-- The tree of the class triple `(5, big, big)` passes the check. -/
theorem tree29_ok : treeOK (.c5, .big, .big) (rootNode (.c5, .big, .big)) tree29 = true :=
  u29_0_ok

/-- The tree of the class triple `(7, 13, 19)`. -/
def tree30 : Tree := u30_0

/-- The tree of the class triple `(7, 13, 19)` passes the check. -/
theorem tree30_ok : treeOK (.c7, .c13, .c19) (rootNode (.c7, .c13, .c19)) tree30 = true :=
  u30_0_ok

/-- The tree of the class triple `(7, 13, 31)`. -/
def tree31 : Tree := u31_0

/-- The tree of the class triple `(7, 13, 31)` passes the check. -/
theorem tree31_ok : treeOK (.c7, .c13, .c31) (rootNode (.c7, .c13, .c31)) tree31 = true :=
  u31_0_ok

/-- The tree of the class triple `(7, 13, 37)`. -/
def tree32 : Tree := u32_0

/-- The tree of the class triple `(7, 13, 37)` passes the check. -/
theorem tree32_ok : treeOK (.c7, .c13, .c37) (rootNode (.c7, .c13, .c37)) tree32 = true :=
  u32_0_ok

/-- The tree of the class triple `(7, 13, 43)`. -/
def tree33 : Tree := u33_0

/-- The tree of the class triple `(7, 13, 43)` passes the check. -/
theorem tree33_ok : treeOK (.c7, .c13, .c43) (rootNode (.c7, .c13, .c43)) tree33 = true :=
  u33_0_ok

/-- The tree of the class triple `(7, 13, n2)`. -/
def tree34 : Tree := u34_0

/-- The tree of the class triple `(7, 13, n2)` passes the check. -/
theorem tree34_ok : treeOK (.c7, .c13, .n2) (rootNode (.c7, .c13, .n2)) tree34 = true :=
  u34_0_ok

/-- The tree of the class triple `(7, 13, big)`. -/
def tree35 : Tree := u35_0

/-- The tree of the class triple `(7, 13, big)` passes the check. -/
theorem tree35_ok : treeOK (.c7, .c13, .big) (rootNode (.c7, .c13, .big)) tree35 = true :=
  u35_0_ok

/-- The tree of the class triple `(7, 19, 31)`. -/
def tree36 : Tree := u36_0

/-- The tree of the class triple `(7, 19, 31)` passes the check. -/
theorem tree36_ok : treeOK (.c7, .c19, .c31) (rootNode (.c7, .c19, .c31)) tree36 = true :=
  u36_0_ok

/-- The tree of the class triple `(7, 19, 37)`. -/
def tree37 : Tree := u37_0

/-- The tree of the class triple `(7, 19, 37)` passes the check. -/
theorem tree37_ok : treeOK (.c7, .c19, .c37) (rootNode (.c7, .c19, .c37)) tree37 = true :=
  u37_0_ok

/-- The tree of the class triple `(7, 19, 43)`. -/
def tree38 : Tree := u38_0

/-- The tree of the class triple `(7, 19, 43)` passes the check. -/
theorem tree38_ok : treeOK (.c7, .c19, .c43) (rootNode (.c7, .c19, .c43)) tree38 = true :=
  u38_0_ok

/-- The tree of the class triple `(7, 19, n2)`. -/
def tree39 : Tree := u39_0

/-- The tree of the class triple `(7, 19, n2)` passes the check. -/
theorem tree39_ok : treeOK (.c7, .c19, .n2) (rootNode (.c7, .c19, .n2)) tree39 = true :=
  u39_0_ok

/-- The tree of the class triple `(7, 19, big)`. -/
def tree40 : Tree := u40_0

/-- The tree of the class triple `(7, 19, big)` passes the check. -/
theorem tree40_ok : treeOK (.c7, .c19, .big) (rootNode (.c7, .c19, .big)) tree40 = true :=
  u40_0_ok

/-- The tree of the class triple `(7, 31, 37)`. -/
def tree41 : Tree := u41_0

/-- The tree of the class triple `(7, 31, 37)` passes the check. -/
theorem tree41_ok : treeOK (.c7, .c31, .c37) (rootNode (.c7, .c31, .c37)) tree41 = true :=
  u41_0_ok

/-- The tree of the class triple `(7, 31, 43)`. -/
def tree42 : Tree := u42_0

/-- The tree of the class triple `(7, 31, 43)` passes the check. -/
theorem tree42_ok : treeOK (.c7, .c31, .c43) (rootNode (.c7, .c31, .c43)) tree42 = true :=
  u42_0_ok

/-- The tree of the class triple `(7, 31, n2)`. -/
def tree43 : Tree := u43_0

/-- The tree of the class triple `(7, 31, n2)` passes the check. -/
theorem tree43_ok : treeOK (.c7, .c31, .n2) (rootNode (.c7, .c31, .n2)) tree43 = true :=
  u43_0_ok

/-- The tree of the class triple `(7, 31, big)`. -/
def tree44 : Tree := (.split 3 61 u44_0 (.split 3 67 u44_1 (.split 3 73 u44_2 (.split 3 79 u44_3 (.split 3 103 u44_4 (.split 3 109 u44_5 (.split 3 127 u44_6 (.split 3 151 u44_7 (.split 3 307 u44_8 (.split 3 409 u44_9 (.split 3 709 u44_10 (.split 3 727 u44_11 (.split 3 991 u44_12 (.split 3 1087 u44_13 (.split 3 1723 u44_14 (.split 3 3541 u44_15 u44_16))))))))))))))))

/-- The tree of the class triple `(7, 31, big)` passes the check. -/
theorem tree44_ok : treeOK (.c7, .c31, .big) (rootNode (.c7, .c31, .big)) tree44 = true :=
  (treeOK_split (by decide) rfl u44_0_ok (treeOK_split (by decide) rfl u44_1_ok (treeOK_split (by decide) rfl u44_2_ok (treeOK_split (by decide) rfl u44_3_ok (treeOK_split (by decide) rfl u44_4_ok (treeOK_split (by decide) rfl u44_5_ok (treeOK_split (by decide) rfl u44_6_ok (treeOK_split (by decide) rfl u44_7_ok (treeOK_split (by decide) rfl u44_8_ok (treeOK_split (by decide) rfl u44_9_ok (treeOK_split (by decide) rfl u44_10_ok (treeOK_split (by decide) rfl u44_11_ok (treeOK_split (by decide) rfl u44_12_ok (treeOK_split (by decide) rfl u44_13_ok (treeOK_split (by decide) rfl u44_14_ok (treeOK_split (by decide) rfl u44_15_ok u44_16_ok))))))))))))))))

/-- The tree of the class triple `(7, 37, 43)`. -/
def tree45 : Tree := u45_0

/-- The tree of the class triple `(7, 37, 43)` passes the check. -/
theorem tree45_ok : treeOK (.c7, .c37, .c43) (rootNode (.c7, .c37, .c43)) tree45 = true :=
  u45_0_ok

/-- The tree of the class triple `(7, 37, n2)`. -/
def tree46 : Tree := u46_0

/-- The tree of the class triple `(7, 37, n2)` passes the check. -/
theorem tree46_ok : treeOK (.c7, .c37, .n2) (rootNode (.c7, .c37, .n2)) tree46 = true :=
  u46_0_ok

/-- The tree of the class triple `(7, 37, big)`. -/
def tree47 : Tree := u47_0

/-- The tree of the class triple `(7, 37, big)` passes the check. -/
theorem tree47_ok : treeOK (.c7, .c37, .big) (rootNode (.c7, .c37, .big)) tree47 = true :=
  u47_0_ok

/-- The tree of the class triple `(7, 43, n2)`. -/
def tree48 : Tree := u48_0

/-- The tree of the class triple `(7, 43, n2)` passes the check. -/
theorem tree48_ok : treeOK (.c7, .c43, .n2) (rootNode (.c7, .c43, .n2)) tree48 = true :=
  u48_0_ok

/-- The tree of the class triple `(7, 43, big)`. -/
def tree49 : Tree := u49_0

/-- The tree of the class triple `(7, 43, big)` passes the check. -/
theorem tree49_ok : treeOK (.c7, .c43, .big) (rootNode (.c7, .c43, .big)) tree49 = true :=
  u49_0_ok

/-- The tree of the class triple `(7, n2, n2)`. -/
def tree50 : Tree := u50_0

/-- The tree of the class triple `(7, n2, n2)` passes the check. -/
theorem tree50_ok : treeOK (.c7, .n2, .n2) (rootNode (.c7, .n2, .n2)) tree50 = true :=
  u50_0_ok

/-- The tree of the class triple `(7, n2, big)`. -/
def tree51 : Tree := u51_0

/-- The tree of the class triple `(7, n2, big)` passes the check. -/
theorem tree51_ok : treeOK (.c7, .n2, .big) (rootNode (.c7, .n2, .big)) tree51 = true :=
  u51_0_ok

/-- The tree of the class triple `(7, big, big)`. -/
def tree52 : Tree := (.split 2 61 u52_0 u52_1)

/-- The tree of the class triple `(7, big, big)` passes the check. -/
theorem tree52_ok : treeOK (.c7, .big, .big) (rootNode (.c7, .big, .big)) tree52 = true :=
  (treeOK_split (by decide) rfl u52_0_ok u52_1_ok)

/-- The tree of the class triple `(13, 19, 31)`. -/
def tree53 : Tree := u53_0

/-- The tree of the class triple `(13, 19, 31)` passes the check. -/
theorem tree53_ok : treeOK (.c13, .c19, .c31) (rootNode (.c13, .c19, .c31)) tree53 = true :=
  u53_0_ok

/-- The tree of the class triple `(13, 19, 37)`. -/
def tree54 : Tree := u54_0

/-- The tree of the class triple `(13, 19, 37)` passes the check. -/
theorem tree54_ok : treeOK (.c13, .c19, .c37) (rootNode (.c13, .c19, .c37)) tree54 = true :=
  u54_0_ok

/-- The tree of the class triple `(13, 19, 43)`. -/
def tree55 : Tree := u55_0

/-- The tree of the class triple `(13, 19, 43)` passes the check. -/
theorem tree55_ok : treeOK (.c13, .c19, .c43) (rootNode (.c13, .c19, .c43)) tree55 = true :=
  u55_0_ok

/-- The tree of the class triple `(13, 19, n2)`. -/
def tree56 : Tree := u56_0

/-- The tree of the class triple `(13, 19, n2)` passes the check. -/
theorem tree56_ok : treeOK (.c13, .c19, .n2) (rootNode (.c13, .c19, .n2)) tree56 = true :=
  u56_0_ok

/-- The tree of the class triple `(13, 19, big)`. -/
def tree57 : Tree := u57_0

/-- The tree of the class triple `(13, 19, big)` passes the check. -/
theorem tree57_ok : treeOK (.c13, .c19, .big) (rootNode (.c13, .c19, .big)) tree57 = true :=
  u57_0_ok

/-- The tree of the class triple `(13, 31, 37)`. -/
def tree58 : Tree := u58_0

/-- The tree of the class triple `(13, 31, 37)` passes the check. -/
theorem tree58_ok : treeOK (.c13, .c31, .c37) (rootNode (.c13, .c31, .c37)) tree58 = true :=
  u58_0_ok

/-- The tree of the class triple `(13, 31, 43)`. -/
def tree59 : Tree := u59_0

/-- The tree of the class triple `(13, 31, 43)` passes the check. -/
theorem tree59_ok : treeOK (.c13, .c31, .c43) (rootNode (.c13, .c31, .c43)) tree59 = true :=
  u59_0_ok

/-- The tree of the class triple `(13, 31, n2)`. -/
def tree60 : Tree := u60_0

/-- The tree of the class triple `(13, 31, n2)` passes the check. -/
theorem tree60_ok : treeOK (.c13, .c31, .n2) (rootNode (.c13, .c31, .n2)) tree60 = true :=
  u60_0_ok

/-- The tree of the class triple `(13, 31, big)`. -/
def tree61 : Tree := u61_0

/-- The tree of the class triple `(13, 31, big)` passes the check. -/
theorem tree61_ok : treeOK (.c13, .c31, .big) (rootNode (.c13, .c31, .big)) tree61 = true :=
  u61_0_ok

/-- The tree of the class triple `(13, 37, 43)`. -/
def tree62 : Tree := u62_0

/-- The tree of the class triple `(13, 37, 43)` passes the check. -/
theorem tree62_ok : treeOK (.c13, .c37, .c43) (rootNode (.c13, .c37, .c43)) tree62 = true :=
  u62_0_ok

/-- The tree of the class triple `(13, 37, n2)`. -/
def tree63 : Tree := u63_0

/-- The tree of the class triple `(13, 37, n2)` passes the check. -/
theorem tree63_ok : treeOK (.c13, .c37, .n2) (rootNode (.c13, .c37, .n2)) tree63 = true :=
  u63_0_ok

/-- The tree of the class triple `(13, 37, big)`. -/
def tree64 : Tree := u64_0

/-- The tree of the class triple `(13, 37, big)` passes the check. -/
theorem tree64_ok : treeOK (.c13, .c37, .big) (rootNode (.c13, .c37, .big)) tree64 = true :=
  u64_0_ok

/-- The tree of the class triple `(13, 43, n2)`. -/
def tree65 : Tree := u65_0

/-- The tree of the class triple `(13, 43, n2)` passes the check. -/
theorem tree65_ok : treeOK (.c13, .c43, .n2) (rootNode (.c13, .c43, .n2)) tree65 = true :=
  u65_0_ok

/-- The tree of the class triple `(13, 43, big)`. -/
def tree66 : Tree := u66_0

/-- The tree of the class triple `(13, 43, big)` passes the check. -/
theorem tree66_ok : treeOK (.c13, .c43, .big) (rootNode (.c13, .c43, .big)) tree66 = true :=
  u66_0_ok

/-- The tree of the class triple `(13, n2, n2)`. -/
def tree67 : Tree := u67_0

/-- The tree of the class triple `(13, n2, n2)` passes the check. -/
theorem tree67_ok : treeOK (.c13, .n2, .n2) (rootNode (.c13, .n2, .n2)) tree67 = true :=
  u67_0_ok

/-- The tree of the class triple `(13, n2, big)`. -/
def tree68 : Tree := u68_0

/-- The tree of the class triple `(13, n2, big)` passes the check. -/
theorem tree68_ok : treeOK (.c13, .n2, .big) (rootNode (.c13, .n2, .big)) tree68 = true :=
  u68_0_ok

/-- The tree of the class triple `(13, big, big)`. -/
def tree69 : Tree := u69_0

/-- The tree of the class triple `(13, big, big)` passes the check. -/
theorem tree69_ok : treeOK (.c13, .big, .big) (rootNode (.c13, .big, .big)) tree69 = true :=
  u69_0_ok

/-- The tree of the class triple `(19, 31, 37)`. -/
def tree70 : Tree := u70_0

/-- The tree of the class triple `(19, 31, 37)` passes the check. -/
theorem tree70_ok : treeOK (.c19, .c31, .c37) (rootNode (.c19, .c31, .c37)) tree70 = true :=
  u70_0_ok

/-- The tree of the class triple `(19, 31, 43)`. -/
def tree71 : Tree := u71_0

/-- The tree of the class triple `(19, 31, 43)` passes the check. -/
theorem tree71_ok : treeOK (.c19, .c31, .c43) (rootNode (.c19, .c31, .c43)) tree71 = true :=
  u71_0_ok

/-- The tree of the class triple `(19, 31, n2)`. -/
def tree72 : Tree := u72_0

/-- The tree of the class triple `(19, 31, n2)` passes the check. -/
theorem tree72_ok : treeOK (.c19, .c31, .n2) (rootNode (.c19, .c31, .n2)) tree72 = true :=
  u72_0_ok

/-- The tree of the class triple `(19, 31, big)`. -/
def tree73 : Tree := u73_0

/-- The tree of the class triple `(19, 31, big)` passes the check. -/
theorem tree73_ok : treeOK (.c19, .c31, .big) (rootNode (.c19, .c31, .big)) tree73 = true :=
  u73_0_ok

/-- The tree of the class triple `(19, 37, 43)`. -/
def tree74 : Tree := u74_0

/-- The tree of the class triple `(19, 37, 43)` passes the check. -/
theorem tree74_ok : treeOK (.c19, .c37, .c43) (rootNode (.c19, .c37, .c43)) tree74 = true :=
  u74_0_ok

/-- The tree of the class triple `(19, 37, n2)`. -/
def tree75 : Tree := u75_0

/-- The tree of the class triple `(19, 37, n2)` passes the check. -/
theorem tree75_ok : treeOK (.c19, .c37, .n2) (rootNode (.c19, .c37, .n2)) tree75 = true :=
  u75_0_ok

/-- The tree of the class triple `(19, 37, big)`. -/
def tree76 : Tree := u76_0

/-- The tree of the class triple `(19, 37, big)` passes the check. -/
theorem tree76_ok : treeOK (.c19, .c37, .big) (rootNode (.c19, .c37, .big)) tree76 = true :=
  u76_0_ok

/-- The tree of the class triple `(19, 43, n2)`. -/
def tree77 : Tree := u77_0

/-- The tree of the class triple `(19, 43, n2)` passes the check. -/
theorem tree77_ok : treeOK (.c19, .c43, .n2) (rootNode (.c19, .c43, .n2)) tree77 = true :=
  u77_0_ok

/-- The tree of the class triple `(19, 43, big)`. -/
def tree78 : Tree := u78_0

/-- The tree of the class triple `(19, 43, big)` passes the check. -/
theorem tree78_ok : treeOK (.c19, .c43, .big) (rootNode (.c19, .c43, .big)) tree78 = true :=
  u78_0_ok

/-- The tree of the class triple `(19, n2, n2)`. -/
def tree79 : Tree := u79_0

/-- The tree of the class triple `(19, n2, n2)` passes the check. -/
theorem tree79_ok : treeOK (.c19, .n2, .n2) (rootNode (.c19, .n2, .n2)) tree79 = true :=
  u79_0_ok

/-- The tree of the class triple `(19, n2, big)`. -/
def tree80 : Tree := u80_0

/-- The tree of the class triple `(19, n2, big)` passes the check. -/
theorem tree80_ok : treeOK (.c19, .n2, .big) (rootNode (.c19, .n2, .big)) tree80 = true :=
  u80_0_ok

/-- The tree of the class triple `(19, big, big)`. -/
def tree81 : Tree := u81_0

/-- The tree of the class triple `(19, big, big)` passes the check. -/
theorem tree81_ok : treeOK (.c19, .big, .big) (rootNode (.c19, .big, .big)) tree81 = true :=
  u81_0_ok

/-- The tree of the class triple `(31, 37, 43)`. -/
def tree82 : Tree := u82_0

/-- The tree of the class triple `(31, 37, 43)` passes the check. -/
theorem tree82_ok : treeOK (.c31, .c37, .c43) (rootNode (.c31, .c37, .c43)) tree82 = true :=
  u82_0_ok

/-- The tree of the class triple `(31, 37, n2)`. -/
def tree83 : Tree := u83_0

/-- The tree of the class triple `(31, 37, n2)` passes the check. -/
theorem tree83_ok : treeOK (.c31, .c37, .n2) (rootNode (.c31, .c37, .n2)) tree83 = true :=
  u83_0_ok

/-- The tree of the class triple `(31, 37, big)`. -/
def tree84 : Tree := u84_0

/-- The tree of the class triple `(31, 37, big)` passes the check. -/
theorem tree84_ok : treeOK (.c31, .c37, .big) (rootNode (.c31, .c37, .big)) tree84 = true :=
  u84_0_ok

/-- The tree of the class triple `(31, 43, n2)`. -/
def tree85 : Tree := u85_0

/-- The tree of the class triple `(31, 43, n2)` passes the check. -/
theorem tree85_ok : treeOK (.c31, .c43, .n2) (rootNode (.c31, .c43, .n2)) tree85 = true :=
  u85_0_ok

/-- The tree of the class triple `(31, 43, big)`. -/
def tree86 : Tree := u86_0

/-- The tree of the class triple `(31, 43, big)` passes the check. -/
theorem tree86_ok : treeOK (.c31, .c43, .big) (rootNode (.c31, .c43, .big)) tree86 = true :=
  u86_0_ok

/-- The tree of the class triple `(31, n2, n2)`. -/
def tree87 : Tree := u87_0

/-- The tree of the class triple `(31, n2, n2)` passes the check. -/
theorem tree87_ok : treeOK (.c31, .n2, .n2) (rootNode (.c31, .n2, .n2)) tree87 = true :=
  u87_0_ok

/-- The tree of the class triple `(31, n2, big)`. -/
def tree88 : Tree := u88_0

/-- The tree of the class triple `(31, n2, big)` passes the check. -/
theorem tree88_ok : treeOK (.c31, .n2, .big) (rootNode (.c31, .n2, .big)) tree88 = true :=
  u88_0_ok

/-- The tree of the class triple `(31, big, big)`. -/
def tree89 : Tree := u89_0

/-- The tree of the class triple `(31, big, big)` passes the check. -/
theorem tree89_ok : treeOK (.c31, .big, .big) (rootNode (.c31, .big, .big)) tree89 = true :=
  u89_0_ok

/-- The tree of the class triple `(37, 43, n2)`. -/
def tree90 : Tree := u90_0

/-- The tree of the class triple `(37, 43, n2)` passes the check. -/
theorem tree90_ok : treeOK (.c37, .c43, .n2) (rootNode (.c37, .c43, .n2)) tree90 = true :=
  u90_0_ok

/-- The tree of the class triple `(37, 43, big)`. -/
def tree91 : Tree := u91_0

/-- The tree of the class triple `(37, 43, big)` passes the check. -/
theorem tree91_ok : treeOK (.c37, .c43, .big) (rootNode (.c37, .c43, .big)) tree91 = true :=
  u91_0_ok

/-- The tree of the class triple `(37, n2, n2)`. -/
def tree92 : Tree := u92_0

/-- The tree of the class triple `(37, n2, n2)` passes the check. -/
theorem tree92_ok : treeOK (.c37, .n2, .n2) (rootNode (.c37, .n2, .n2)) tree92 = true :=
  u92_0_ok

/-- The tree of the class triple `(37, n2, big)`. -/
def tree93 : Tree := u93_0

/-- The tree of the class triple `(37, n2, big)` passes the check. -/
theorem tree93_ok : treeOK (.c37, .n2, .big) (rootNode (.c37, .n2, .big)) tree93 = true :=
  u93_0_ok

/-- The tree of the class triple `(37, big, big)`. -/
def tree94 : Tree := u94_0

/-- The tree of the class triple `(37, big, big)` passes the check. -/
theorem tree94_ok : treeOK (.c37, .big, .big) (rootNode (.c37, .big, .big)) tree94 = true :=
  u94_0_ok

/-- The tree of the class triple `(43, n2, n2)`. -/
def tree95 : Tree := u95_0

/-- The tree of the class triple `(43, n2, n2)` passes the check. -/
theorem tree95_ok : treeOK (.c43, .n2, .n2) (rootNode (.c43, .n2, .n2)) tree95 = true :=
  u95_0_ok

/-- The tree of the class triple `(43, n2, big)`. -/
def tree96 : Tree := u96_0

/-- The tree of the class triple `(43, n2, big)` passes the check. -/
theorem tree96_ok : treeOK (.c43, .n2, .big) (rootNode (.c43, .n2, .big)) tree96 = true :=
  u96_0_ok

/-- The tree of the class triple `(43, big, big)`. -/
def tree97 : Tree := u97_0

/-- The tree of the class triple `(43, big, big)` passes the check. -/
theorem tree97_ok : treeOK (.c43, .big, .big) (rootNode (.c43, .big, .big)) tree97 = true :=
  u97_0_ok

/-- The tree of the class triple `(n2, n2, n2)`. -/
def tree98 : Tree := u98_0

/-- The tree of the class triple `(n2, n2, n2)` passes the check. -/
theorem tree98_ok : treeOK (.n2, .n2, .n2) (rootNode (.n2, .n2, .n2)) tree98 = true :=
  u98_0_ok

/-- The tree of the class triple `(n2, n2, big)`. -/
def tree99 : Tree := u99_0

/-- The tree of the class triple `(n2, n2, big)` passes the check. -/
theorem tree99_ok : treeOK (.n2, .n2, .big) (rootNode (.n2, .n2, .big)) tree99 = true :=
  u99_0_ok

/-- The tree of the class triple `(n2, big, big)`. -/
def tree100 : Tree := u100_0

/-- The tree of the class triple `(n2, big, big)` passes the check. -/
theorem tree100_ok : treeOK (.n2, .big, .big) (rootNode (.n2, .big, .big)) tree100 = true :=
  u100_0_ok

/-- The tree of the class triple `(big, big, big)`. -/
def tree101 : Tree := u101_0

/-- The tree of the class triple `(big, big, big)` passes the check. -/
theorem tree101_ok : treeOK (.big, .big, .big) (rootNode (.big, .big, .big)) tree101 = true :=
  u101_0_ok

/-- The trees of the 102 sorted class triples. -/
def trees : List (ClassTriple × Tree) :=
  [((.c5, .c7, .c13), tree0),
    ((.c5, .c7, .c19), tree1),
    ((.c5, .c7, .c31), tree2),
    ((.c5, .c7, .c37), tree3),
    ((.c5, .c7, .c43), tree4),
    ((.c5, .c7, .n2), tree5),
    ((.c5, .c7, .big), tree6),
    ((.c5, .c13, .c19), tree7),
    ((.c5, .c13, .c31), tree8),
    ((.c5, .c13, .c37), tree9),
    ((.c5, .c13, .c43), tree10),
    ((.c5, .c13, .n2), tree11),
    ((.c5, .c13, .big), tree12),
    ((.c5, .c19, .c31), tree13),
    ((.c5, .c19, .c37), tree14),
    ((.c5, .c19, .c43), tree15),
    ((.c5, .c19, .n2), tree16),
    ((.c5, .c19, .big), tree17),
    ((.c5, .c31, .c37), tree18),
    ((.c5, .c31, .c43), tree19),
    ((.c5, .c31, .n2), tree20),
    ((.c5, .c31, .big), tree21),
    ((.c5, .c37, .c43), tree22),
    ((.c5, .c37, .n2), tree23),
    ((.c5, .c37, .big), tree24),
    ((.c5, .c43, .n2), tree25),
    ((.c5, .c43, .big), tree26),
    ((.c5, .n2, .n2), tree27),
    ((.c5, .n2, .big), tree28),
    ((.c5, .big, .big), tree29),
    ((.c7, .c13, .c19), tree30),
    ((.c7, .c13, .c31), tree31),
    ((.c7, .c13, .c37), tree32),
    ((.c7, .c13, .c43), tree33),
    ((.c7, .c13, .n2), tree34),
    ((.c7, .c13, .big), tree35),
    ((.c7, .c19, .c31), tree36),
    ((.c7, .c19, .c37), tree37),
    ((.c7, .c19, .c43), tree38),
    ((.c7, .c19, .n2), tree39),
    ((.c7, .c19, .big), tree40),
    ((.c7, .c31, .c37), tree41),
    ((.c7, .c31, .c43), tree42),
    ((.c7, .c31, .n2), tree43),
    ((.c7, .c31, .big), tree44),
    ((.c7, .c37, .c43), tree45),
    ((.c7, .c37, .n2), tree46),
    ((.c7, .c37, .big), tree47),
    ((.c7, .c43, .n2), tree48),
    ((.c7, .c43, .big), tree49),
    ((.c7, .n2, .n2), tree50),
    ((.c7, .n2, .big), tree51),
    ((.c7, .big, .big), tree52),
    ((.c13, .c19, .c31), tree53),
    ((.c13, .c19, .c37), tree54),
    ((.c13, .c19, .c43), tree55),
    ((.c13, .c19, .n2), tree56),
    ((.c13, .c19, .big), tree57),
    ((.c13, .c31, .c37), tree58),
    ((.c13, .c31, .c43), tree59),
    ((.c13, .c31, .n2), tree60),
    ((.c13, .c31, .big), tree61),
    ((.c13, .c37, .c43), tree62),
    ((.c13, .c37, .n2), tree63),
    ((.c13, .c37, .big), tree64),
    ((.c13, .c43, .n2), tree65),
    ((.c13, .c43, .big), tree66),
    ((.c13, .n2, .n2), tree67),
    ((.c13, .n2, .big), tree68),
    ((.c13, .big, .big), tree69),
    ((.c19, .c31, .c37), tree70),
    ((.c19, .c31, .c43), tree71),
    ((.c19, .c31, .n2), tree72),
    ((.c19, .c31, .big), tree73),
    ((.c19, .c37, .c43), tree74),
    ((.c19, .c37, .n2), tree75),
    ((.c19, .c37, .big), tree76),
    ((.c19, .c43, .n2), tree77),
    ((.c19, .c43, .big), tree78),
    ((.c19, .n2, .n2), tree79),
    ((.c19, .n2, .big), tree80),
    ((.c19, .big, .big), tree81),
    ((.c31, .c37, .c43), tree82),
    ((.c31, .c37, .n2), tree83),
    ((.c31, .c37, .big), tree84),
    ((.c31, .c43, .n2), tree85),
    ((.c31, .c43, .big), tree86),
    ((.c31, .n2, .n2), tree87),
    ((.c31, .n2, .big), tree88),
    ((.c31, .big, .big), tree89),
    ((.c37, .c43, .n2), tree90),
    ((.c37, .c43, .big), tree91),
    ((.c37, .n2, .n2), tree92),
    ((.c37, .n2, .big), tree93),
    ((.c37, .big, .big), tree94),
    ((.c43, .n2, .n2), tree95),
    ((.c43, .n2, .big), tree96),
    ((.c43, .big, .big), tree97),
    ((.n2, .n2, .n2), tree98),
    ((.n2, .n2, .big), tree99),
    ((.n2, .big, .big), tree100),
    ((.big, .big, .big), tree101)]

private theorem forall_cons {P : ClassTriple × Tree → Prop} {a : ClassTriple × Tree}
    {l : List (ClassTriple × Tree)} (ha : P a) (hl : ∀ e ∈ l, P e) : ∀ e ∈ a :: l, P e :=
  List.forall_mem_cons.mpr ⟨ha, hl⟩

private theorem trees_fst : trees.map Prod.fst = triples := by decide +kernel

private theorem trees_ok : ∀ e ∈ trees, treeOK e.1 (rootNode e.1) e.2 = true :=
  forall_cons tree0_ok
    (forall_cons tree1_ok
    (forall_cons tree2_ok
    (forall_cons tree3_ok
    (forall_cons tree4_ok
    (forall_cons tree5_ok
    (forall_cons tree6_ok
    (forall_cons tree7_ok
    (forall_cons tree8_ok
    (forall_cons tree9_ok
    (forall_cons tree10_ok
    (forall_cons tree11_ok
    (forall_cons tree12_ok
    (forall_cons tree13_ok
    (forall_cons tree14_ok
    (forall_cons tree15_ok
    (forall_cons tree16_ok
    (forall_cons tree17_ok
    (forall_cons tree18_ok
    (forall_cons tree19_ok
    (forall_cons tree20_ok
    (forall_cons tree21_ok
    (forall_cons tree22_ok
    (forall_cons tree23_ok
    (forall_cons tree24_ok
    (forall_cons tree25_ok
    (forall_cons tree26_ok
    (forall_cons tree27_ok
    (forall_cons tree28_ok
    (forall_cons tree29_ok
    (forall_cons tree30_ok
    (forall_cons tree31_ok
    (forall_cons tree32_ok
    (forall_cons tree33_ok
    (forall_cons tree34_ok
    (forall_cons tree35_ok
    (forall_cons tree36_ok
    (forall_cons tree37_ok
    (forall_cons tree38_ok
    (forall_cons tree39_ok
    (forall_cons tree40_ok
    (forall_cons tree41_ok
    (forall_cons tree42_ok
    (forall_cons tree43_ok
    (forall_cons tree44_ok
    (forall_cons tree45_ok
    (forall_cons tree46_ok
    (forall_cons tree47_ok
    (forall_cons tree48_ok
    (forall_cons tree49_ok
    (forall_cons tree50_ok
    (forall_cons tree51_ok
    (forall_cons tree52_ok
    (forall_cons tree53_ok
    (forall_cons tree54_ok
    (forall_cons tree55_ok
    (forall_cons tree56_ok
    (forall_cons tree57_ok
    (forall_cons tree58_ok
    (forall_cons tree59_ok
    (forall_cons tree60_ok
    (forall_cons tree61_ok
    (forall_cons tree62_ok
    (forall_cons tree63_ok
    (forall_cons tree64_ok
    (forall_cons tree65_ok
    (forall_cons tree66_ok
    (forall_cons tree67_ok
    (forall_cons tree68_ok
    (forall_cons tree69_ok
    (forall_cons tree70_ok
    (forall_cons tree71_ok
    (forall_cons tree72_ok
    (forall_cons tree73_ok
    (forall_cons tree74_ok
    (forall_cons tree75_ok
    (forall_cons tree76_ok
    (forall_cons tree77_ok
    (forall_cons tree78_ok
    (forall_cons tree79_ok
    (forall_cons tree80_ok
    (forall_cons tree81_ok
    (forall_cons tree82_ok
    (forall_cons tree83_ok
    (forall_cons tree84_ok
    (forall_cons tree85_ok
    (forall_cons tree86_ok
    (forall_cons tree87_ok
    (forall_cons tree88_ok
    (forall_cons tree89_ok
    (forall_cons tree90_ok
    (forall_cons tree91_ok
    (forall_cons tree92_ok
    (forall_cons tree93_ok
    (forall_cons tree94_ok
    (forall_cons tree95_ok
    (forall_cons tree96_ok
    (forall_cons tree97_ok
    (forall_cons tree98_ok
    (forall_cons tree99_ok
    (forall_cons tree100_ok
    (forall_cons tree101_ok
    ((fun _ h => absurd h List.not_mem_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The check of all trees, assembled from the separate tree checks. -/
theorem allOK_trees : allOK trees = true :=
  allOK_of fun t ht => by
    rw [← trees_fst] at ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    exact ⟨e.2, he, trees_ok e he⟩

end ThreeFreeThree

/-- An odd perfect number `N` with special prime `q`, in which every prime factor `p` other than
`q` and three further numbers `r₁`, `r₂`, `r₃` has an exponent `e = N.factorization p` with
`3 ∣ e + 1`, is divisible by 3. Here `r₁, r₂, r₃` are arbitrary natural numbers: they need not
be distinct, prime, or divisors of `N`, so the cases of fewer exceptional primes are included.
The case analysis behind the proof was found by a search outside Lean and is rechecked by the
kernel. -/
theorem three_dvd_of_three_mod_exceptions {N q r₁ r₂ r₃ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hmod : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → 3 ∣ N.factorization p + 1) :
    3 ∣ N :=
  ThreeFreeThree.three_dvd_of_three_exceptions_of_check ThreeFreeThree.trees
    ThreeFreeThree.allOK_trees h hq hodd hmod

/-- An odd perfect number in which every prime factor other than the special prime `q` and
three further primes `r₁`, `r₂`, `r₃` has exponent exactly 2 is divisible by 3. Here
`r₁, r₂, r₃` are arbitrary natural numbers: they need not be distinct, prime, or divisors of
`N`, so the cases of fewer exceptional primes are included. This is the case `e = 2` of
`three_dvd_of_three_mod_exceptions`. -/
theorem three_dvd_of_three_exceptions {N q r₁ r₂ r₃ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → N.factorization p = 2) :
    3 ∣ N :=
  three_dvd_of_three_mod_exceptions (r₁ := r₁) (r₂ := r₂) (r₃ := r₃) h hq hodd
    fun p hp h0 h1 h2 h3 => by simp [hsq p hp h0 h1 h2 h3]

/-- The counting form of `three_dvd_of_three_mod_exceptions`: if `N` is an odd perfect number
with special prime `q` and `3 ∤ N`, then at least four prime factors `p ≠ q` of `N` have an
exponent `e = N.factorization p` with `3 ∤ e + 1`. -/
theorem four_le_card_mod_exceptions {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N) :
    4 ≤ ((N.primeFactors.erase q).filter fun p => ¬ 3 ∣ N.factorization p + 1).card := by
  by_contra hc
  set B := (N.primeFactors.erase q).filter fun p => ¬ 3 ∣ N.factorization p + 1
  have hB : B.card ≤ 3 := by omega
  have hU : 3 ≤ (B ∪ {0, 1, 2}).card :=
    le_trans (by decide) (Finset.card_le_card Finset.subset_union_right)
  obtain ⟨R, hBR, -, hR⟩ := Finset.exists_subsuperset_card_eq Finset.subset_union_left hB hU
  obtain ⟨a, b, d, -, -, -, rfl⟩ := Finset.card_eq_three.mp hR
  apply h3
  refine three_dvd_of_three_mod_exceptions (r₁ := a) (r₂ := b) (r₃ := d) h hq hodd
    fun p hp hpq ha hb hd => ?_
  by_contra hn
  have hm := hBR (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpq, hp⟩, hn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  tauto

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.allOK_trees
#print axioms OddPerfect.three_dvd_of_three_mod_exceptions
#print axioms OddPerfect.three_dvd_of_three_exceptions
#print axioms OddPerfect.four_le_card_mod_exceptions
