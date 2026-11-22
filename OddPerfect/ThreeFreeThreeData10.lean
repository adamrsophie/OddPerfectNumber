import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 10

Subtrees of the case analysis certificate for the class triples `(13, 31, big)`,
`(13, 37, 43)`, `(13, 37, n2)`, `(13, 37, big)`, `(13, 43, n2)`, `(13, 43, big)`, `(13, n2, n2)`,
`(13, n2, big)`, `(13, big, big)`, `(19, 31, 37)`, `(19, 31, 43)`, `(19, 31, n2)`,
`(19, 31, big)`, `(19, 37, 43)`, `(19, 37, n2)`, `(19, 37, big)`, `(19, 43, n2)`, `(19, 43, big)`,
`(19, n2, n2)`, `(19, n2, big)`, `(19, big, big)`, `(31, 37, 43)`, `(31, 37, n2)`,
`(31, 37, big)`, `(31, 43, n2)`, `(31, 43, big)`, `(31, n2, n2)`, `(31, n2, big)`, with 127
leaves in all. Each public theorem states that a subtree passes `treeOK` from explicit
constraints. The data was found by a search outside Lean; everything in this file is
rechecked by the kernel through `decide +kernel` on the leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u61_0_g0 :
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 61⟩ ⟨(1, 5), (109, 393), (155, 863), (79, 617)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 67⟩ ⟨(1, 5), (109, 393), (155, 863), (27, 221)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 73⟩ ⟨(1, 5), (109, 393), (155, 863), (57, 487)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 109⟩ ⟨(1, 5), (109, 393), (155, 863), (25, 261)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 151⟩ ⟨(1, 5), (109, 393), (155, 863), (59, 725)⟩))))) = true := by
  decide +kernel

private theorem u61_0_g1 :
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 307⟩ ⟨(1, 5), (109, 393), (155, 863), (48, 841)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 709⟩ ⟨(1, 5), (109, 393), (155, 863), (8, 213)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 727⟩ ⟨(1, 5), (109, 393), (155, 863), (26, 701)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 991⟩ ⟨(1, 5), (109, 393), (155, 863), (25, 787)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 1087⟩ ⟨(1, 5), (109, 393), (155, 863), (30, 989)⟩))))) = true := by
  decide +kernel

private theorem u61_0_g2 :
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 1723⟩ ⟨(1, 5), (109, 393), (155, 863), (2, 83)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 3541⟩ ⟨(1, 5), (109, 393), (155, 863), (2, 119)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 5113⟩ ⟨(1, 5), (109, 393), (155, 863), (2, 143)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 8011⟩ ⟨(1, 5), (109, 393), (155, 863), (2, 179)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 10303⟩ ⟨(1, 5), (109, 393), (155, 863), (2, 203)⟩))))) = true := by
  decide +kernel

private theorem u61_0_g3 :
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 17293⟩ ⟨(1, 5), (109, 393), (155, 863), (2, 263)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 28057⟩ ⟨(1, 5), (109, 393), (155, 863), (2, 335)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 30103⟩ ⟨(1, 5), (109, 393), (155, 863), (2, 347)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .pin 86143⟩ ⟨(1, 5), (109, 393), (155, 863), (2, 587)⟩ &&
    (leafOK (.c13, .c31, .big) ⟨.free .q 13 [], .pin 13, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61]⟩ ⟨(1, 5), (109, 393), (155, 863), (1, 8)⟩))))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(13, 31, big)`, with 20 leaves. -/
def u61_0 : Tree :=
  .split 3 61
    (.leaf ⟨(1, 5), (109, 393), (155, 863), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(1, 5), (109, 393), (155, 863), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(1, 5), (109, 393), (155, 863), (57, 487)⟩)
        (.split 3 109
          (.leaf ⟨(1, 5), (109, 393), (155, 863), (25, 261)⟩)
          (.split 3 151
            (.leaf ⟨(1, 5), (109, 393), (155, 863), (59, 725)⟩)
            (.split 3 307
              (.leaf ⟨(1, 5), (109, 393), (155, 863), (48, 841)⟩)
              (.split 3 709
                (.leaf ⟨(1, 5), (109, 393), (155, 863), (8, 213)⟩)
                (.split 3 727
                  (.leaf ⟨(1, 5), (109, 393), (155, 863), (26, 701)⟩)
                  (.split 3 991
                    (.leaf ⟨(1, 5), (109, 393), (155, 863), (25, 787)⟩)
                    (.split 3 1087
                      (.leaf ⟨(1, 5), (109, 393), (155, 863), (30, 989)⟩)
                      (.split 3 1723
                        (.leaf ⟨(1, 5), (109, 393), (155, 863), (2, 83)⟩)
                        (.split 3 3541
                          (.leaf ⟨(1, 5), (109, 393), (155, 863), (2, 119)⟩)
                          (.split 3 5113
                            (.leaf ⟨(1, 5), (109, 393), (155, 863), (2, 143)⟩)
                            (.split 3 8011
                              (.leaf ⟨(1, 5), (109, 393), (155, 863), (2, 179)⟩)
                              (.split 3 10303
                                (.leaf ⟨(1, 5), (109, 393), (155, 863), (2, 203)⟩)
                                (.split 3 17293
                                  (.leaf ⟨(1, 5), (109, 393), (155, 863), (2, 263)⟩)
                                  (.split 3 28057
                                    (.leaf ⟨(1, 5), (109, 393), (155, 863), (2, 335)⟩)
                                    (.split 3 30103
                                      (.leaf ⟨(1, 5), (109, 393), (155, 863), (2, 347)⟩)
                                      (.split 3 86143
                                        (.leaf ⟨(1, 5), (109, 393), (155, 863), (2, 587)⟩)
                                        (.leaf ⟨(1, 5), (109, 393), (155, 863), (1, 8)⟩)))))))))))))))))))

/-- Subtree 0 of the class triple `(13, 31, big)` passes the check. -/
theorem u61_0_ok : treeOK (.c13, .c31, .big)
    (rootNode (.c13, .c31, .big)) u61_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u61_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u61_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u61_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u61_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g3).2).2).2).1)
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u61_0_g3).2).2).2).2)))))))))))))))))))

private theorem u62_0_g0 :
    leafOK (.c13, .c37, .c43) ⟨.free .q 13 [], .pin 13, .pin 37, .pin 43⟩ ⟨(1, 5), (109, 393), (145, 882), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(13, 37, 43)`, with 1 leaves. -/
def u62_0 : Tree :=
  .leaf ⟨(1, 5), (109, 393), (145, 882), (61, 400)⟩

/-- Subtree 0 of the class triple `(13, 37, 43)` passes the check. -/
theorem u62_0_ok : treeOK (.c13, .c37, .c43)
    (rootNode (.c13, .c37, .c43)) u62_0 = true :=
  treeOK_leaf u62_0_g0

private theorem u63_0_g0 :
    leafOK (.c13, .c37, .n2) ⟨.free .q 13 [], .pin 13, .pin 37, .free .n2 11 []⟩ ⟨(1, 5), (109, 393), (145, 882), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(13, 37, n2)`, with 1 leaves. -/
def u63_0 : Tree :=
  .leaf ⟨(1, 5), (109, 393), (145, 882), (0, 1)⟩

/-- Subtree 0 of the class triple `(13, 37, n2)` passes the check. -/
theorem u63_0_ok : treeOK (.c13, .c37, .n2)
    (rootNode (.c13, .c37, .n2)) u63_0 = true :=
  treeOK_leaf u63_0_g0

private theorem u64_0_g0 :
    leafOK (.c13, .c37, .big) ⟨.free .q 13 [], .pin 13, .pin 37, .free .big 61 []⟩ ⟨(1, 5), (109, 393), (145, 882), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(13, 37, big)`, with 1 leaves. -/
def u64_0 : Tree :=
  .leaf ⟨(1, 5), (109, 393), (145, 882), (79, 617)⟩

/-- Subtree 0 of the class triple `(13, 37, big)` passes the check. -/
theorem u64_0_ok : treeOK (.c13, .c37, .big)
    (rootNode (.c13, .c37, .big)) u64_0 = true :=
  treeOK_leaf u64_0_g0

private theorem u65_0_g0 :
    leafOK (.c13, .c43, .n2) ⟨.free .q 13 [], .pin 13, .pin 43, .free .n2 11 []⟩ ⟨(1, 5), (109, 393), (61, 400), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(13, 43, n2)`, with 1 leaves. -/
def u65_0 : Tree :=
  .leaf ⟨(1, 5), (109, 393), (61, 400), (0, 1)⟩

/-- Subtree 0 of the class triple `(13, 43, n2)` passes the check. -/
theorem u65_0_ok : treeOK (.c13, .c43, .n2)
    (rootNode (.c13, .c43, .n2)) u65_0 = true :=
  treeOK_leaf u65_0_g0

private theorem u66_0_g0 :
    leafOK (.c13, .c43, .big) ⟨.free .q 13 [], .pin 13, .pin 43, .free .big 61 []⟩ ⟨(1, 5), (109, 393), (61, 400), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(13, 43, big)`, with 1 leaves. -/
def u66_0 : Tree :=
  .leaf ⟨(1, 5), (109, 393), (61, 400), (79, 617)⟩

/-- Subtree 0 of the class triple `(13, 43, big)` passes the check. -/
theorem u66_0_ok : treeOK (.c13, .c43, .big)
    (rootNode (.c13, .c43, .big)) u66_0 = true :=
  treeOK_leaf u66_0_g0

private theorem u67_0_g0 :
    leafOK (.c13, .n2, .n2) ⟨.free .q 13 [], .pin 13, .free .n2 11 [], .free .n2 11 []⟩ ⟨(1, 5), (109, 393), (0, 1), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(13, n2, n2)`, with 1 leaves. -/
def u67_0 : Tree :=
  .leaf ⟨(1, 5), (109, 393), (0, 1), (0, 1)⟩

/-- Subtree 0 of the class triple `(13, n2, n2)` passes the check. -/
theorem u67_0_ok : treeOK (.c13, .n2, .n2)
    (rootNode (.c13, .n2, .n2)) u67_0 = true :=
  treeOK_leaf u67_0_g0

private theorem u68_0_g0 :
    leafOK (.c13, .n2, .big) ⟨.free .q 13 [], .pin 13, .free .n2 11 [], .free .big 61 []⟩ ⟨(1, 5), (109, 393), (0, 1), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(13, n2, big)`, with 1 leaves. -/
def u68_0 : Tree :=
  .leaf ⟨(1, 5), (109, 393), (0, 1), (79, 617)⟩

/-- Subtree 0 of the class triple `(13, n2, big)` passes the check. -/
theorem u68_0_ok : treeOK (.c13, .n2, .big)
    (rootNode (.c13, .n2, .big)) u68_0 = true :=
  treeOK_leaf u68_0_g0

private theorem u69_0_g0 :
    leafOK (.c13, .big, .big) ⟨.free .q 13 [], .pin 13, .free .big 61 [], .free .big 61 []⟩ ⟨(1, 5), (109, 393), (79, 617), (1, 8)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(13, big, big)`, with 1 leaves. -/
def u69_0 : Tree :=
  .leaf ⟨(1, 5), (109, 393), (79, 617), (1, 8)⟩

/-- Subtree 0 of the class triple `(13, big, big)` passes the check. -/
theorem u69_0_ok : treeOK (.c13, .big, .big)
    (rootNode (.c13, .big, .big)) u69_0 = true :=
  treeOK_leaf u69_0_g0

private theorem u70_0_g0 :
    leafOK (.c19, .c31, .c37) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 37⟩ ⟨(109, 393), (209, 911), (155, 863), (145, 882)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, 31, 37)`, with 1 leaves. -/
def u70_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (155, 863), (145, 882)⟩

/-- Subtree 0 of the class triple `(19, 31, 37)` passes the check. -/
theorem u70_0_ok : treeOK (.c19, .c31, .c37)
    (rootNode (.c19, .c31, .c37)) u70_0 = true :=
  treeOK_leaf u70_0_g0

private theorem u71_0_g0 :
    leafOK (.c19, .c31, .c43) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 43⟩ ⟨(109, 393), (209, 911), (155, 863), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, 31, 43)`, with 1 leaves. -/
def u71_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (155, 863), (61, 400)⟩

/-- Subtree 0 of the class triple `(19, 31, 43)` passes the check. -/
theorem u71_0_ok : treeOK (.c19, .c31, .c43)
    (rootNode (.c19, .c31, .c43)) u71_0 = true :=
  treeOK_leaf u71_0_g0

private theorem u72_0_g0 :
    leafOK (.c19, .c31, .n2) ⟨.free .q 13 [], .pin 19, .pin 31, .free .n2 11 []⟩ ⟨(109, 393), (209, 911), (155, 863), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, 31, n2)`, with 1 leaves. -/
def u72_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (155, 863), (0, 1)⟩

/-- Subtree 0 of the class triple `(19, 31, n2)` passes the check. -/
theorem u72_0_ok : treeOK (.c19, .c31, .n2)
    (rootNode (.c19, .c31, .n2)) u72_0 = true :=
  treeOK_leaf u72_0_g0

private theorem u73_0_g0 :
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 61⟩ ⟨(109, 393), (209, 911), (155, 863), (79, 617)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 67⟩ ⟨(109, 393), (209, 911), (155, 863), (27, 221)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 73⟩ ⟨(109, 393), (209, 911), (155, 863), (57, 487)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 109⟩ ⟨(109, 393), (209, 911), (155, 863), (25, 261)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 151⟩ ⟨(109, 393), (209, 911), (155, 863), (59, 725)⟩))))) = true := by
  decide +kernel

private theorem u73_0_g1 :
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 307⟩ ⟨(109, 393), (209, 911), (155, 863), (48, 841)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 367⟩ ⟨(109, 393), (209, 911), (155, 863), (51, 977)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 709⟩ ⟨(109, 393), (209, 911), (155, 863), (8, 213)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 727⟩ ⟨(109, 393), (209, 911), (155, 863), (26, 701)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 991⟩ ⟨(109, 393), (209, 911), (155, 863), (25, 787)⟩))))) = true := by
  decide +kernel

private theorem u73_0_g2 :
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 1087⟩ ⟨(109, 393), (209, 911), (155, 863), (30, 989)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 1723⟩ ⟨(109, 393), (209, 911), (155, 863), (2, 83)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 2053⟩ ⟨(109, 393), (209, 911), (155, 863), (13, 589)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 3019⟩ ⟨(109, 393), (209, 911), (155, 863), (18, 989)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 3541⟩ ⟨(109, 393), (209, 911), (155, 863), (2, 119)⟩))))) = true := by
  decide +kernel

private theorem u73_0_g3 :
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 5113⟩ ⟨(109, 393), (209, 911), (155, 863), (2, 143)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 8011⟩ ⟨(109, 393), (209, 911), (155, 863), (2, 179)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 10303⟩ ⟨(109, 393), (209, 911), (155, 863), (2, 203)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 17293⟩ ⟨(109, 393), (209, 911), (155, 863), (2, 263)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 28057⟩ ⟨(109, 393), (209, 911), (155, 863), (2, 335)⟩))))) = true := by
  decide +kernel

private theorem u73_0_g4 :
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 30103⟩ ⟨(109, 393), (209, 911), (155, 863), (2, 347)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .pin 86143⟩ ⟨(109, 393), (209, 911), (155, 863), (2, 587)⟩ &&
    (leafOK (.c19, .c31, .big) ⟨.free .q 13 [], .pin 19, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 367, 307, 151, 109, 73, 67, 61]⟩ ⟨(109, 393), (209, 911), (155, 863), (1, 8)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, 31, big)`, with 23 leaves. -/
def u73_0 : Tree :=
  .split 3 61
    (.leaf ⟨(109, 393), (209, 911), (155, 863), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(109, 393), (209, 911), (155, 863), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(109, 393), (209, 911), (155, 863), (57, 487)⟩)
        (.split 3 109
          (.leaf ⟨(109, 393), (209, 911), (155, 863), (25, 261)⟩)
          (.split 3 151
            (.leaf ⟨(109, 393), (209, 911), (155, 863), (59, 725)⟩)
            (.split 3 307
              (.leaf ⟨(109, 393), (209, 911), (155, 863), (48, 841)⟩)
              (.split 3 367
                (.leaf ⟨(109, 393), (209, 911), (155, 863), (51, 977)⟩)
                (.split 3 709
                  (.leaf ⟨(109, 393), (209, 911), (155, 863), (8, 213)⟩)
                  (.split 3 727
                    (.leaf ⟨(109, 393), (209, 911), (155, 863), (26, 701)⟩)
                    (.split 3 991
                      (.leaf ⟨(109, 393), (209, 911), (155, 863), (25, 787)⟩)
                      (.split 3 1087
                        (.leaf ⟨(109, 393), (209, 911), (155, 863), (30, 989)⟩)
                        (.split 3 1723
                          (.leaf ⟨(109, 393), (209, 911), (155, 863), (2, 83)⟩)
                          (.split 3 2053
                            (.leaf ⟨(109, 393), (209, 911), (155, 863), (13, 589)⟩)
                            (.split 3 3019
                              (.leaf ⟨(109, 393), (209, 911), (155, 863), (18, 989)⟩)
                              (.split 3 3541
                                (.leaf ⟨(109, 393), (209, 911), (155, 863), (2, 119)⟩)
                                (.split 3 5113
                                  (.leaf ⟨(109, 393), (209, 911), (155, 863), (2, 143)⟩)
                                  (.split 3 8011
                                    (.leaf ⟨(109, 393), (209, 911), (155, 863), (2, 179)⟩)
                                    (.split 3 10303
                                      (.leaf ⟨(109, 393), (209, 911), (155, 863), (2, 203)⟩)
                                      (.split 3 17293
                                        (.leaf ⟨(109, 393), (209, 911), (155, 863), (2, 263)⟩)
                                        (.split 3 28057
                                          (.leaf ⟨(109, 393), (209, 911), (155, 863), (2, 335)⟩)
                                          (.split 3 30103
                                            (.leaf ⟨(109, 393), (209, 911), (155, 863), (2, 347)⟩)
                                            (.split 3 86143
                                              (.leaf ⟨(109, 393), (209, 911), (155, 863), (2, 587)⟩)
                                              (.leaf ⟨(109, 393), (209, 911), (155, 863), (1, 8)⟩))))))))))))))))))))))

/-- Subtree 0 of the class triple `(19, 31, big)` passes the check. -/
theorem u73_0_ok : treeOK (.c19, .c31, .big)
    (rootNode (.c19, .c31, .big)) u73_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u73_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u73_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u73_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u73_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g3).2).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g3).2).2).2).2)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp u73_0_g4).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g4).2).1)
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u73_0_g4).2).2))))))))))))))))))))))

private theorem u74_0_g0 :
    leafOK (.c19, .c37, .c43) ⟨.free .q 13 [], .pin 19, .pin 37, .pin 43⟩ ⟨(109, 393), (209, 911), (145, 882), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, 37, 43)`, with 1 leaves. -/
def u74_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (145, 882), (61, 400)⟩

/-- Subtree 0 of the class triple `(19, 37, 43)` passes the check. -/
theorem u74_0_ok : treeOK (.c19, .c37, .c43)
    (rootNode (.c19, .c37, .c43)) u74_0 = true :=
  treeOK_leaf u74_0_g0

private theorem u75_0_g0 :
    leafOK (.c19, .c37, .n2) ⟨.free .q 13 [], .pin 19, .pin 37, .free .n2 11 []⟩ ⟨(109, 393), (209, 911), (145, 882), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, 37, n2)`, with 1 leaves. -/
def u75_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (145, 882), (0, 1)⟩

/-- Subtree 0 of the class triple `(19, 37, n2)` passes the check. -/
theorem u75_0_ok : treeOK (.c19, .c37, .n2)
    (rootNode (.c19, .c37, .n2)) u75_0 = true :=
  treeOK_leaf u75_0_g0

private theorem u76_0_g0 :
    leafOK (.c19, .c37, .big) ⟨.free .q 13 [], .pin 19, .pin 37, .free .big 61 []⟩ ⟨(109, 393), (209, 911), (145, 882), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, 37, big)`, with 1 leaves. -/
def u76_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (145, 882), (79, 617)⟩

/-- Subtree 0 of the class triple `(19, 37, big)` passes the check. -/
theorem u76_0_ok : treeOK (.c19, .c37, .big)
    (rootNode (.c19, .c37, .big)) u76_0 = true :=
  treeOK_leaf u76_0_g0

private theorem u77_0_g0 :
    leafOK (.c19, .c43, .n2) ⟨.free .q 13 [], .pin 19, .pin 43, .free .n2 11 []⟩ ⟨(109, 393), (209, 911), (61, 400), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, 43, n2)`, with 1 leaves. -/
def u77_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (61, 400), (0, 1)⟩

/-- Subtree 0 of the class triple `(19, 43, n2)` passes the check. -/
theorem u77_0_ok : treeOK (.c19, .c43, .n2)
    (rootNode (.c19, .c43, .n2)) u77_0 = true :=
  treeOK_leaf u77_0_g0

private theorem u78_0_g0 :
    leafOK (.c19, .c43, .big) ⟨.free .q 13 [], .pin 19, .pin 43, .free .big 61 []⟩ ⟨(109, 393), (209, 911), (61, 400), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, 43, big)`, with 1 leaves. -/
def u78_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (61, 400), (79, 617)⟩

/-- Subtree 0 of the class triple `(19, 43, big)` passes the check. -/
theorem u78_0_ok : treeOK (.c19, .c43, .big)
    (rootNode (.c19, .c43, .big)) u78_0 = true :=
  treeOK_leaf u78_0_g0

private theorem u79_0_g0 :
    leafOK (.c19, .n2, .n2) ⟨.free .q 13 [], .pin 19, .free .n2 11 [], .free .n2 11 []⟩ ⟨(109, 393), (209, 911), (0, 1), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, n2, n2)`, with 1 leaves. -/
def u79_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (0, 1), (0, 1)⟩

/-- Subtree 0 of the class triple `(19, n2, n2)` passes the check. -/
theorem u79_0_ok : treeOK (.c19, .n2, .n2)
    (rootNode (.c19, .n2, .n2)) u79_0 = true :=
  treeOK_leaf u79_0_g0

private theorem u80_0_g0 :
    leafOK (.c19, .n2, .big) ⟨.free .q 13 [], .pin 19, .free .n2 11 [], .free .big 61 []⟩ ⟨(109, 393), (209, 911), (0, 1), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, n2, big)`, with 1 leaves. -/
def u80_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (0, 1), (79, 617)⟩

/-- Subtree 0 of the class triple `(19, n2, big)` passes the check. -/
theorem u80_0_ok : treeOK (.c19, .n2, .big)
    (rootNode (.c19, .n2, .big)) u80_0 = true :=
  treeOK_leaf u80_0_g0

private theorem u81_0_g0 :
    leafOK (.c19, .big, .big) ⟨.free .q 13 [], .pin 19, .free .big 61 [], .free .big 61 []⟩ ⟨(109, 393), (209, 911), (79, 617), (1, 8)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(19, big, big)`, with 1 leaves. -/
def u81_0 : Tree :=
  .leaf ⟨(109, 393), (209, 911), (79, 617), (1, 8)⟩

/-- Subtree 0 of the class triple `(19, big, big)` passes the check. -/
theorem u81_0_ok : treeOK (.c19, .big, .big)
    (rootNode (.c19, .big, .big)) u81_0 = true :=
  treeOK_leaf u81_0_g0

private theorem u82_0_g0 :
    leafOK (.c31, .c37, .c43) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 43⟩ ⟨(109, 393), (155, 863), (145, 882), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(31, 37, 43)`, with 1 leaves. -/
def u82_0 : Tree :=
  .leaf ⟨(109, 393), (155, 863), (145, 882), (61, 400)⟩

/-- Subtree 0 of the class triple `(31, 37, 43)` passes the check. -/
theorem u82_0_ok : treeOK (.c31, .c37, .c43)
    (rootNode (.c31, .c37, .c43)) u82_0 = true :=
  treeOK_leaf u82_0_g0

private theorem u83_0_g0 :
    leafOK (.c31, .c37, .n2) ⟨.free .q 13 [], .pin 31, .pin 37, .free .n2 11 []⟩ ⟨(109, 393), (155, 863), (145, 882), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(31, 37, n2)`, with 1 leaves. -/
def u83_0 : Tree :=
  .leaf ⟨(109, 393), (155, 863), (145, 882), (0, 1)⟩

/-- Subtree 0 of the class triple `(31, 37, n2)` passes the check. -/
theorem u83_0_ok : treeOK (.c31, .c37, .n2)
    (rootNode (.c31, .c37, .n2)) u83_0 = true :=
  treeOK_leaf u83_0_g0

private theorem u84_0_g0 :
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 61⟩ ⟨(109, 393), (155, 863), (145, 882), (79, 617)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 67⟩ ⟨(109, 393), (155, 863), (145, 882), (27, 221)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 73⟩ ⟨(109, 393), (155, 863), (145, 882), (57, 487)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 109⟩ ⟨(109, 393), (155, 863), (145, 882), (25, 261)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 151⟩ ⟨(109, 393), (155, 863), (145, 882), (59, 725)⟩))))) = true := by
  decide +kernel

private theorem u84_0_g1 :
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 307⟩ ⟨(109, 393), (155, 863), (145, 882), (48, 841)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 709⟩ ⟨(109, 393), (155, 863), (145, 882), (8, 213)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 727⟩ ⟨(109, 393), (155, 863), (145, 882), (26, 701)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 991⟩ ⟨(109, 393), (155, 863), (145, 882), (25, 787)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 1087⟩ ⟨(109, 393), (155, 863), (145, 882), (30, 989)⟩))))) = true := by
  decide +kernel

private theorem u84_0_g2 :
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 1723⟩ ⟨(109, 393), (155, 863), (145, 882), (2, 83)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 3541⟩ ⟨(109, 393), (155, 863), (145, 882), (2, 119)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 5113⟩ ⟨(109, 393), (155, 863), (145, 882), (2, 143)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 8011⟩ ⟨(109, 393), (155, 863), (145, 882), (2, 179)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 10303⟩ ⟨(109, 393), (155, 863), (145, 882), (2, 203)⟩))))) = true := by
  decide +kernel

private theorem u84_0_g3 :
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 17293⟩ ⟨(109, 393), (155, 863), (145, 882), (2, 263)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 28057⟩ ⟨(109, 393), (155, 863), (145, 882), (2, 335)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 30103⟩ ⟨(109, 393), (155, 863), (145, 882), (2, 347)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .pin 86143⟩ ⟨(109, 393), (155, 863), (145, 882), (2, 587)⟩ &&
    (leafOK (.c31, .c37, .big) ⟨.free .q 13 [], .pin 31, .pin 37, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61]⟩ ⟨(109, 393), (155, 863), (145, 882), (1, 8)⟩))))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(31, 37, big)`, with 20 leaves. -/
def u84_0 : Tree :=
  .split 3 61
    (.leaf ⟨(109, 393), (155, 863), (145, 882), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(109, 393), (155, 863), (145, 882), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(109, 393), (155, 863), (145, 882), (57, 487)⟩)
        (.split 3 109
          (.leaf ⟨(109, 393), (155, 863), (145, 882), (25, 261)⟩)
          (.split 3 151
            (.leaf ⟨(109, 393), (155, 863), (145, 882), (59, 725)⟩)
            (.split 3 307
              (.leaf ⟨(109, 393), (155, 863), (145, 882), (48, 841)⟩)
              (.split 3 709
                (.leaf ⟨(109, 393), (155, 863), (145, 882), (8, 213)⟩)
                (.split 3 727
                  (.leaf ⟨(109, 393), (155, 863), (145, 882), (26, 701)⟩)
                  (.split 3 991
                    (.leaf ⟨(109, 393), (155, 863), (145, 882), (25, 787)⟩)
                    (.split 3 1087
                      (.leaf ⟨(109, 393), (155, 863), (145, 882), (30, 989)⟩)
                      (.split 3 1723
                        (.leaf ⟨(109, 393), (155, 863), (145, 882), (2, 83)⟩)
                        (.split 3 3541
                          (.leaf ⟨(109, 393), (155, 863), (145, 882), (2, 119)⟩)
                          (.split 3 5113
                            (.leaf ⟨(109, 393), (155, 863), (145, 882), (2, 143)⟩)
                            (.split 3 8011
                              (.leaf ⟨(109, 393), (155, 863), (145, 882), (2, 179)⟩)
                              (.split 3 10303
                                (.leaf ⟨(109, 393), (155, 863), (145, 882), (2, 203)⟩)
                                (.split 3 17293
                                  (.leaf ⟨(109, 393), (155, 863), (145, 882), (2, 263)⟩)
                                  (.split 3 28057
                                    (.leaf ⟨(109, 393), (155, 863), (145, 882), (2, 335)⟩)
                                    (.split 3 30103
                                      (.leaf ⟨(109, 393), (155, 863), (145, 882), (2, 347)⟩)
                                      (.split 3 86143
                                        (.leaf ⟨(109, 393), (155, 863), (145, 882), (2, 587)⟩)
                                        (.leaf ⟨(109, 393), (155, 863), (145, 882), (1, 8)⟩)))))))))))))))))))

/-- Subtree 0 of the class triple `(31, 37, big)` passes the check. -/
theorem u84_0_ok : treeOK (.c31, .c37, .big)
    (rootNode (.c31, .c37, .big)) u84_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u84_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u84_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u84_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u84_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g3).2).2).2).1)
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u84_0_g3).2).2).2).2)))))))))))))))))))

private theorem u85_0_g0 :
    leafOK (.c31, .c43, .n2) ⟨.free .q 13 [], .pin 31, .pin 43, .free .n2 11 []⟩ ⟨(109, 393), (155, 863), (61, 400), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(31, 43, n2)`, with 1 leaves. -/
def u85_0 : Tree :=
  .leaf ⟨(109, 393), (155, 863), (61, 400), (0, 1)⟩

/-- Subtree 0 of the class triple `(31, 43, n2)` passes the check. -/
theorem u85_0_ok : treeOK (.c31, .c43, .n2)
    (rootNode (.c31, .c43, .n2)) u85_0 = true :=
  treeOK_leaf u85_0_g0

private theorem u86_0_g0 :
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 61⟩ ⟨(109, 393), (155, 863), (61, 400), (79, 617)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 67⟩ ⟨(109, 393), (155, 863), (61, 400), (27, 221)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 73⟩ ⟨(109, 393), (155, 863), (61, 400), (57, 487)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 109⟩ ⟨(109, 393), (155, 863), (61, 400), (25, 261)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 151⟩ ⟨(109, 393), (155, 863), (61, 400), (59, 725)⟩))))) = true := by
  decide +kernel

private theorem u86_0_g1 :
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 307⟩ ⟨(109, 393), (155, 863), (61, 400), (48, 841)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 709⟩ ⟨(109, 393), (155, 863), (61, 400), (8, 213)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 727⟩ ⟨(109, 393), (155, 863), (61, 400), (26, 701)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 991⟩ ⟨(109, 393), (155, 863), (61, 400), (25, 787)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 1087⟩ ⟨(109, 393), (155, 863), (61, 400), (30, 989)⟩))))) = true := by
  decide +kernel

private theorem u86_0_g2 :
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 1471⟩ ⟨(109, 393), (155, 863), (61, 400), (17, 652)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 1723⟩ ⟨(109, 393), (155, 863), (61, 400), (2, 83)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 3541⟩ ⟨(109, 393), (155, 863), (61, 400), (2, 119)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 5113⟩ ⟨(109, 393), (155, 863), (61, 400), (2, 143)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 8011⟩ ⟨(109, 393), (155, 863), (61, 400), (2, 179)⟩))))) = true := by
  decide +kernel

private theorem u86_0_g3 :
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 10303⟩ ⟨(109, 393), (155, 863), (61, 400), (2, 203)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 17293⟩ ⟨(109, 393), (155, 863), (61, 400), (2, 263)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 28057⟩ ⟨(109, 393), (155, 863), (61, 400), (2, 335)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 30103⟩ ⟨(109, 393), (155, 863), (61, 400), (2, 347)⟩ &&
    (leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .pin 86143⟩ ⟨(109, 393), (155, 863), (61, 400), (2, 587)⟩))))) = true := by
  decide +kernel

private theorem u86_0_g4 :
    leafOK (.c31, .c43, .big) ⟨.free .q 13 [], .pin 31, .pin 43, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1471, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61]⟩ ⟨(109, 393), (155, 863), (61, 400), (1, 8)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(31, 43, big)`, with 21 leaves. -/
def u86_0 : Tree :=
  .split 3 61
    (.leaf ⟨(109, 393), (155, 863), (61, 400), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(109, 393), (155, 863), (61, 400), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(109, 393), (155, 863), (61, 400), (57, 487)⟩)
        (.split 3 109
          (.leaf ⟨(109, 393), (155, 863), (61, 400), (25, 261)⟩)
          (.split 3 151
            (.leaf ⟨(109, 393), (155, 863), (61, 400), (59, 725)⟩)
            (.split 3 307
              (.leaf ⟨(109, 393), (155, 863), (61, 400), (48, 841)⟩)
              (.split 3 709
                (.leaf ⟨(109, 393), (155, 863), (61, 400), (8, 213)⟩)
                (.split 3 727
                  (.leaf ⟨(109, 393), (155, 863), (61, 400), (26, 701)⟩)
                  (.split 3 991
                    (.leaf ⟨(109, 393), (155, 863), (61, 400), (25, 787)⟩)
                    (.split 3 1087
                      (.leaf ⟨(109, 393), (155, 863), (61, 400), (30, 989)⟩)
                      (.split 3 1471
                        (.leaf ⟨(109, 393), (155, 863), (61, 400), (17, 652)⟩)
                        (.split 3 1723
                          (.leaf ⟨(109, 393), (155, 863), (61, 400), (2, 83)⟩)
                          (.split 3 3541
                            (.leaf ⟨(109, 393), (155, 863), (61, 400), (2, 119)⟩)
                            (.split 3 5113
                              (.leaf ⟨(109, 393), (155, 863), (61, 400), (2, 143)⟩)
                              (.split 3 8011
                                (.leaf ⟨(109, 393), (155, 863), (61, 400), (2, 179)⟩)
                                (.split 3 10303
                                  (.leaf ⟨(109, 393), (155, 863), (61, 400), (2, 203)⟩)
                                  (.split 3 17293
                                    (.leaf ⟨(109, 393), (155, 863), (61, 400), (2, 263)⟩)
                                    (.split 3 28057
                                      (.leaf ⟨(109, 393), (155, 863), (61, 400), (2, 335)⟩)
                                      (.split 3 30103
                                        (.leaf ⟨(109, 393), (155, 863), (61, 400), (2, 347)⟩)
                                        (.split 3 86143
                                          (.leaf ⟨(109, 393), (155, 863), (61, 400), (2, 587)⟩)
                                          (.leaf ⟨(109, 393), (155, 863), (61, 400), (1, 8)⟩))))))))))))))))))))

/-- Subtree 0 of the class triple `(31, 43, big)` passes the check. -/
theorem u86_0_ok : treeOK (.c31, .c43, .big)
    (rootNode (.c31, .c43, .big)) u86_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u86_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u86_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u86_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u86_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g3).2).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u86_0_g3).2).2).2).2)
                                          (treeOK_leaf u86_0_g4))))))))))))))))))))

private theorem u87_0_g0 :
    leafOK (.c31, .n2, .n2) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .free .n2 11 []⟩ ⟨(109, 393), (155, 863), (0, 1), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(31, n2, n2)`, with 1 leaves. -/
def u87_0 : Tree :=
  .leaf ⟨(109, 393), (155, 863), (0, 1), (0, 1)⟩

/-- Subtree 0 of the class triple `(31, n2, n2)` passes the check. -/
theorem u87_0_ok : treeOK (.c31, .n2, .n2)
    (rootNode (.c31, .n2, .n2)) u87_0 = true :=
  treeOK_leaf u87_0_g0

private theorem u88_0_g0 :
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 61⟩ ⟨(109, 393), (155, 863), (0, 1), (79, 617)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 67⟩ ⟨(109, 393), (155, 863), (0, 1), (27, 221)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 73⟩ ⟨(109, 393), (155, 863), (0, 1), (57, 487)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 109⟩ ⟨(109, 393), (155, 863), (0, 1), (25, 261)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 151⟩ ⟨(109, 393), (155, 863), (0, 1), (59, 725)⟩))))) = true := by
  decide +kernel

private theorem u88_0_g1 :
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 307⟩ ⟨(109, 393), (155, 863), (0, 1), (48, 841)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 709⟩ ⟨(109, 393), (155, 863), (0, 1), (8, 213)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 727⟩ ⟨(109, 393), (155, 863), (0, 1), (26, 701)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 991⟩ ⟨(109, 393), (155, 863), (0, 1), (25, 787)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 1087⟩ ⟨(109, 393), (155, 863), (0, 1), (30, 989)⟩))))) = true := by
  decide +kernel

private theorem u88_0_g2 :
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 1723⟩ ⟨(109, 393), (155, 863), (0, 1), (2, 83)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 3541⟩ ⟨(109, 393), (155, 863), (0, 1), (2, 119)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 5113⟩ ⟨(109, 393), (155, 863), (0, 1), (2, 143)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 8011⟩ ⟨(109, 393), (155, 863), (0, 1), (2, 179)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 10303⟩ ⟨(109, 393), (155, 863), (0, 1), (2, 203)⟩))))) = true := by
  decide +kernel

private theorem u88_0_g3 :
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 17293⟩ ⟨(109, 393), (155, 863), (0, 1), (2, 263)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 28057⟩ ⟨(109, 393), (155, 863), (0, 1), (2, 335)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 30103⟩ ⟨(109, 393), (155, 863), (0, 1), (2, 347)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .pin 86143⟩ ⟨(109, 393), (155, 863), (0, 1), (2, 587)⟩ &&
    (leafOK (.c31, .n2, .big) ⟨.free .q 13 [], .pin 31, .free .n2 11 [], .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61]⟩ ⟨(109, 393), (155, 863), (0, 1), (1, 8)⟩))))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(31, n2, big)`, with 20 leaves. -/
def u88_0 : Tree :=
  .split 3 61
    (.leaf ⟨(109, 393), (155, 863), (0, 1), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(109, 393), (155, 863), (0, 1), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(109, 393), (155, 863), (0, 1), (57, 487)⟩)
        (.split 3 109
          (.leaf ⟨(109, 393), (155, 863), (0, 1), (25, 261)⟩)
          (.split 3 151
            (.leaf ⟨(109, 393), (155, 863), (0, 1), (59, 725)⟩)
            (.split 3 307
              (.leaf ⟨(109, 393), (155, 863), (0, 1), (48, 841)⟩)
              (.split 3 709
                (.leaf ⟨(109, 393), (155, 863), (0, 1), (8, 213)⟩)
                (.split 3 727
                  (.leaf ⟨(109, 393), (155, 863), (0, 1), (26, 701)⟩)
                  (.split 3 991
                    (.leaf ⟨(109, 393), (155, 863), (0, 1), (25, 787)⟩)
                    (.split 3 1087
                      (.leaf ⟨(109, 393), (155, 863), (0, 1), (30, 989)⟩)
                      (.split 3 1723
                        (.leaf ⟨(109, 393), (155, 863), (0, 1), (2, 83)⟩)
                        (.split 3 3541
                          (.leaf ⟨(109, 393), (155, 863), (0, 1), (2, 119)⟩)
                          (.split 3 5113
                            (.leaf ⟨(109, 393), (155, 863), (0, 1), (2, 143)⟩)
                            (.split 3 8011
                              (.leaf ⟨(109, 393), (155, 863), (0, 1), (2, 179)⟩)
                              (.split 3 10303
                                (.leaf ⟨(109, 393), (155, 863), (0, 1), (2, 203)⟩)
                                (.split 3 17293
                                  (.leaf ⟨(109, 393), (155, 863), (0, 1), (2, 263)⟩)
                                  (.split 3 28057
                                    (.leaf ⟨(109, 393), (155, 863), (0, 1), (2, 335)⟩)
                                    (.split 3 30103
                                      (.leaf ⟨(109, 393), (155, 863), (0, 1), (2, 347)⟩)
                                      (.split 3 86143
                                        (.leaf ⟨(109, 393), (155, 863), (0, 1), (2, 587)⟩)
                                        (.leaf ⟨(109, 393), (155, 863), (0, 1), (1, 8)⟩)))))))))))))))))))

/-- Subtree 0 of the class triple `(31, n2, big)` passes the check. -/
theorem u88_0_ok : treeOK (.c31, .n2, .big)
    (rootNode (.c31, .n2, .big)) u88_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u88_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u88_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u88_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u88_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g3).2).2).2).1)
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u88_0_g3).2).2).2).2)))))))))))))))))))

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u61_0_ok
#print axioms OddPerfect.ThreeFreeThree.u62_0_ok
#print axioms OddPerfect.ThreeFreeThree.u63_0_ok
#print axioms OddPerfect.ThreeFreeThree.u64_0_ok
#print axioms OddPerfect.ThreeFreeThree.u65_0_ok
#print axioms OddPerfect.ThreeFreeThree.u66_0_ok
#print axioms OddPerfect.ThreeFreeThree.u67_0_ok
#print axioms OddPerfect.ThreeFreeThree.u68_0_ok
#print axioms OddPerfect.ThreeFreeThree.u69_0_ok
#print axioms OddPerfect.ThreeFreeThree.u70_0_ok
#print axioms OddPerfect.ThreeFreeThree.u71_0_ok
#print axioms OddPerfect.ThreeFreeThree.u72_0_ok
#print axioms OddPerfect.ThreeFreeThree.u73_0_ok
#print axioms OddPerfect.ThreeFreeThree.u74_0_ok
#print axioms OddPerfect.ThreeFreeThree.u75_0_ok
#print axioms OddPerfect.ThreeFreeThree.u76_0_ok
#print axioms OddPerfect.ThreeFreeThree.u77_0_ok
#print axioms OddPerfect.ThreeFreeThree.u78_0_ok
#print axioms OddPerfect.ThreeFreeThree.u79_0_ok
#print axioms OddPerfect.ThreeFreeThree.u80_0_ok
#print axioms OddPerfect.ThreeFreeThree.u81_0_ok
#print axioms OddPerfect.ThreeFreeThree.u82_0_ok
#print axioms OddPerfect.ThreeFreeThree.u83_0_ok
#print axioms OddPerfect.ThreeFreeThree.u84_0_ok
#print axioms OddPerfect.ThreeFreeThree.u85_0_ok
#print axioms OddPerfect.ThreeFreeThree.u86_0_ok
#print axioms OddPerfect.ThreeFreeThree.u87_0_ok
#print axioms OddPerfect.ThreeFreeThree.u88_0_ok
