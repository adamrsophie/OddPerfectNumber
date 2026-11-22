import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 8

Subtrees of the case analysis certificate for the class triples `(7, 37, big)`,
`(7, 43, n2)`, `(7, 43, big)`, `(7, n2, n2)`, `(7, n2, big)`, `(7, big, big)` (part), with 102
leaves in all. Each public theorem states that a subtree passes `treeOK` from explicit
constraints. The data was found by a search outside Lean; everything in this file is
rechecked by the kernel through `decide +kernel` on the leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u47_0_g0 :
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 61⟩ ⟨(109, 393), (223, 590), (145, 882), (79, 617)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 67⟩ ⟨(109, 393), (223, 590), (145, 882), (27, 221)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 73⟩ ⟨(109, 393), (223, 590), (145, 882), (57, 487)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 79⟩ ⟨(109, 393), (223, 590), (145, 882), (107, 951)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 109⟩ ⟨(109, 393), (223, 590), (145, 882), (25, 261)⟩))))) = true := by
  decide +kernel

private theorem u47_0_g1 :
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 127⟩ ⟨(109, 393), (223, 590), (145, 882), (26, 293)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 151⟩ ⟨(109, 393), (223, 590), (145, 882), (59, 725)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 307⟩ ⟨(109, 393), (223, 590), (145, 882), (48, 841)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 409⟩ ⟨(109, 393), (223, 590), (145, 882), (9, 182)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 709⟩ ⟨(109, 393), (223, 590), (145, 882), (8, 213)⟩))))) = true := by
  decide +kernel

private theorem u47_0_g2 :
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 727⟩ ⟨(109, 393), (223, 590), (145, 882), (26, 701)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 991⟩ ⟨(109, 393), (223, 590), (145, 882), (25, 787)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 1087⟩ ⟨(109, 393), (223, 590), (145, 882), (30, 989)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 1723⟩ ⟨(109, 393), (223, 590), (145, 882), (2, 83)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 3541⟩ ⟨(109, 393), (223, 590), (145, 882), (2, 119)⟩))))) = true := by
  decide +kernel

private theorem u47_0_g3 :
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 4603⟩ ⟨(109, 393), (223, 590), (145, 882), (6, 407)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 5113⟩ ⟨(109, 393), (223, 590), (145, 882), (2, 143)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 7789⟩ ⟨(109, 393), (223, 590), (145, 882), (4, 353)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 8011⟩ ⟨(109, 393), (223, 590), (145, 882), (2, 179)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 10303⟩ ⟨(109, 393), (223, 590), (145, 882), (2, 203)⟩))))) = true := by
  decide +kernel

private theorem u47_0_g4 :
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 17293⟩ ⟨(109, 393), (223, 590), (145, 882), (2, 263)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 28057⟩ ⟨(109, 393), (223, 590), (145, 882), (2, 335)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 30103⟩ ⟨(109, 393), (223, 590), (145, 882), (2, 347)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 86143⟩ ⟨(109, 393), (223, 590), (145, 882), (2, 587)⟩ &&
    (leafOK (.c7, .c37, .big) ⟨.free .q 13 [], .pin 7, .pin 37, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(109, 393), (223, 590), (145, 882), (1, 8)⟩))))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 37, big)`, with 25 leaves. -/
def u47_0 : Tree :=
  .split 3 61
    (.leaf ⟨(109, 393), (223, 590), (145, 882), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(109, 393), (223, 590), (145, 882), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(109, 393), (223, 590), (145, 882), (57, 487)⟩)
        (.split 3 79
          (.leaf ⟨(109, 393), (223, 590), (145, 882), (107, 951)⟩)
          (.split 3 109
            (.leaf ⟨(109, 393), (223, 590), (145, 882), (25, 261)⟩)
            (.split 3 127
              (.leaf ⟨(109, 393), (223, 590), (145, 882), (26, 293)⟩)
              (.split 3 151
                (.leaf ⟨(109, 393), (223, 590), (145, 882), (59, 725)⟩)
                (.split 3 307
                  (.leaf ⟨(109, 393), (223, 590), (145, 882), (48, 841)⟩)
                  (.split 3 409
                    (.leaf ⟨(109, 393), (223, 590), (145, 882), (9, 182)⟩)
                    (.split 3 709
                      (.leaf ⟨(109, 393), (223, 590), (145, 882), (8, 213)⟩)
                      (.split 3 727
                        (.leaf ⟨(109, 393), (223, 590), (145, 882), (26, 701)⟩)
                        (.split 3 991
                          (.leaf ⟨(109, 393), (223, 590), (145, 882), (25, 787)⟩)
                          (.split 3 1087
                            (.leaf ⟨(109, 393), (223, 590), (145, 882), (30, 989)⟩)
                            (.split 3 1723
                              (.leaf ⟨(109, 393), (223, 590), (145, 882), (2, 83)⟩)
                              (.split 3 3541
                                (.leaf ⟨(109, 393), (223, 590), (145, 882), (2, 119)⟩)
                                (.split 3 4603
                                  (.leaf ⟨(109, 393), (223, 590), (145, 882), (6, 407)⟩)
                                  (.split 3 5113
                                    (.leaf ⟨(109, 393), (223, 590), (145, 882), (2, 143)⟩)
                                    (.split 3 7789
                                      (.leaf ⟨(109, 393), (223, 590), (145, 882), (4, 353)⟩)
                                      (.split 3 8011
                                        (.leaf ⟨(109, 393), (223, 590), (145, 882), (2, 179)⟩)
                                        (.split 3 10303
                                          (.leaf ⟨(109, 393), (223, 590), (145, 882), (2, 203)⟩)
                                          (.split 3 17293
                                            (.leaf ⟨(109, 393), (223, 590), (145, 882), (2, 263)⟩)
                                            (.split 3 28057
                                              (.leaf ⟨(109, 393), (223, 590), (145, 882), (2, 335)⟩)
                                              (.split 3 30103
                                                (.leaf ⟨(109, 393), (223, 590), (145, 882), (2, 347)⟩)
                                                (.split 3 86143
                                                  (.leaf ⟨(109, 393), (223, 590), (145, 882), (2, 587)⟩)
                                                  (.leaf ⟨(109, 393), (223, 590), (145, 882), (1, 8)⟩))))))))))))))))))))))))

/-- Subtree 0 of the class triple `(7, 37, big)` passes the check. -/
theorem u47_0_ok : treeOK (.c7, .c37, .big)
    (rootNode (.c7, .c37, .big)) u47_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u47_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u47_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u47_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u47_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g3).2).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g3).2).2).2).2)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp u47_0_g4).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g4).2).1)
                                              (treeOK_split (by decide) rfl
                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g4).2).2).1)
                                                (treeOK_split (by decide) rfl
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g4).2).2).2).1)
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u47_0_g4).2).2).2).2))))))))))))))))))))))))

private theorem u48_0_g0 :
    leafOK (.c7, .c43, .n2) ⟨.free .q 13 [], .pin 7, .pin 43, .free .n2 11 []⟩ ⟨(109, 393), (223, 590), (61, 400), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 43, n2)`, with 1 leaves. -/
def u48_0 : Tree :=
  .leaf ⟨(109, 393), (223, 590), (61, 400), (0, 1)⟩

/-- Subtree 0 of the class triple `(7, 43, n2)` passes the check. -/
theorem u48_0_ok : treeOK (.c7, .c43, .n2)
    (rootNode (.c7, .c43, .n2)) u48_0 = true :=
  treeOK_leaf u48_0_g0

private theorem u49_0_g0 :
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 61⟩ ⟨(109, 393), (223, 590), (61, 400), (79, 617)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 67⟩ ⟨(109, 393), (223, 590), (61, 400), (27, 221)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 73⟩ ⟨(109, 393), (223, 590), (61, 400), (57, 487)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 79⟩ ⟨(109, 393), (223, 590), (61, 400), (107, 951)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 109⟩ ⟨(109, 393), (223, 590), (61, 400), (25, 261)⟩))))) = true := by
  decide +kernel

private theorem u49_0_g1 :
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 127⟩ ⟨(109, 393), (223, 590), (61, 400), (26, 293)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 151⟩ ⟨(109, 393), (223, 590), (61, 400), (59, 725)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 307⟩ ⟨(109, 393), (223, 590), (61, 400), (48, 841)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 409⟩ ⟨(109, 393), (223, 590), (61, 400), (9, 182)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 709⟩ ⟨(109, 393), (223, 590), (61, 400), (8, 213)⟩))))) = true := by
  decide +kernel

private theorem u49_0_g2 :
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 727⟩ ⟨(109, 393), (223, 590), (61, 400), (26, 701)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 991⟩ ⟨(109, 393), (223, 590), (61, 400), (25, 787)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 1087⟩ ⟨(109, 393), (223, 590), (61, 400), (30, 989)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 1471⟩ ⟨(109, 393), (223, 590), (61, 400), (17, 652)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 1723⟩ ⟨(109, 393), (223, 590), (61, 400), (2, 83)⟩))))) = true := by
  decide +kernel

private theorem u49_0_g3 :
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 3541⟩ ⟨(109, 393), (223, 590), (61, 400), (2, 119)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 4603⟩ ⟨(109, 393), (223, 590), (61, 400), (6, 407)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 5113⟩ ⟨(109, 393), (223, 590), (61, 400), (2, 143)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 7789⟩ ⟨(109, 393), (223, 590), (61, 400), (4, 353)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 8011⟩ ⟨(109, 393), (223, 590), (61, 400), (2, 179)⟩))))) = true := by
  decide +kernel

private theorem u49_0_g4 :
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 10303⟩ ⟨(109, 393), (223, 590), (61, 400), (2, 203)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 17293⟩ ⟨(109, 393), (223, 590), (61, 400), (2, 263)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 28057⟩ ⟨(109, 393), (223, 590), (61, 400), (2, 335)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 30103⟩ ⟨(109, 393), (223, 590), (61, 400), (2, 347)⟩ &&
    (leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .pin 86143⟩ ⟨(109, 393), (223, 590), (61, 400), (2, 587)⟩))))) = true := by
  decide +kernel

private theorem u49_0_g5 :
    leafOK (.c7, .c43, .big) ⟨.free .q 13 [], .pin 7, .pin 43, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1471, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(109, 393), (223, 590), (61, 400), (1, 8)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 43, big)`, with 26 leaves. -/
def u49_0 : Tree :=
  .split 3 61
    (.leaf ⟨(109, 393), (223, 590), (61, 400), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(109, 393), (223, 590), (61, 400), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(109, 393), (223, 590), (61, 400), (57, 487)⟩)
        (.split 3 79
          (.leaf ⟨(109, 393), (223, 590), (61, 400), (107, 951)⟩)
          (.split 3 109
            (.leaf ⟨(109, 393), (223, 590), (61, 400), (25, 261)⟩)
            (.split 3 127
              (.leaf ⟨(109, 393), (223, 590), (61, 400), (26, 293)⟩)
              (.split 3 151
                (.leaf ⟨(109, 393), (223, 590), (61, 400), (59, 725)⟩)
                (.split 3 307
                  (.leaf ⟨(109, 393), (223, 590), (61, 400), (48, 841)⟩)
                  (.split 3 409
                    (.leaf ⟨(109, 393), (223, 590), (61, 400), (9, 182)⟩)
                    (.split 3 709
                      (.leaf ⟨(109, 393), (223, 590), (61, 400), (8, 213)⟩)
                      (.split 3 727
                        (.leaf ⟨(109, 393), (223, 590), (61, 400), (26, 701)⟩)
                        (.split 3 991
                          (.leaf ⟨(109, 393), (223, 590), (61, 400), (25, 787)⟩)
                          (.split 3 1087
                            (.leaf ⟨(109, 393), (223, 590), (61, 400), (30, 989)⟩)
                            (.split 3 1471
                              (.leaf ⟨(109, 393), (223, 590), (61, 400), (17, 652)⟩)
                              (.split 3 1723
                                (.leaf ⟨(109, 393), (223, 590), (61, 400), (2, 83)⟩)
                                (.split 3 3541
                                  (.leaf ⟨(109, 393), (223, 590), (61, 400), (2, 119)⟩)
                                  (.split 3 4603
                                    (.leaf ⟨(109, 393), (223, 590), (61, 400), (6, 407)⟩)
                                    (.split 3 5113
                                      (.leaf ⟨(109, 393), (223, 590), (61, 400), (2, 143)⟩)
                                      (.split 3 7789
                                        (.leaf ⟨(109, 393), (223, 590), (61, 400), (4, 353)⟩)
                                        (.split 3 8011
                                          (.leaf ⟨(109, 393), (223, 590), (61, 400), (2, 179)⟩)
                                          (.split 3 10303
                                            (.leaf ⟨(109, 393), (223, 590), (61, 400), (2, 203)⟩)
                                            (.split 3 17293
                                              (.leaf ⟨(109, 393), (223, 590), (61, 400), (2, 263)⟩)
                                              (.split 3 28057
                                                (.leaf ⟨(109, 393), (223, 590), (61, 400), (2, 335)⟩)
                                                (.split 3 30103
                                                  (.leaf ⟨(109, 393), (223, 590), (61, 400), (2, 347)⟩)
                                                  (.split 3 86143
                                                    (.leaf ⟨(109, 393), (223, 590), (61, 400), (2, 587)⟩)
                                                    (.leaf ⟨(109, 393), (223, 590), (61, 400), (1, 8)⟩)))))))))))))))))))))))))

/-- Subtree 0 of the class triple `(7, 43, big)` passes the check. -/
theorem u49_0_ok : treeOK (.c7, .c43, .big)
    (rootNode (.c7, .c43, .big)) u49_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u49_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u49_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u49_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u49_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g3).2).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g3).2).2).2).2)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp u49_0_g4).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g4).2).1)
                                              (treeOK_split (by decide) rfl
                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g4).2).2).1)
                                                (treeOK_split (by decide) rfl
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g4).2).2).2).1)
                                                  (treeOK_split (by decide) rfl
                                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u49_0_g4).2).2).2).2)
                                                    (treeOK_leaf u49_0_g5)))))))))))))))))))))))))

private theorem u50_0_g0 :
    leafOK (.c7, .n2, .n2) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .free .n2 11 []⟩ ⟨(109, 393), (223, 590), (0, 1), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, n2, n2)`, with 1 leaves. -/
def u50_0 : Tree :=
  .leaf ⟨(109, 393), (223, 590), (0, 1), (0, 1)⟩

/-- Subtree 0 of the class triple `(7, n2, n2)` passes the check. -/
theorem u50_0_ok : treeOK (.c7, .n2, .n2)
    (rootNode (.c7, .n2, .n2)) u50_0 = true :=
  treeOK_leaf u50_0_g0

private theorem u51_0_g0 :
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 61⟩ ⟨(109, 393), (223, 590), (0, 1), (79, 617)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 67⟩ ⟨(109, 393), (223, 590), (0, 1), (27, 221)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 73⟩ ⟨(109, 393), (223, 590), (0, 1), (57, 487)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 79⟩ ⟨(109, 393), (223, 590), (0, 1), (107, 951)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 109⟩ ⟨(109, 393), (223, 590), (0, 1), (25, 261)⟩))))) = true := by
  decide +kernel

private theorem u51_0_g1 :
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 127⟩ ⟨(109, 393), (223, 590), (0, 1), (26, 293)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 151⟩ ⟨(109, 393), (223, 590), (0, 1), (59, 725)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 307⟩ ⟨(109, 393), (223, 590), (0, 1), (48, 841)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 409⟩ ⟨(109, 393), (223, 590), (0, 1), (9, 182)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 709⟩ ⟨(109, 393), (223, 590), (0, 1), (8, 213)⟩))))) = true := by
  decide +kernel

private theorem u51_0_g2 :
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 727⟩ ⟨(109, 393), (223, 590), (0, 1), (26, 701)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 991⟩ ⟨(109, 393), (223, 590), (0, 1), (25, 787)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 1087⟩ ⟨(109, 393), (223, 590), (0, 1), (30, 989)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 1723⟩ ⟨(109, 393), (223, 590), (0, 1), (2, 83)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 3541⟩ ⟨(109, 393), (223, 590), (0, 1), (2, 119)⟩))))) = true := by
  decide +kernel

private theorem u51_0_g3 :
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 4603⟩ ⟨(109, 393), (223, 590), (0, 1), (6, 407)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 5113⟩ ⟨(109, 393), (223, 590), (0, 1), (2, 143)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 7789⟩ ⟨(109, 393), (223, 590), (0, 1), (4, 353)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 8011⟩ ⟨(109, 393), (223, 590), (0, 1), (2, 179)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 10303⟩ ⟨(109, 393), (223, 590), (0, 1), (2, 203)⟩))))) = true := by
  decide +kernel

private theorem u51_0_g4 :
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 17293⟩ ⟨(109, 393), (223, 590), (0, 1), (2, 263)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 28057⟩ ⟨(109, 393), (223, 590), (0, 1), (2, 335)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 30103⟩ ⟨(109, 393), (223, 590), (0, 1), (2, 347)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .pin 86143⟩ ⟨(109, 393), (223, 590), (0, 1), (2, 587)⟩ &&
    (leafOK (.c7, .n2, .big) ⟨.free .q 13 [], .pin 7, .free .n2 11 [], .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(109, 393), (223, 590), (0, 1), (1, 8)⟩))))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, n2, big)`, with 25 leaves. -/
def u51_0 : Tree :=
  .split 3 61
    (.leaf ⟨(109, 393), (223, 590), (0, 1), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(109, 393), (223, 590), (0, 1), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(109, 393), (223, 590), (0, 1), (57, 487)⟩)
        (.split 3 79
          (.leaf ⟨(109, 393), (223, 590), (0, 1), (107, 951)⟩)
          (.split 3 109
            (.leaf ⟨(109, 393), (223, 590), (0, 1), (25, 261)⟩)
            (.split 3 127
              (.leaf ⟨(109, 393), (223, 590), (0, 1), (26, 293)⟩)
              (.split 3 151
                (.leaf ⟨(109, 393), (223, 590), (0, 1), (59, 725)⟩)
                (.split 3 307
                  (.leaf ⟨(109, 393), (223, 590), (0, 1), (48, 841)⟩)
                  (.split 3 409
                    (.leaf ⟨(109, 393), (223, 590), (0, 1), (9, 182)⟩)
                    (.split 3 709
                      (.leaf ⟨(109, 393), (223, 590), (0, 1), (8, 213)⟩)
                      (.split 3 727
                        (.leaf ⟨(109, 393), (223, 590), (0, 1), (26, 701)⟩)
                        (.split 3 991
                          (.leaf ⟨(109, 393), (223, 590), (0, 1), (25, 787)⟩)
                          (.split 3 1087
                            (.leaf ⟨(109, 393), (223, 590), (0, 1), (30, 989)⟩)
                            (.split 3 1723
                              (.leaf ⟨(109, 393), (223, 590), (0, 1), (2, 83)⟩)
                              (.split 3 3541
                                (.leaf ⟨(109, 393), (223, 590), (0, 1), (2, 119)⟩)
                                (.split 3 4603
                                  (.leaf ⟨(109, 393), (223, 590), (0, 1), (6, 407)⟩)
                                  (.split 3 5113
                                    (.leaf ⟨(109, 393), (223, 590), (0, 1), (2, 143)⟩)
                                    (.split 3 7789
                                      (.leaf ⟨(109, 393), (223, 590), (0, 1), (4, 353)⟩)
                                      (.split 3 8011
                                        (.leaf ⟨(109, 393), (223, 590), (0, 1), (2, 179)⟩)
                                        (.split 3 10303
                                          (.leaf ⟨(109, 393), (223, 590), (0, 1), (2, 203)⟩)
                                          (.split 3 17293
                                            (.leaf ⟨(109, 393), (223, 590), (0, 1), (2, 263)⟩)
                                            (.split 3 28057
                                              (.leaf ⟨(109, 393), (223, 590), (0, 1), (2, 335)⟩)
                                              (.split 3 30103
                                                (.leaf ⟨(109, 393), (223, 590), (0, 1), (2, 347)⟩)
                                                (.split 3 86143
                                                  (.leaf ⟨(109, 393), (223, 590), (0, 1), (2, 587)⟩)
                                                  (.leaf ⟨(109, 393), (223, 590), (0, 1), (1, 8)⟩))))))))))))))))))))))))

/-- Subtree 0 of the class triple `(7, n2, big)` passes the check. -/
theorem u51_0_ok : treeOK (.c7, .n2, .big)
    (rootNode (.c7, .n2, .big)) u51_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u51_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u51_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u51_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u51_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g3).2).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g3).2).2).2).2)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp u51_0_g4).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g4).2).1)
                                              (treeOK_split (by decide) rfl
                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g4).2).2).1)
                                                (treeOK_split (by decide) rfl
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g4).2).2).2).1)
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u51_0_g4).2).2).2).2))))))))))))))))))))))))

private theorem u52_0_g0 :
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 67⟩ ⟨(109, 393), (223, 590), (79, 617), (27, 221)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 73⟩ ⟨(109, 393), (223, 590), (79, 617), (57, 487)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 79⟩ ⟨(109, 393), (223, 590), (79, 617), (107, 951)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 109⟩ ⟨(109, 393), (223, 590), (79, 617), (25, 261)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 127⟩ ⟨(109, 393), (223, 590), (79, 617), (26, 293)⟩))))) = true := by
  decide +kernel

private theorem u52_0_g1 :
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 151⟩ ⟨(109, 393), (223, 590), (79, 617), (59, 725)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 307⟩ ⟨(109, 393), (223, 590), (79, 617), (48, 841)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 409⟩ ⟨(109, 393), (223, 590), (79, 617), (9, 182)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 709⟩ ⟨(109, 393), (223, 590), (79, 617), (8, 213)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 727⟩ ⟨(109, 393), (223, 590), (79, 617), (26, 701)⟩))))) = true := by
  decide +kernel

private theorem u52_0_g2 :
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 991⟩ ⟨(109, 393), (223, 590), (79, 617), (25, 787)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 1087⟩ ⟨(109, 393), (223, 590), (79, 617), (30, 989)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 1723⟩ ⟨(109, 393), (223, 590), (79, 617), (2, 83)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 3541⟩ ⟨(109, 393), (223, 590), (79, 617), (2, 119)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 4603⟩ ⟨(109, 393), (223, 590), (79, 617), (6, 407)⟩))))) = true := by
  decide +kernel

private theorem u52_0_g3 :
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 5113⟩ ⟨(109, 393), (223, 590), (79, 617), (2, 143)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 7789⟩ ⟨(109, 393), (223, 590), (79, 617), (4, 353)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 8011⟩ ⟨(109, 393), (223, 590), (79, 617), (2, 179)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 10303⟩ ⟨(109, 393), (223, 590), (79, 617), (2, 203)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 17293⟩ ⟨(109, 393), (223, 590), (79, 617), (2, 263)⟩))))) = true := by
  decide +kernel

private theorem u52_0_g4 :
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 28057⟩ ⟨(109, 393), (223, 590), (79, 617), (2, 335)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 30103⟩ ⟨(109, 393), (223, 590), (79, 617), (2, 347)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .pin 86143⟩ ⟨(109, 393), (223, 590), (79, 617), (2, 587)⟩ &&
    (leafOK (.c7, .big, .big) ⟨.free .q 13 [], .pin 7, .pin 61, .free .big 62 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67]⟩ ⟨(109, 393), (223, 590), (79, 617), (1, 8)⟩)))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, big, big)`, with 24 leaves. -/
def u52_0 : Tree :=
  .split 3 67
    (.leaf ⟨(109, 393), (223, 590), (79, 617), (27, 221)⟩)
    (.split 3 73
      (.leaf ⟨(109, 393), (223, 590), (79, 617), (57, 487)⟩)
      (.split 3 79
        (.leaf ⟨(109, 393), (223, 590), (79, 617), (107, 951)⟩)
        (.split 3 109
          (.leaf ⟨(109, 393), (223, 590), (79, 617), (25, 261)⟩)
          (.split 3 127
            (.leaf ⟨(109, 393), (223, 590), (79, 617), (26, 293)⟩)
            (.split 3 151
              (.leaf ⟨(109, 393), (223, 590), (79, 617), (59, 725)⟩)
              (.split 3 307
                (.leaf ⟨(109, 393), (223, 590), (79, 617), (48, 841)⟩)
                (.split 3 409
                  (.leaf ⟨(109, 393), (223, 590), (79, 617), (9, 182)⟩)
                  (.split 3 709
                    (.leaf ⟨(109, 393), (223, 590), (79, 617), (8, 213)⟩)
                    (.split 3 727
                      (.leaf ⟨(109, 393), (223, 590), (79, 617), (26, 701)⟩)
                      (.split 3 991
                        (.leaf ⟨(109, 393), (223, 590), (79, 617), (25, 787)⟩)
                        (.split 3 1087
                          (.leaf ⟨(109, 393), (223, 590), (79, 617), (30, 989)⟩)
                          (.split 3 1723
                            (.leaf ⟨(109, 393), (223, 590), (79, 617), (2, 83)⟩)
                            (.split 3 3541
                              (.leaf ⟨(109, 393), (223, 590), (79, 617), (2, 119)⟩)
                              (.split 3 4603
                                (.leaf ⟨(109, 393), (223, 590), (79, 617), (6, 407)⟩)
                                (.split 3 5113
                                  (.leaf ⟨(109, 393), (223, 590), (79, 617), (2, 143)⟩)
                                  (.split 3 7789
                                    (.leaf ⟨(109, 393), (223, 590), (79, 617), (4, 353)⟩)
                                    (.split 3 8011
                                      (.leaf ⟨(109, 393), (223, 590), (79, 617), (2, 179)⟩)
                                      (.split 3 10303
                                        (.leaf ⟨(109, 393), (223, 590), (79, 617), (2, 203)⟩)
                                        (.split 3 17293
                                          (.leaf ⟨(109, 393), (223, 590), (79, 617), (2, 263)⟩)
                                          (.split 3 28057
                                            (.leaf ⟨(109, 393), (223, 590), (79, 617), (2, 335)⟩)
                                            (.split 3 30103
                                              (.leaf ⟨(109, 393), (223, 590), (79, 617), (2, 347)⟩)
                                              (.split 3 86143
                                                (.leaf ⟨(109, 393), (223, 590), (79, 617), (2, 587)⟩)
                                                (.leaf ⟨(109, 393), (223, 590), (79, 617), (1, 8)⟩)))))))))))))))))))))))

/-- Subtree 0 of the class triple `(7, big, big)` passes the check. -/
theorem u52_0_ok : treeOK (.c7, .big, .big)
    ⟨.free .q 13 [], .pin 7, .pin 61, .free .big 62 []⟩ u52_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u52_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u52_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u52_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u52_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g3).2).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g3).2).2).2).2)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp u52_0_g4).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g4).2).1)
                                              (treeOK_split (by decide) rfl
                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g4).2).2).1)
                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u52_0_g4).2).2).2)))))))))))))))))))))))

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u47_0_ok
#print axioms OddPerfect.ThreeFreeThree.u48_0_ok
#print axioms OddPerfect.ThreeFreeThree.u49_0_ok
#print axioms OddPerfect.ThreeFreeThree.u50_0_ok
#print axioms OddPerfect.ThreeFreeThree.u51_0_ok
#print axioms OddPerfect.ThreeFreeThree.u52_0_ok
