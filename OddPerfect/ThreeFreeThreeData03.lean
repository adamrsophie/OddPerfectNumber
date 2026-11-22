import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 3

Subtrees of the case analysis certificate for the class triples `(7, 13, 19)`,
`(7, 13, 31)`, `(7, 13, 37)`, `(7, 13, 43)`, `(7, 13, n2)`, `(7, 13, big)`, `(7, 19, 31)`,
`(7, 19, 37)`, `(7, 19, 43)`, `(7, 19, n2)`, with 111 leaves in all. Each public theorem
states that a subtree passes `treeOK` from explicit constraints. The data was found by
a search outside Lean; everything in this file is rechecked by the kernel through
`decide +kernel` on the leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u30_0_g0 :
    (leafOK (.c7, .c13, .c19) ⟨.pin 37, .pin 7, .pin 13, .pin 19⟩ ⟨(145, 882), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.pin 61, .pin 7, .pin 13, .pin 19⟩ ⟨(79, 617), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.pin 73, .pin 7, .pin 13, .pin 19⟩ ⟨(57, 487), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.pin 109, .pin 7, .pin 13, .pin 19⟩ ⟨(25, 261), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.pin 409, .pin 7, .pin 13, .pin 19⟩ ⟨(9, 182), (223, 590), (109, 393), (209, 911)⟩))))) = true := by
  decide +kernel

private theorem u30_0_g1 :
    (leafOK (.c7, .c13, .c19) ⟨.pin 709, .pin 7, .pin 13, .pin 19⟩ ⟨(8, 213), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.pin 2053, .pin 7, .pin 13, .pin 19⟩ ⟨(13, 589), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.pin 3541, .pin 7, .pin 13, .pin 19⟩ ⟨(2, 119), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.pin 5113, .pin 7, .pin 13, .pin 19⟩ ⟨(2, 143), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.pin 7789, .pin 7, .pin 13, .pin 19⟩ ⟨(4, 353), (223, 590), (109, 393), (209, 911)⟩))))) = true := by
  decide +kernel

private theorem u30_0_g2 :
    (leafOK (.c7, .c13, .c19) ⟨.pin 17293, .pin 7, .pin 13, .pin 19⟩ ⟨(2, 263), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.pin 28057, .pin 7, .pin 13, .pin 19⟩ ⟨(2, 335), (223, 590), (109, 393), (209, 911)⟩ &&
    (leafOK (.c7, .c13, .c19) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37], .pin 7, .pin 13, .pin 19⟩ ⟨(1, 5), (223, 590), (109, 393), (209, 911)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 13, 19)`, with 13 leaves. -/
def u30_0 : Tree :=
  .split 0 37
    (.leaf ⟨(145, 882), (223, 590), (109, 393), (209, 911)⟩)
    (.split 0 61
      (.leaf ⟨(79, 617), (223, 590), (109, 393), (209, 911)⟩)
      (.split 0 73
        (.leaf ⟨(57, 487), (223, 590), (109, 393), (209, 911)⟩)
        (.split 0 109
          (.leaf ⟨(25, 261), (223, 590), (109, 393), (209, 911)⟩)
          (.split 0 409
            (.leaf ⟨(9, 182), (223, 590), (109, 393), (209, 911)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (223, 590), (109, 393), (209, 911)⟩)
              (.split 0 2053
                (.leaf ⟨(13, 589), (223, 590), (109, 393), (209, 911)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (109, 393), (209, 911)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (109, 393), (209, 911)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (109, 393), (209, 911)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (109, 393), (209, 911)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (109, 393), (209, 911)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (109, 393), (209, 911)⟩))))))))))))

/-- Subtree 0 of the class triple `(7, 13, 19)` passes the check. -/
theorem u30_0_ok : treeOK (.c7, .c13, .c19)
    (rootNode (.c7, .c13, .c19)) u30_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u30_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u30_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u30_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u30_0_g2).2).2))))))))))))

private theorem u31_0_g0 :
    (leafOK (.c7, .c13, .c31) ⟨.pin 37, .pin 7, .pin 13, .pin 31⟩ ⟨(145, 882), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.pin 61, .pin 7, .pin 13, .pin 31⟩ ⟨(79, 617), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.pin 73, .pin 7, .pin 13, .pin 31⟩ ⟨(57, 487), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.pin 109, .pin 7, .pin 13, .pin 31⟩ ⟨(25, 261), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.pin 409, .pin 7, .pin 13, .pin 31⟩ ⟨(9, 182), (223, 590), (109, 393), (155, 863)⟩))))) = true := by
  decide +kernel

private theorem u31_0_g1 :
    (leafOK (.c7, .c13, .c31) ⟨.pin 709, .pin 7, .pin 13, .pin 31⟩ ⟨(8, 213), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.pin 3541, .pin 7, .pin 13, .pin 31⟩ ⟨(2, 119), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.pin 5113, .pin 7, .pin 13, .pin 31⟩ ⟨(2, 143), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.pin 7789, .pin 7, .pin 13, .pin 31⟩ ⟨(4, 353), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.pin 17293, .pin 7, .pin 13, .pin 31⟩ ⟨(2, 263), (223, 590), (109, 393), (155, 863)⟩))))) = true := by
  decide +kernel

private theorem u31_0_g2 :
    (leafOK (.c7, .c13, .c31) ⟨.pin 28057, .pin 7, .pin 13, .pin 31⟩ ⟨(2, 335), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.pin 25, .pin 7, .pin 13, .pin 31⟩ ⟨(1, 5), (223, 590), (109, 393), (155, 863)⟩ &&
    (leafOK (.c7, .c13, .c31) ⟨.free .q 13 [25, 28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37], .pin 7, .pin 13, .pin 31⟩ ⟨(1, 7), (223, 590), (109, 393), (155, 863)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 13, 31)`, with 13 leaves. -/
def u31_0 : Tree :=
  .split 0 37
    (.leaf ⟨(145, 882), (223, 590), (109, 393), (155, 863)⟩)
    (.split 0 61
      (.leaf ⟨(79, 617), (223, 590), (109, 393), (155, 863)⟩)
      (.split 0 73
        (.leaf ⟨(57, 487), (223, 590), (109, 393), (155, 863)⟩)
        (.split 0 109
          (.leaf ⟨(25, 261), (223, 590), (109, 393), (155, 863)⟩)
          (.split 0 409
            (.leaf ⟨(9, 182), (223, 590), (109, 393), (155, 863)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (223, 590), (109, 393), (155, 863)⟩)
              (.split 0 3541
                (.leaf ⟨(2, 119), (223, 590), (109, 393), (155, 863)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (223, 590), (109, 393), (155, 863)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (223, 590), (109, 393), (155, 863)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (223, 590), (109, 393), (155, 863)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (223, 590), (109, 393), (155, 863)⟩)
                        (.split 0 25
                          (.leaf ⟨(1, 5), (223, 590), (109, 393), (155, 863)⟩)
                          (.leaf ⟨(1, 7), (223, 590), (109, 393), (155, 863)⟩))))))))))))

/-- Subtree 0 of the class triple `(7, 13, 31)` passes the check. -/
theorem u31_0_ok : treeOK (.c7, .c13, .c31)
    (rootNode (.c7, .c13, .c31)) u31_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u31_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u31_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u31_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u31_0_g2).2).2))))))))))))

private theorem u32_0_g0 :
    leafOK (.c7, .c13, .c37) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 37⟩ ⟨(1, 5), (223, 590), (109, 393), (145, 882)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 13, 37)`, with 1 leaves. -/
def u32_0 : Tree :=
  .leaf ⟨(1, 5), (223, 590), (109, 393), (145, 882)⟩

/-- Subtree 0 of the class triple `(7, 13, 37)` passes the check. -/
theorem u32_0_ok : treeOK (.c7, .c13, .c37)
    (rootNode (.c7, .c13, .c37)) u32_0 = true :=
  treeOK_leaf u32_0_g0

private theorem u33_0_g0 :
    leafOK (.c7, .c13, .c43) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 43⟩ ⟨(1, 5), (223, 590), (109, 393), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 13, 43)`, with 1 leaves. -/
def u33_0 : Tree :=
  .leaf ⟨(1, 5), (223, 590), (109, 393), (61, 400)⟩

/-- Subtree 0 of the class triple `(7, 13, 43)` passes the check. -/
theorem u33_0_ok : treeOK (.c7, .c13, .c43)
    (rootNode (.c7, .c13, .c43)) u33_0 = true :=
  treeOK_leaf u33_0_g0

private theorem u34_0_g0 :
    leafOK (.c7, .c13, .n2) ⟨.free .q 13 [], .pin 7, .pin 13, .free .n2 11 []⟩ ⟨(1, 5), (223, 590), (109, 393), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 13, n2)`, with 1 leaves. -/
def u34_0 : Tree :=
  .leaf ⟨(1, 5), (223, 590), (109, 393), (0, 1)⟩

/-- Subtree 0 of the class triple `(7, 13, n2)` passes the check. -/
theorem u34_0_ok : treeOK (.c7, .c13, .n2)
    (rootNode (.c7, .c13, .n2)) u34_0 = true :=
  treeOK_leaf u34_0_g0

private theorem u35_0_g0 :
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 61⟩ ⟨(1, 5), (223, 590), (109, 393), (79, 617)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 67⟩ ⟨(1, 5), (223, 590), (109, 393), (27, 221)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 73⟩ ⟨(1, 5), (223, 590), (109, 393), (57, 487)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 79⟩ ⟨(1, 5), (223, 590), (109, 393), (107, 951)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 109⟩ ⟨(1, 5), (223, 590), (109, 393), (25, 261)⟩))))) = true := by
  decide +kernel

private theorem u35_0_g1 :
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 127⟩ ⟨(1, 5), (223, 590), (109, 393), (26, 293)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 151⟩ ⟨(1, 5), (223, 590), (109, 393), (59, 725)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 307⟩ ⟨(1, 5), (223, 590), (109, 393), (48, 841)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 409⟩ ⟨(1, 5), (223, 590), (109, 393), (9, 182)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 709⟩ ⟨(1, 5), (223, 590), (109, 393), (8, 213)⟩))))) = true := by
  decide +kernel

private theorem u35_0_g2 :
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 727⟩ ⟨(1, 5), (223, 590), (109, 393), (26, 701)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 991⟩ ⟨(1, 5), (223, 590), (109, 393), (25, 787)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 1087⟩ ⟨(1, 5), (223, 590), (109, 393), (30, 989)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 1723⟩ ⟨(1, 5), (223, 590), (109, 393), (2, 83)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 3541⟩ ⟨(1, 5), (223, 590), (109, 393), (2, 119)⟩))))) = true := by
  decide +kernel

private theorem u35_0_g3 :
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 4603⟩ ⟨(1, 5), (223, 590), (109, 393), (6, 407)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 5113⟩ ⟨(1, 5), (223, 590), (109, 393), (2, 143)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 7789⟩ ⟨(1, 5), (223, 590), (109, 393), (4, 353)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 8011⟩ ⟨(1, 5), (223, 590), (109, 393), (2, 179)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 10303⟩ ⟨(1, 5), (223, 590), (109, 393), (2, 203)⟩))))) = true := by
  decide +kernel

private theorem u35_0_g4 :
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 17293⟩ ⟨(1, 5), (223, 590), (109, 393), (2, 263)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 28057⟩ ⟨(1, 5), (223, 590), (109, 393), (2, 335)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 30103⟩ ⟨(1, 5), (223, 590), (109, 393), (2, 347)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .pin 86143⟩ ⟨(1, 5), (223, 590), (109, 393), (2, 587)⟩ &&
    (leafOK (.c7, .c13, .big) ⟨.free .q 13 [], .pin 7, .pin 13, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(1, 5), (223, 590), (109, 393), (1, 8)⟩))))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 13, big)`, with 25 leaves. -/
def u35_0 : Tree :=
  .split 3 61
    (.leaf ⟨(1, 5), (223, 590), (109, 393), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(1, 5), (223, 590), (109, 393), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(1, 5), (223, 590), (109, 393), (57, 487)⟩)
        (.split 3 79
          (.leaf ⟨(1, 5), (223, 590), (109, 393), (107, 951)⟩)
          (.split 3 109
            (.leaf ⟨(1, 5), (223, 590), (109, 393), (25, 261)⟩)
            (.split 3 127
              (.leaf ⟨(1, 5), (223, 590), (109, 393), (26, 293)⟩)
              (.split 3 151
                (.leaf ⟨(1, 5), (223, 590), (109, 393), (59, 725)⟩)
                (.split 3 307
                  (.leaf ⟨(1, 5), (223, 590), (109, 393), (48, 841)⟩)
                  (.split 3 409
                    (.leaf ⟨(1, 5), (223, 590), (109, 393), (9, 182)⟩)
                    (.split 3 709
                      (.leaf ⟨(1, 5), (223, 590), (109, 393), (8, 213)⟩)
                      (.split 3 727
                        (.leaf ⟨(1, 5), (223, 590), (109, 393), (26, 701)⟩)
                        (.split 3 991
                          (.leaf ⟨(1, 5), (223, 590), (109, 393), (25, 787)⟩)
                          (.split 3 1087
                            (.leaf ⟨(1, 5), (223, 590), (109, 393), (30, 989)⟩)
                            (.split 3 1723
                              (.leaf ⟨(1, 5), (223, 590), (109, 393), (2, 83)⟩)
                              (.split 3 3541
                                (.leaf ⟨(1, 5), (223, 590), (109, 393), (2, 119)⟩)
                                (.split 3 4603
                                  (.leaf ⟨(1, 5), (223, 590), (109, 393), (6, 407)⟩)
                                  (.split 3 5113
                                    (.leaf ⟨(1, 5), (223, 590), (109, 393), (2, 143)⟩)
                                    (.split 3 7789
                                      (.leaf ⟨(1, 5), (223, 590), (109, 393), (4, 353)⟩)
                                      (.split 3 8011
                                        (.leaf ⟨(1, 5), (223, 590), (109, 393), (2, 179)⟩)
                                        (.split 3 10303
                                          (.leaf ⟨(1, 5), (223, 590), (109, 393), (2, 203)⟩)
                                          (.split 3 17293
                                            (.leaf ⟨(1, 5), (223, 590), (109, 393), (2, 263)⟩)
                                            (.split 3 28057
                                              (.leaf ⟨(1, 5), (223, 590), (109, 393), (2, 335)⟩)
                                              (.split 3 30103
                                                (.leaf ⟨(1, 5), (223, 590), (109, 393), (2, 347)⟩)
                                                (.split 3 86143
                                                  (.leaf ⟨(1, 5), (223, 590), (109, 393), (2, 587)⟩)
                                                  (.leaf ⟨(1, 5), (223, 590), (109, 393), (1, 8)⟩))))))))))))))))))))))))

/-- Subtree 0 of the class triple `(7, 13, big)` passes the check. -/
theorem u35_0_ok : treeOK (.c7, .c13, .big)
    (rootNode (.c7, .c13, .big)) u35_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u35_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u35_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u35_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u35_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g3).2).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g3).2).2).2).2)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp u35_0_g4).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g4).2).1)
                                              (treeOK_split (by decide) rfl
                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g4).2).2).1)
                                                (treeOK_split (by decide) rfl
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g4).2).2).2).1)
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u35_0_g4).2).2).2).2))))))))))))))))))))))))

private theorem u36_0_g0 :
    (leafOK (.c7, .c19, .c31) ⟨.pin 13, .pin 7, .pin 19, .pin 31⟩ ⟨(109, 393), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 37, .pin 7, .pin 19, .pin 31⟩ ⟨(145, 882), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 61, .pin 7, .pin 19, .pin 31⟩ ⟨(79, 617), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 73, .pin 7, .pin 19, .pin 31⟩ ⟨(57, 487), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 109, .pin 7, .pin 19, .pin 31⟩ ⟨(25, 261), (223, 590), (209, 911), (155, 863)⟩))))) = true := by
  decide +kernel

private theorem u36_0_g1 :
    (leafOK (.c7, .c19, .c31) ⟨.pin 409, .pin 7, .pin 19, .pin 31⟩ ⟨(9, 182), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 709, .pin 7, .pin 19, .pin 31⟩ ⟨(8, 213), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 2053, .pin 7, .pin 19, .pin 31⟩ ⟨(13, 589), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 3541, .pin 7, .pin 19, .pin 31⟩ ⟨(2, 119), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 5113, .pin 7, .pin 19, .pin 31⟩ ⟨(2, 143), (223, 590), (209, 911), (155, 863)⟩))))) = true := by
  decide +kernel

private theorem u36_0_g2 :
    (leafOK (.c7, .c19, .c31) ⟨.pin 7789, .pin 7, .pin 19, .pin 31⟩ ⟨(4, 353), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 17293, .pin 7, .pin 19, .pin 31⟩ ⟨(2, 263), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 28057, .pin 7, .pin 19, .pin 31⟩ ⟨(2, 335), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 25, .pin 7, .pin 19, .pin 31⟩ ⟨(1, 5), (223, 590), (209, 911), (155, 863)⟩ &&
    (leafOK (.c7, .c19, .c31) ⟨.pin 49, .pin 7, .pin 19, .pin 31⟩ ⟨(1, 7), (223, 590), (209, 911), (155, 863)⟩))))) = true := by
  decide +kernel

private theorem u36_0_g3 :
    leafOK (.c7, .c19, .c31) ⟨.free .q 13 [49, 25, 28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 19, .pin 31⟩ ⟨(41, 378), (223, 590), (209, 911), (155, 863)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 19, 31)`, with 16 leaves. -/
def u36_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (209, 911), (155, 863)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (209, 911), (155, 863)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (209, 911), (155, 863)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (209, 911), (155, 863)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (209, 911), (155, 863)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (209, 911), (155, 863)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (209, 911), (155, 863)⟩)
                (.split 0 2053
                  (.leaf ⟨(13, 589), (223, 590), (209, 911), (155, 863)⟩)
                  (.split 0 3541
                    (.leaf ⟨(2, 119), (223, 590), (209, 911), (155, 863)⟩)
                    (.split 0 5113
                      (.leaf ⟨(2, 143), (223, 590), (209, 911), (155, 863)⟩)
                      (.split 0 7789
                        (.leaf ⟨(4, 353), (223, 590), (209, 911), (155, 863)⟩)
                        (.split 0 17293
                          (.leaf ⟨(2, 263), (223, 590), (209, 911), (155, 863)⟩)
                          (.split 0 28057
                            (.leaf ⟨(2, 335), (223, 590), (209, 911), (155, 863)⟩)
                            (.split 0 25
                              (.leaf ⟨(1, 5), (223, 590), (209, 911), (155, 863)⟩)
                              (.split 0 49
                                (.leaf ⟨(1, 7), (223, 590), (209, 911), (155, 863)⟩)
                                (.leaf ⟨(41, 378), (223, 590), (209, 911), (155, 863)⟩)))))))))))))))

/-- Subtree 0 of the class triple `(7, 19, 31)` passes the check. -/
theorem u36_0_ok : treeOK (.c7, .c19, .c31)
    (rootNode (.c7, .c19, .c31)) u36_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u36_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u36_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u36_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u36_0_g2).2).2).2).2)
                                (treeOK_leaf u36_0_g3)))))))))))))))

private theorem u37_0_g0 :
    (leafOK (.c7, .c19, .c37) ⟨.pin 13, .pin 7, .pin 19, .pin 37⟩ ⟨(109, 393), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.pin 61, .pin 7, .pin 19, .pin 37⟩ ⟨(79, 617), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.pin 73, .pin 7, .pin 19, .pin 37⟩ ⟨(57, 487), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.pin 109, .pin 7, .pin 19, .pin 37⟩ ⟨(25, 261), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.pin 409, .pin 7, .pin 19, .pin 37⟩ ⟨(9, 182), (223, 590), (209, 911), (145, 882)⟩))))) = true := by
  decide +kernel

private theorem u37_0_g1 :
    (leafOK (.c7, .c19, .c37) ⟨.pin 709, .pin 7, .pin 19, .pin 37⟩ ⟨(8, 213), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.pin 2053, .pin 7, .pin 19, .pin 37⟩ ⟨(13, 589), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.pin 3541, .pin 7, .pin 19, .pin 37⟩ ⟨(2, 119), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.pin 5113, .pin 7, .pin 19, .pin 37⟩ ⟨(2, 143), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.pin 7789, .pin 7, .pin 19, .pin 37⟩ ⟨(4, 353), (223, 590), (209, 911), (145, 882)⟩))))) = true := by
  decide +kernel

private theorem u37_0_g2 :
    (leafOK (.c7, .c19, .c37) ⟨.pin 17293, .pin 7, .pin 19, .pin 37⟩ ⟨(2, 263), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.pin 28057, .pin 7, .pin 19, .pin 37⟩ ⟨(2, 335), (223, 590), (209, 911), (145, 882)⟩ &&
    (leafOK (.c7, .c19, .c37) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 13], .pin 7, .pin 19, .pin 37⟩ ⟨(1, 5), (223, 590), (209, 911), (145, 882)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 19, 37)`, with 13 leaves. -/
def u37_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (209, 911), (145, 882)⟩)
    (.split 0 61
      (.leaf ⟨(79, 617), (223, 590), (209, 911), (145, 882)⟩)
      (.split 0 73
        (.leaf ⟨(57, 487), (223, 590), (209, 911), (145, 882)⟩)
        (.split 0 109
          (.leaf ⟨(25, 261), (223, 590), (209, 911), (145, 882)⟩)
          (.split 0 409
            (.leaf ⟨(9, 182), (223, 590), (209, 911), (145, 882)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (223, 590), (209, 911), (145, 882)⟩)
              (.split 0 2053
                (.leaf ⟨(13, 589), (223, 590), (209, 911), (145, 882)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (209, 911), (145, 882)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (209, 911), (145, 882)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (209, 911), (145, 882)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (209, 911), (145, 882)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (209, 911), (145, 882)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (209, 911), (145, 882)⟩))))))))))))

/-- Subtree 0 of the class triple `(7, 19, 37)` passes the check. -/
theorem u37_0_ok : treeOK (.c7, .c19, .c37)
    (rootNode (.c7, .c19, .c37)) u37_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u37_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u37_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u37_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u37_0_g2).2).2))))))))))))

private theorem u38_0_g0 :
    (leafOK (.c7, .c19, .c43) ⟨.pin 13, .pin 7, .pin 19, .pin 43⟩ ⟨(109, 393), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 37, .pin 7, .pin 19, .pin 43⟩ ⟨(145, 882), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 61, .pin 7, .pin 19, .pin 43⟩ ⟨(79, 617), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 73, .pin 7, .pin 19, .pin 43⟩ ⟨(57, 487), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 109, .pin 7, .pin 19, .pin 43⟩ ⟨(25, 261), (223, 590), (209, 911), (61, 400)⟩))))) = true := by
  decide +kernel

private theorem u38_0_g1 :
    (leafOK (.c7, .c19, .c43) ⟨.pin 409, .pin 7, .pin 19, .pin 43⟩ ⟨(9, 182), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 709, .pin 7, .pin 19, .pin 43⟩ ⟨(8, 213), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 2053, .pin 7, .pin 19, .pin 43⟩ ⟨(13, 589), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 3541, .pin 7, .pin 19, .pin 43⟩ ⟨(2, 119), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 5113, .pin 7, .pin 19, .pin 43⟩ ⟨(2, 143), (223, 590), (209, 911), (61, 400)⟩))))) = true := by
  decide +kernel

private theorem u38_0_g2 :
    (leafOK (.c7, .c19, .c43) ⟨.pin 7789, .pin 7, .pin 19, .pin 43⟩ ⟨(4, 353), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 17293, .pin 7, .pin 19, .pin 43⟩ ⟨(2, 263), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.pin 28057, .pin 7, .pin 19, .pin 43⟩ ⟨(2, 335), (223, 590), (209, 911), (61, 400)⟩ &&
    (leafOK (.c7, .c19, .c43) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 19, .pin 43⟩ ⟨(1, 5), (223, 590), (209, 911), (61, 400)⟩)))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 19, 43)`, with 14 leaves. -/
def u38_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (209, 911), (61, 400)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (209, 911), (61, 400)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (209, 911), (61, 400)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (209, 911), (61, 400)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (209, 911), (61, 400)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (209, 911), (61, 400)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (209, 911), (61, 400)⟩)
                (.split 0 2053
                  (.leaf ⟨(13, 589), (223, 590), (209, 911), (61, 400)⟩)
                  (.split 0 3541
                    (.leaf ⟨(2, 119), (223, 590), (209, 911), (61, 400)⟩)
                    (.split 0 5113
                      (.leaf ⟨(2, 143), (223, 590), (209, 911), (61, 400)⟩)
                      (.split 0 7789
                        (.leaf ⟨(4, 353), (223, 590), (209, 911), (61, 400)⟩)
                        (.split 0 17293
                          (.leaf ⟨(2, 263), (223, 590), (209, 911), (61, 400)⟩)
                          (.split 0 28057
                            (.leaf ⟨(2, 335), (223, 590), (209, 911), (61, 400)⟩)
                            (.leaf ⟨(1, 5), (223, 590), (209, 911), (61, 400)⟩)))))))))))))

/-- Subtree 0 of the class triple `(7, 19, 43)` passes the check. -/
theorem u38_0_ok : treeOK (.c7, .c19, .c43)
    (rootNode (.c7, .c19, .c43)) u38_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u38_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u38_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u38_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g2).2).2).1)
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u38_0_g2).2).2).2)))))))))))))

private theorem u39_0_g0 :
    (leafOK (.c7, .c19, .n2) ⟨.pin 13, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(109, 393), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 37, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(145, 882), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 61, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(79, 617), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 73, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(57, 487), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 109, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(25, 261), (223, 590), (209, 911), (0, 1)⟩))))) = true := by
  decide +kernel

private theorem u39_0_g1 :
    (leafOK (.c7, .c19, .n2) ⟨.pin 409, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(9, 182), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 709, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(8, 213), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 2053, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(13, 589), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 3541, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(2, 119), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 5113, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(2, 143), (223, 590), (209, 911), (0, 1)⟩))))) = true := by
  decide +kernel

private theorem u39_0_g2 :
    (leafOK (.c7, .c19, .n2) ⟨.pin 7789, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(4, 353), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 17293, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(2, 263), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.pin 28057, .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(2, 335), (223, 590), (209, 911), (0, 1)⟩ &&
    (leafOK (.c7, .c19, .n2) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 19, .free .n2 11 []⟩ ⟨(1, 5), (223, 590), (209, 911), (0, 1)⟩)))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 19, n2)`, with 14 leaves. -/
def u39_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (209, 911), (0, 1)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (209, 911), (0, 1)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (209, 911), (0, 1)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (209, 911), (0, 1)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (209, 911), (0, 1)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (209, 911), (0, 1)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (209, 911), (0, 1)⟩)
                (.split 0 2053
                  (.leaf ⟨(13, 589), (223, 590), (209, 911), (0, 1)⟩)
                  (.split 0 3541
                    (.leaf ⟨(2, 119), (223, 590), (209, 911), (0, 1)⟩)
                    (.split 0 5113
                      (.leaf ⟨(2, 143), (223, 590), (209, 911), (0, 1)⟩)
                      (.split 0 7789
                        (.leaf ⟨(4, 353), (223, 590), (209, 911), (0, 1)⟩)
                        (.split 0 17293
                          (.leaf ⟨(2, 263), (223, 590), (209, 911), (0, 1)⟩)
                          (.split 0 28057
                            (.leaf ⟨(2, 335), (223, 590), (209, 911), (0, 1)⟩)
                            (.leaf ⟨(1, 5), (223, 590), (209, 911), (0, 1)⟩)))))))))))))

/-- Subtree 0 of the class triple `(7, 19, n2)` passes the check. -/
theorem u39_0_ok : treeOK (.c7, .c19, .n2)
    (rootNode (.c7, .c19, .n2)) u39_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u39_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u39_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u39_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g2).2).2).1)
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u39_0_g2).2).2).2)))))))))))))

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u30_0_ok
#print axioms OddPerfect.ThreeFreeThree.u31_0_ok
#print axioms OddPerfect.ThreeFreeThree.u32_0_ok
#print axioms OddPerfect.ThreeFreeThree.u33_0_ok
#print axioms OddPerfect.ThreeFreeThree.u34_0_ok
#print axioms OddPerfect.ThreeFreeThree.u35_0_ok
#print axioms OddPerfect.ThreeFreeThree.u36_0_ok
#print axioms OddPerfect.ThreeFreeThree.u37_0_ok
#print axioms OddPerfect.ThreeFreeThree.u38_0_ok
#print axioms OddPerfect.ThreeFreeThree.u39_0_ok
