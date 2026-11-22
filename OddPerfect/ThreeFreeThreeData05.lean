import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 5

Subtrees of the case analysis certificate for the class triples `(7, 31, 43)`,
`(7, 31, n2)`, `(7, 31, big)` (part), with 127 leaves in all. Each public theorem states
that a subtree passes `treeOK` from explicit constraints. The data was found by a
search outside Lean; everything in this file is rechecked by the kernel through
`decide +kernel` on the leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u42_0_g0 :
    (leafOK (.c7, .c31, .c43) ⟨.pin 13, .pin 7, .pin 31, .pin 43⟩ ⟨(109, 393), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.pin 37, .pin 7, .pin 31, .pin 43⟩ ⟨(145, 882), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.pin 61, .pin 7, .pin 31, .pin 43⟩ ⟨(79, 617), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.pin 73, .pin 7, .pin 31, .pin 43⟩ ⟨(57, 487), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.pin 109, .pin 7, .pin 31, .pin 43⟩ ⟨(25, 261), (223, 590), (155, 863), (61, 400)⟩))))) = true := by
  decide +kernel

private theorem u42_0_g1 :
    (leafOK (.c7, .c31, .c43) ⟨.pin 409, .pin 7, .pin 31, .pin 43⟩ ⟨(9, 182), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.pin 709, .pin 7, .pin 31, .pin 43⟩ ⟨(8, 213), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.pin 3541, .pin 7, .pin 31, .pin 43⟩ ⟨(2, 119), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.pin 5113, .pin 7, .pin 31, .pin 43⟩ ⟨(2, 143), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.pin 7789, .pin 7, .pin 31, .pin 43⟩ ⟨(4, 353), (223, 590), (155, 863), (61, 400)⟩))))) = true := by
  decide +kernel

private theorem u42_0_g2 :
    (leafOK (.c7, .c31, .c43) ⟨.pin 17293, .pin 7, .pin 31, .pin 43⟩ ⟨(2, 263), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.pin 28057, .pin 7, .pin 31, .pin 43⟩ ⟨(2, 335), (223, 590), (155, 863), (61, 400)⟩ &&
    (leafOK (.c7, .c31, .c43) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 43⟩ ⟨(1, 5), (223, 590), (155, 863), (61, 400)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 31, 43)`, with 13 leaves. -/
def u42_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (61, 400)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (61, 400)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (61, 400)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (61, 400)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (61, 400)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (61, 400)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (61, 400)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (61, 400)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (61, 400)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (61, 400)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (61, 400)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (61, 400)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (61, 400)⟩))))))))))))

/-- Subtree 0 of the class triple `(7, 31, 43)` passes the check. -/
theorem u42_0_ok : treeOK (.c7, .c31, .c43)
    (rootNode (.c7, .c31, .c43)) u42_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u42_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u42_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u42_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u42_0_g2).2).2))))))))))))

private theorem u43_0_g0 :
    (leafOK (.c7, .c31, .n2) ⟨.pin 13, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(109, 393), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.pin 37, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(145, 882), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.pin 61, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(79, 617), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.pin 73, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(57, 487), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.pin 109, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(25, 261), (223, 590), (155, 863), (0, 1)⟩))))) = true := by
  decide +kernel

private theorem u43_0_g1 :
    (leafOK (.c7, .c31, .n2) ⟨.pin 409, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(9, 182), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.pin 709, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(8, 213), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.pin 3541, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(2, 119), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.pin 5113, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(2, 143), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.pin 7789, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(4, 353), (223, 590), (155, 863), (0, 1)⟩))))) = true := by
  decide +kernel

private theorem u43_0_g2 :
    (leafOK (.c7, .c31, .n2) ⟨.pin 17293, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(2, 263), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.pin 28057, .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(2, 335), (223, 590), (155, 863), (0, 1)⟩ &&
    (leafOK (.c7, .c31, .n2) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .free .n2 11 []⟩ ⟨(1, 5), (223, 590), (155, 863), (0, 1)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 31, n2)`, with 13 leaves. -/
def u43_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (0, 1)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (0, 1)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (0, 1)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (0, 1)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (0, 1)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (0, 1)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (0, 1)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (0, 1)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (0, 1)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (0, 1)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (0, 1)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (0, 1)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (0, 1)⟩))))))))))))

/-- Subtree 0 of the class triple `(7, 31, n2)` passes the check. -/
theorem u43_0_ok : treeOK (.c7, .c31, .n2)
    (rootNode (.c7, .c31, .n2)) u43_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u43_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u43_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u43_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u43_0_g2).2).2))))))))))))

private theorem u44_0_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 61⟩ ⟨(109, 393), (223, 590), (155, 863), (79, 617)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 61⟩ ⟨(145, 882), (223, 590), (155, 863), (79, 617)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 61⟩ ⟨(57, 487), (223, 590), (155, 863), (79, 617)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 61⟩ ⟨(25, 261), (223, 590), (155, 863), (79, 617)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 61⟩ ⟨(9, 182), (223, 590), (155, 863), (79, 617)⟩))))) = true := by
  decide +kernel

private theorem u44_0_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 61⟩ ⟨(8, 213), (223, 590), (155, 863), (79, 617)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 61⟩ ⟨(2, 119), (223, 590), (155, 863), (79, 617)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 61⟩ ⟨(2, 143), (223, 590), (155, 863), (79, 617)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 61⟩ ⟨(4, 353), (223, 590), (155, 863), (79, 617)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 61⟩ ⟨(2, 263), (223, 590), (155, 863), (79, 617)⟩))))) = true := by
  decide +kernel

private theorem u44_0_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 61⟩ ⟨(2, 335), (223, 590), (155, 863), (79, 617)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 37, 13], .pin 7, .pin 31, .pin 61⟩ ⟨(1, 5), (223, 590), (155, 863), (79, 617)⟩)) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 31, big)`, with 12 leaves. -/
def u44_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (79, 617)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (79, 617)⟩)
      (.split 0 73
        (.leaf ⟨(57, 487), (223, 590), (155, 863), (79, 617)⟩)
        (.split 0 109
          (.leaf ⟨(25, 261), (223, 590), (155, 863), (79, 617)⟩)
          (.split 0 409
            (.leaf ⟨(9, 182), (223, 590), (155, 863), (79, 617)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (223, 590), (155, 863), (79, 617)⟩)
              (.split 0 3541
                (.leaf ⟨(2, 119), (223, 590), (155, 863), (79, 617)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (223, 590), (155, 863), (79, 617)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (223, 590), (155, 863), (79, 617)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (223, 590), (155, 863), (79, 617)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (223, 590), (155, 863), (79, 617)⟩)
                        (.leaf ⟨(1, 5), (223, 590), (155, 863), (79, 617)⟩)))))))))))

/-- Subtree 0 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_0_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 61⟩ u44_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_0_g2).1)
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_0_g2).2)))))))))))

private theorem u44_1_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 67⟩ ⟨(109, 393), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 67⟩ ⟨(145, 882), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 67⟩ ⟨(79, 617), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 67⟩ ⟨(57, 487), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 67⟩ ⟨(25, 261), (223, 590), (155, 863), (27, 221)⟩))))) = true := by
  decide +kernel

private theorem u44_1_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 67⟩ ⟨(9, 182), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 67⟩ ⟨(8, 213), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 67⟩ ⟨(2, 119), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 67⟩ ⟨(2, 143), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 67⟩ ⟨(4, 353), (223, 590), (155, 863), (27, 221)⟩))))) = true := by
  decide +kernel

private theorem u44_1_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 67⟩ ⟨(2, 263), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 67⟩ ⟨(2, 335), (223, 590), (155, 863), (27, 221)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 67⟩ ⟨(1, 5), (223, 590), (155, 863), (27, 221)⟩))) = true := by
  decide +kernel

/-- Subtree 1 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_1 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (27, 221)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (27, 221)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (27, 221)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (27, 221)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (27, 221)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (27, 221)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (27, 221)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (27, 221)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (27, 221)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (27, 221)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (27, 221)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (27, 221)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (27, 221)⟩))))))))))))

/-- Subtree 1 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_1_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 67⟩ u44_1 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_1_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_1_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_1_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_1_g2).2).2))))))))))))

private theorem u44_2_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 73⟩ ⟨(109, 393), (223, 590), (155, 863), (57, 487)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 73⟩ ⟨(145, 882), (223, 590), (155, 863), (57, 487)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 73⟩ ⟨(79, 617), (223, 590), (155, 863), (57, 487)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 73⟩ ⟨(25, 261), (223, 590), (155, 863), (57, 487)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 73⟩ ⟨(9, 182), (223, 590), (155, 863), (57, 487)⟩))))) = true := by
  decide +kernel

private theorem u44_2_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 73⟩ ⟨(8, 213), (223, 590), (155, 863), (57, 487)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 73⟩ ⟨(2, 119), (223, 590), (155, 863), (57, 487)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 73⟩ ⟨(2, 143), (223, 590), (155, 863), (57, 487)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 73⟩ ⟨(4, 353), (223, 590), (155, 863), (57, 487)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 73⟩ ⟨(2, 263), (223, 590), (155, 863), (57, 487)⟩))))) = true := by
  decide +kernel

private theorem u44_2_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 73⟩ ⟨(2, 335), (223, 590), (155, 863), (57, 487)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 61, 37, 13], .pin 7, .pin 31, .pin 73⟩ ⟨(1, 5), (223, 590), (155, 863), (57, 487)⟩)) = true := by
  decide +kernel

/-- Subtree 2 of the class triple `(7, 31, big)`, with 12 leaves. -/
def u44_2 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (57, 487)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (57, 487)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (57, 487)⟩)
        (.split 0 109
          (.leaf ⟨(25, 261), (223, 590), (155, 863), (57, 487)⟩)
          (.split 0 409
            (.leaf ⟨(9, 182), (223, 590), (155, 863), (57, 487)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (223, 590), (155, 863), (57, 487)⟩)
              (.split 0 3541
                (.leaf ⟨(2, 119), (223, 590), (155, 863), (57, 487)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (223, 590), (155, 863), (57, 487)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (223, 590), (155, 863), (57, 487)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (223, 590), (155, 863), (57, 487)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (223, 590), (155, 863), (57, 487)⟩)
                        (.leaf ⟨(1, 5), (223, 590), (155, 863), (57, 487)⟩)))))))))))

/-- Subtree 2 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_2_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 73⟩ u44_2 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_2_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_2_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_2_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_2_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_2_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_2_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_2_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_2_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_2_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_2_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_2_g2).1)
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_2_g2).2)))))))))))

private theorem u44_3_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 79⟩ ⟨(109, 393), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 79⟩ ⟨(145, 882), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 79⟩ ⟨(79, 617), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 79⟩ ⟨(57, 487), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 79⟩ ⟨(25, 261), (223, 590), (155, 863), (107, 951)⟩))))) = true := by
  decide +kernel

private theorem u44_3_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 79⟩ ⟨(9, 182), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 79⟩ ⟨(8, 213), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 79⟩ ⟨(2, 119), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 79⟩ ⟨(2, 143), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 79⟩ ⟨(4, 353), (223, 590), (155, 863), (107, 951)⟩))))) = true := by
  decide +kernel

private theorem u44_3_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 79⟩ ⟨(2, 263), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 79⟩ ⟨(2, 335), (223, 590), (155, 863), (107, 951)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 79⟩ ⟨(1, 5), (223, 590), (155, 863), (107, 951)⟩))) = true := by
  decide +kernel

/-- Subtree 3 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_3 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (107, 951)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (107, 951)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (107, 951)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (107, 951)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (107, 951)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (107, 951)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (107, 951)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (107, 951)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (107, 951)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (107, 951)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (107, 951)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (107, 951)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (107, 951)⟩))))))))))))

/-- Subtree 3 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_3_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 79⟩ u44_3 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_3_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_3_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_3_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_3_g2).2).2))))))))))))

private theorem u44_4_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 103⟩ ⟨(109, 393), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 103⟩ ⟨(145, 882), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 103⟩ ⟨(79, 617), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 103⟩ ⟨(57, 487), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 103⟩ ⟨(25, 261), (223, 590), (155, 863), (74, 751)⟩))))) = true := by
  decide +kernel

private theorem u44_4_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 103⟩ ⟨(9, 182), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 103⟩ ⟨(8, 213), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 103⟩ ⟨(2, 119), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 103⟩ ⟨(2, 143), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 103⟩ ⟨(4, 353), (223, 590), (155, 863), (74, 751)⟩))))) = true := by
  decide +kernel

private theorem u44_4_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 103⟩ ⟨(2, 263), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 103⟩ ⟨(2, 335), (223, 590), (155, 863), (74, 751)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 103⟩ ⟨(1, 5), (223, 590), (155, 863), (74, 751)⟩))) = true := by
  decide +kernel

/-- Subtree 4 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_4 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (74, 751)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (74, 751)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (74, 751)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (74, 751)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (74, 751)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (74, 751)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (74, 751)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (74, 751)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (74, 751)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (74, 751)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (74, 751)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (74, 751)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (74, 751)⟩))))))))))))

/-- Subtree 4 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_4_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 103⟩ u44_4 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_4_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_4_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_4_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_4_g2).2).2))))))))))))

private theorem u44_5_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 109⟩ ⟨(109, 393), (223, 590), (155, 863), (25, 261)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 109⟩ ⟨(145, 882), (223, 590), (155, 863), (25, 261)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 109⟩ ⟨(79, 617), (223, 590), (155, 863), (25, 261)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 109⟩ ⟨(57, 487), (223, 590), (155, 863), (25, 261)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 109⟩ ⟨(9, 182), (223, 590), (155, 863), (25, 261)⟩))))) = true := by
  decide +kernel

private theorem u44_5_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 109⟩ ⟨(8, 213), (223, 590), (155, 863), (25, 261)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 109⟩ ⟨(2, 119), (223, 590), (155, 863), (25, 261)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 109⟩ ⟨(2, 143), (223, 590), (155, 863), (25, 261)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 109⟩ ⟨(4, 353), (223, 590), (155, 863), (25, 261)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 109⟩ ⟨(2, 263), (223, 590), (155, 863), (25, 261)⟩))))) = true := by
  decide +kernel

private theorem u44_5_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 109⟩ ⟨(2, 335), (223, 590), (155, 863), (25, 261)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 73, 61, 37, 13], .pin 7, .pin 31, .pin 109⟩ ⟨(1, 5), (223, 590), (155, 863), (25, 261)⟩)) = true := by
  decide +kernel

/-- Subtree 5 of the class triple `(7, 31, big)`, with 12 leaves. -/
def u44_5 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (25, 261)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (25, 261)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (25, 261)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (25, 261)⟩)
          (.split 0 409
            (.leaf ⟨(9, 182), (223, 590), (155, 863), (25, 261)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (223, 590), (155, 863), (25, 261)⟩)
              (.split 0 3541
                (.leaf ⟨(2, 119), (223, 590), (155, 863), (25, 261)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (223, 590), (155, 863), (25, 261)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (223, 590), (155, 863), (25, 261)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (223, 590), (155, 863), (25, 261)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (223, 590), (155, 863), (25, 261)⟩)
                        (.leaf ⟨(1, 5), (223, 590), (155, 863), (25, 261)⟩)))))))))))

/-- Subtree 5 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_5_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 109⟩ u44_5 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_5_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_5_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_5_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_5_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_5_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_5_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_5_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_5_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_5_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_5_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_5_g2).1)
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_5_g2).2)))))))))))

private theorem u44_6_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 127⟩ ⟨(109, 393), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 127⟩ ⟨(145, 882), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 127⟩ ⟨(79, 617), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 127⟩ ⟨(57, 487), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 127⟩ ⟨(25, 261), (223, 590), (155, 863), (26, 293)⟩))))) = true := by
  decide +kernel

private theorem u44_6_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 127⟩ ⟨(9, 182), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 127⟩ ⟨(8, 213), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 127⟩ ⟨(2, 119), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 127⟩ ⟨(2, 143), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 127⟩ ⟨(4, 353), (223, 590), (155, 863), (26, 293)⟩))))) = true := by
  decide +kernel

private theorem u44_6_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 127⟩ ⟨(2, 263), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 127⟩ ⟨(2, 335), (223, 590), (155, 863), (26, 293)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 127⟩ ⟨(1, 5), (223, 590), (155, 863), (26, 293)⟩))) = true := by
  decide +kernel

/-- Subtree 6 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_6 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (26, 293)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (26, 293)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (26, 293)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (26, 293)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (26, 293)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (26, 293)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (26, 293)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (26, 293)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (26, 293)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (26, 293)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (26, 293)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (26, 293)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (26, 293)⟩))))))))))))

/-- Subtree 6 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_6_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 127⟩ u44_6 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_6_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_6_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_6_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_6_g2).2).2))))))))))))

private theorem u44_7_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 151⟩ ⟨(109, 393), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 151⟩ ⟨(145, 882), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 151⟩ ⟨(79, 617), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 151⟩ ⟨(57, 487), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 151⟩ ⟨(25, 261), (223, 590), (155, 863), (59, 725)⟩))))) = true := by
  decide +kernel

private theorem u44_7_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 151⟩ ⟨(9, 182), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 151⟩ ⟨(8, 213), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 151⟩ ⟨(2, 119), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 151⟩ ⟨(2, 143), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 151⟩ ⟨(4, 353), (223, 590), (155, 863), (59, 725)⟩))))) = true := by
  decide +kernel

private theorem u44_7_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 151⟩ ⟨(2, 263), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 151⟩ ⟨(2, 335), (223, 590), (155, 863), (59, 725)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 151⟩ ⟨(1, 5), (223, 590), (155, 863), (59, 725)⟩))) = true := by
  decide +kernel

/-- Subtree 7 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_7 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (59, 725)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (59, 725)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (59, 725)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (59, 725)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (59, 725)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (59, 725)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (59, 725)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (59, 725)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (59, 725)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (59, 725)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (59, 725)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (59, 725)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (59, 725)⟩))))))))))))

/-- Subtree 7 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_7_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 151⟩ u44_7 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_7_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_7_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_7_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_7_g2).2).2))))))))))))

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u42_0_ok
#print axioms OddPerfect.ThreeFreeThree.u43_0_ok
#print axioms OddPerfect.ThreeFreeThree.u44_0_ok
#print axioms OddPerfect.ThreeFreeThree.u44_1_ok
#print axioms OddPerfect.ThreeFreeThree.u44_2_ok
#print axioms OddPerfect.ThreeFreeThree.u44_3_ok
#print axioms OddPerfect.ThreeFreeThree.u44_4_ok
#print axioms OddPerfect.ThreeFreeThree.u44_5_ok
#print axioms OddPerfect.ThreeFreeThree.u44_6_ok
#print axioms OddPerfect.ThreeFreeThree.u44_7_ok
