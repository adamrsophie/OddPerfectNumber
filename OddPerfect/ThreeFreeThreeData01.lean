import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 1

Subtrees of the case analysis certificate for the class triples `(5, 7, 13)`,
`(5, 7, 19)`, `(5, 7, 31)`, `(5, 7, 37)`, `(5, 7, 43)`, `(5, 7, n2)`, with 77 leaves in all.
Each public theorem states that a subtree passes `treeOK` from explicit constraints.
The data was found by a search outside Lean; everything in this file is rechecked by
the kernel through `decide +kernel` on the leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u0_0_g0 :
    (leafOK (.c5, .c7, .c13) ⟨.pin 37, .pin 5, .pin 7, .pin 13⟩ ⟨(145, 882), (0, 1), (223, 590), (109, 393)⟩ &&
    (leafOK (.c5, .c7, .c13) ⟨.pin 61, .pin 5, .pin 7, .pin 13⟩ ⟨(79, 617), (0, 1), (223, 590), (109, 393)⟩ &&
    (leafOK (.c5, .c7, .c13) ⟨.pin 73, .pin 5, .pin 7, .pin 13⟩ ⟨(57, 487), (0, 1), (223, 590), (109, 393)⟩ &&
    (leafOK (.c5, .c7, .c13) ⟨.pin 109, .pin 5, .pin 7, .pin 13⟩ ⟨(25, 261), (0, 1), (223, 590), (109, 393)⟩ &&
    (leafOK (.c5, .c7, .c13) ⟨.pin 409, .pin 5, .pin 7, .pin 13⟩ ⟨(9, 182), (0, 1), (223, 590), (109, 393)⟩))))) = true := by
  decide +kernel

private theorem u0_0_g1 :
    (leafOK (.c5, .c7, .c13) ⟨.pin 709, .pin 5, .pin 7, .pin 13⟩ ⟨(8, 213), (0, 1), (223, 590), (109, 393)⟩ &&
    (leafOK (.c5, .c7, .c13) ⟨.pin 3541, .pin 5, .pin 7, .pin 13⟩ ⟨(2, 119), (0, 1), (223, 590), (109, 393)⟩ &&
    (leafOK (.c5, .c7, .c13) ⟨.pin 5113, .pin 5, .pin 7, .pin 13⟩ ⟨(2, 143), (0, 1), (223, 590), (109, 393)⟩ &&
    (leafOK (.c5, .c7, .c13) ⟨.pin 7789, .pin 5, .pin 7, .pin 13⟩ ⟨(4, 353), (0, 1), (223, 590), (109, 393)⟩ &&
    (leafOK (.c5, .c7, .c13) ⟨.pin 17293, .pin 5, .pin 7, .pin 13⟩ ⟨(2, 263), (0, 1), (223, 590), (109, 393)⟩))))) = true := by
  decide +kernel

private theorem u0_0_g2 :
    (leafOK (.c5, .c7, .c13) ⟨.pin 28057, .pin 5, .pin 7, .pin 13⟩ ⟨(2, 335), (0, 1), (223, 590), (109, 393)⟩ &&
    (leafOK (.c5, .c7, .c13) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37], .pin 5, .pin 7, .pin 13⟩ ⟨(1, 5), (0, 1), (223, 590), (109, 393)⟩)) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 7, 13)`, with 12 leaves. -/
def u0_0 : Tree :=
  .split 0 37
    (.leaf ⟨(145, 882), (0, 1), (223, 590), (109, 393)⟩)
    (.split 0 61
      (.leaf ⟨(79, 617), (0, 1), (223, 590), (109, 393)⟩)
      (.split 0 73
        (.leaf ⟨(57, 487), (0, 1), (223, 590), (109, 393)⟩)
        (.split 0 109
          (.leaf ⟨(25, 261), (0, 1), (223, 590), (109, 393)⟩)
          (.split 0 409
            (.leaf ⟨(9, 182), (0, 1), (223, 590), (109, 393)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (0, 1), (223, 590), (109, 393)⟩)
              (.split 0 3541
                (.leaf ⟨(2, 119), (0, 1), (223, 590), (109, 393)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (0, 1), (223, 590), (109, 393)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (0, 1), (223, 590), (109, 393)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (0, 1), (223, 590), (109, 393)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (0, 1), (223, 590), (109, 393)⟩)
                        (.leaf ⟨(1, 5), (0, 1), (223, 590), (109, 393)⟩)))))))))))

/-- Subtree 0 of the class triple `(5, 7, 13)` passes the check. -/
theorem u0_0_ok : treeOK (.c5, .c7, .c13)
    (rootNode (.c5, .c7, .c13)) u0_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u0_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u0_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u0_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u0_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u0_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u0_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u0_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u0_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u0_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u0_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u0_0_g2).1)
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u0_0_g2).2)))))))))))

private theorem u1_0_g0 :
    (leafOK (.c5, .c7, .c19) ⟨.pin 13, .pin 5, .pin 7, .pin 19⟩ ⟨(109, 393), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 37, .pin 5, .pin 7, .pin 19⟩ ⟨(145, 882), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 61, .pin 5, .pin 7, .pin 19⟩ ⟨(79, 617), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 73, .pin 5, .pin 7, .pin 19⟩ ⟨(57, 487), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 109, .pin 5, .pin 7, .pin 19⟩ ⟨(25, 261), (0, 1), (223, 590), (209, 911)⟩))))) = true := by
  decide +kernel

private theorem u1_0_g1 :
    (leafOK (.c5, .c7, .c19) ⟨.pin 409, .pin 5, .pin 7, .pin 19⟩ ⟨(9, 182), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 709, .pin 5, .pin 7, .pin 19⟩ ⟨(8, 213), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 2053, .pin 5, .pin 7, .pin 19⟩ ⟨(13, 589), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 3541, .pin 5, .pin 7, .pin 19⟩ ⟨(2, 119), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 5113, .pin 5, .pin 7, .pin 19⟩ ⟨(2, 143), (0, 1), (223, 590), (209, 911)⟩))))) = true := by
  decide +kernel

private theorem u1_0_g2 :
    (leafOK (.c5, .c7, .c19) ⟨.pin 7789, .pin 5, .pin 7, .pin 19⟩ ⟨(4, 353), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 17293, .pin 5, .pin 7, .pin 19⟩ ⟨(2, 263), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.pin 28057, .pin 5, .pin 7, .pin 19⟩ ⟨(2, 335), (0, 1), (223, 590), (209, 911)⟩ &&
    (leafOK (.c5, .c7, .c19) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37, 13], .pin 5, .pin 7, .pin 19⟩ ⟨(1, 5), (0, 1), (223, 590), (209, 911)⟩)))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 7, 19)`, with 14 leaves. -/
def u1_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (0, 1), (223, 590), (209, 911)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (0, 1), (223, 590), (209, 911)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (0, 1), (223, 590), (209, 911)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (0, 1), (223, 590), (209, 911)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (0, 1), (223, 590), (209, 911)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (0, 1), (223, 590), (209, 911)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (0, 1), (223, 590), (209, 911)⟩)
                (.split 0 2053
                  (.leaf ⟨(13, 589), (0, 1), (223, 590), (209, 911)⟩)
                  (.split 0 3541
                    (.leaf ⟨(2, 119), (0, 1), (223, 590), (209, 911)⟩)
                    (.split 0 5113
                      (.leaf ⟨(2, 143), (0, 1), (223, 590), (209, 911)⟩)
                      (.split 0 7789
                        (.leaf ⟨(4, 353), (0, 1), (223, 590), (209, 911)⟩)
                        (.split 0 17293
                          (.leaf ⟨(2, 263), (0, 1), (223, 590), (209, 911)⟩)
                          (.split 0 28057
                            (.leaf ⟨(2, 335), (0, 1), (223, 590), (209, 911)⟩)
                            (.leaf ⟨(1, 5), (0, 1), (223, 590), (209, 911)⟩)))))))))))))

/-- Subtree 0 of the class triple `(5, 7, 19)` passes the check. -/
theorem u1_0_ok : treeOK (.c5, .c7, .c19)
    (rootNode (.c5, .c7, .c19)) u1_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u1_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u1_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u1_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g2).2).2).1)
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u1_0_g2).2).2).2)))))))))))))

private theorem u2_0_g0 :
    (leafOK (.c5, .c7, .c31) ⟨.pin 13, .pin 5, .pin 7, .pin 31⟩ ⟨(109, 393), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.pin 37, .pin 5, .pin 7, .pin 31⟩ ⟨(145, 882), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.pin 61, .pin 5, .pin 7, .pin 31⟩ ⟨(79, 617), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.pin 73, .pin 5, .pin 7, .pin 31⟩ ⟨(57, 487), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.pin 109, .pin 5, .pin 7, .pin 31⟩ ⟨(25, 261), (0, 1), (223, 590), (155, 863)⟩))))) = true := by
  decide +kernel

private theorem u2_0_g1 :
    (leafOK (.c5, .c7, .c31) ⟨.pin 409, .pin 5, .pin 7, .pin 31⟩ ⟨(9, 182), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.pin 709, .pin 5, .pin 7, .pin 31⟩ ⟨(8, 213), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.pin 3541, .pin 5, .pin 7, .pin 31⟩ ⟨(2, 119), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.pin 5113, .pin 5, .pin 7, .pin 31⟩ ⟨(2, 143), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.pin 7789, .pin 5, .pin 7, .pin 31⟩ ⟨(4, 353), (0, 1), (223, 590), (155, 863)⟩))))) = true := by
  decide +kernel

private theorem u2_0_g2 :
    (leafOK (.c5, .c7, .c31) ⟨.pin 17293, .pin 5, .pin 7, .pin 31⟩ ⟨(2, 263), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.pin 28057, .pin 5, .pin 7, .pin 31⟩ ⟨(2, 335), (0, 1), (223, 590), (155, 863)⟩ &&
    (leafOK (.c5, .c7, .c31) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 5, .pin 7, .pin 31⟩ ⟨(1, 5), (0, 1), (223, 590), (155, 863)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 7, 31)`, with 13 leaves. -/
def u2_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (0, 1), (223, 590), (155, 863)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (0, 1), (223, 590), (155, 863)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (0, 1), (223, 590), (155, 863)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (0, 1), (223, 590), (155, 863)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (0, 1), (223, 590), (155, 863)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (0, 1), (223, 590), (155, 863)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (0, 1), (223, 590), (155, 863)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (0, 1), (223, 590), (155, 863)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (0, 1), (223, 590), (155, 863)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (0, 1), (223, 590), (155, 863)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (0, 1), (223, 590), (155, 863)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (0, 1), (223, 590), (155, 863)⟩)
                          (.leaf ⟨(1, 5), (0, 1), (223, 590), (155, 863)⟩))))))))))))

/-- Subtree 0 of the class triple `(5, 7, 31)` passes the check. -/
theorem u2_0_ok : treeOK (.c5, .c7, .c31)
    (rootNode (.c5, .c7, .c31)) u2_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u2_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u2_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u2_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u2_0_g2).2).2))))))))))))

private theorem u3_0_g0 :
    (leafOK (.c5, .c7, .c37) ⟨.pin 13, .pin 5, .pin 7, .pin 37⟩ ⟨(109, 393), (0, 1), (223, 590), (145, 882)⟩ &&
    (leafOK (.c5, .c7, .c37) ⟨.pin 61, .pin 5, .pin 7, .pin 37⟩ ⟨(79, 617), (0, 1), (223, 590), (145, 882)⟩ &&
    (leafOK (.c5, .c7, .c37) ⟨.pin 73, .pin 5, .pin 7, .pin 37⟩ ⟨(57, 487), (0, 1), (223, 590), (145, 882)⟩ &&
    (leafOK (.c5, .c7, .c37) ⟨.pin 109, .pin 5, .pin 7, .pin 37⟩ ⟨(25, 261), (0, 1), (223, 590), (145, 882)⟩ &&
    (leafOK (.c5, .c7, .c37) ⟨.pin 409, .pin 5, .pin 7, .pin 37⟩ ⟨(9, 182), (0, 1), (223, 590), (145, 882)⟩))))) = true := by
  decide +kernel

private theorem u3_0_g1 :
    (leafOK (.c5, .c7, .c37) ⟨.pin 709, .pin 5, .pin 7, .pin 37⟩ ⟨(8, 213), (0, 1), (223, 590), (145, 882)⟩ &&
    (leafOK (.c5, .c7, .c37) ⟨.pin 3541, .pin 5, .pin 7, .pin 37⟩ ⟨(2, 119), (0, 1), (223, 590), (145, 882)⟩ &&
    (leafOK (.c5, .c7, .c37) ⟨.pin 5113, .pin 5, .pin 7, .pin 37⟩ ⟨(2, 143), (0, 1), (223, 590), (145, 882)⟩ &&
    (leafOK (.c5, .c7, .c37) ⟨.pin 7789, .pin 5, .pin 7, .pin 37⟩ ⟨(4, 353), (0, 1), (223, 590), (145, 882)⟩ &&
    (leafOK (.c5, .c7, .c37) ⟨.pin 17293, .pin 5, .pin 7, .pin 37⟩ ⟨(2, 263), (0, 1), (223, 590), (145, 882)⟩))))) = true := by
  decide +kernel

private theorem u3_0_g2 :
    (leafOK (.c5, .c7, .c37) ⟨.pin 28057, .pin 5, .pin 7, .pin 37⟩ ⟨(2, 335), (0, 1), (223, 590), (145, 882)⟩ &&
    (leafOK (.c5, .c7, .c37) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 13], .pin 5, .pin 7, .pin 37⟩ ⟨(1, 5), (0, 1), (223, 590), (145, 882)⟩)) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 7, 37)`, with 12 leaves. -/
def u3_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (0, 1), (223, 590), (145, 882)⟩)
    (.split 0 61
      (.leaf ⟨(79, 617), (0, 1), (223, 590), (145, 882)⟩)
      (.split 0 73
        (.leaf ⟨(57, 487), (0, 1), (223, 590), (145, 882)⟩)
        (.split 0 109
          (.leaf ⟨(25, 261), (0, 1), (223, 590), (145, 882)⟩)
          (.split 0 409
            (.leaf ⟨(9, 182), (0, 1), (223, 590), (145, 882)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (0, 1), (223, 590), (145, 882)⟩)
              (.split 0 3541
                (.leaf ⟨(2, 119), (0, 1), (223, 590), (145, 882)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (0, 1), (223, 590), (145, 882)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (0, 1), (223, 590), (145, 882)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (0, 1), (223, 590), (145, 882)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (0, 1), (223, 590), (145, 882)⟩)
                        (.leaf ⟨(1, 5), (0, 1), (223, 590), (145, 882)⟩)))))))))))

/-- Subtree 0 of the class triple `(5, 7, 37)` passes the check. -/
theorem u3_0_ok : treeOK (.c5, .c7, .c37)
    (rootNode (.c5, .c7, .c37)) u3_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u3_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u3_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u3_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u3_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u3_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u3_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u3_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u3_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u3_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u3_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u3_0_g2).1)
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u3_0_g2).2)))))))))))

private theorem u4_0_g0 :
    (leafOK (.c5, .c7, .c43) ⟨.pin 13, .pin 5, .pin 7, .pin 43⟩ ⟨(109, 393), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.pin 37, .pin 5, .pin 7, .pin 43⟩ ⟨(145, 882), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.pin 61, .pin 5, .pin 7, .pin 43⟩ ⟨(79, 617), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.pin 73, .pin 5, .pin 7, .pin 43⟩ ⟨(57, 487), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.pin 109, .pin 5, .pin 7, .pin 43⟩ ⟨(25, 261), (0, 1), (223, 590), (61, 400)⟩))))) = true := by
  decide +kernel

private theorem u4_0_g1 :
    (leafOK (.c5, .c7, .c43) ⟨.pin 409, .pin 5, .pin 7, .pin 43⟩ ⟨(9, 182), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.pin 709, .pin 5, .pin 7, .pin 43⟩ ⟨(8, 213), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.pin 3541, .pin 5, .pin 7, .pin 43⟩ ⟨(2, 119), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.pin 5113, .pin 5, .pin 7, .pin 43⟩ ⟨(2, 143), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.pin 7789, .pin 5, .pin 7, .pin 43⟩ ⟨(4, 353), (0, 1), (223, 590), (61, 400)⟩))))) = true := by
  decide +kernel

private theorem u4_0_g2 :
    (leafOK (.c5, .c7, .c43) ⟨.pin 17293, .pin 5, .pin 7, .pin 43⟩ ⟨(2, 263), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.pin 28057, .pin 5, .pin 7, .pin 43⟩ ⟨(2, 335), (0, 1), (223, 590), (61, 400)⟩ &&
    (leafOK (.c5, .c7, .c43) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 5, .pin 7, .pin 43⟩ ⟨(1, 5), (0, 1), (223, 590), (61, 400)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 7, 43)`, with 13 leaves. -/
def u4_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (0, 1), (223, 590), (61, 400)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (0, 1), (223, 590), (61, 400)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (0, 1), (223, 590), (61, 400)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (0, 1), (223, 590), (61, 400)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (0, 1), (223, 590), (61, 400)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (0, 1), (223, 590), (61, 400)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (0, 1), (223, 590), (61, 400)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (0, 1), (223, 590), (61, 400)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (0, 1), (223, 590), (61, 400)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (0, 1), (223, 590), (61, 400)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (0, 1), (223, 590), (61, 400)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (0, 1), (223, 590), (61, 400)⟩)
                          (.leaf ⟨(1, 5), (0, 1), (223, 590), (61, 400)⟩))))))))))))

/-- Subtree 0 of the class triple `(5, 7, 43)` passes the check. -/
theorem u4_0_ok : treeOK (.c5, .c7, .c43)
    (rootNode (.c5, .c7, .c43)) u4_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u4_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u4_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u4_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u4_0_g2).2).2))))))))))))

private theorem u5_0_g0 :
    (leafOK (.c5, .c7, .n2) ⟨.pin 13, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(109, 393), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.pin 37, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(145, 882), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.pin 61, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(79, 617), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.pin 73, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(57, 487), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.pin 109, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(25, 261), (0, 1), (223, 590), (0, 1)⟩))))) = true := by
  decide +kernel

private theorem u5_0_g1 :
    (leafOK (.c5, .c7, .n2) ⟨.pin 409, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(9, 182), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.pin 709, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(8, 213), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.pin 3541, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(2, 119), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.pin 5113, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(2, 143), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.pin 7789, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(4, 353), (0, 1), (223, 590), (0, 1)⟩))))) = true := by
  decide +kernel

private theorem u5_0_g2 :
    (leafOK (.c5, .c7, .n2) ⟨.pin 17293, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(2, 263), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.pin 28057, .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(2, 335), (0, 1), (223, 590), (0, 1)⟩ &&
    (leafOK (.c5, .c7, .n2) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 5, .pin 7, .free .n2 11 []⟩ ⟨(1, 5), (0, 1), (223, 590), (0, 1)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 7, n2)`, with 13 leaves. -/
def u5_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (0, 1), (223, 590), (0, 1)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (0, 1), (223, 590), (0, 1)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (0, 1), (223, 590), (0, 1)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (0, 1), (223, 590), (0, 1)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (0, 1), (223, 590), (0, 1)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (0, 1), (223, 590), (0, 1)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (0, 1), (223, 590), (0, 1)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (0, 1), (223, 590), (0, 1)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (0, 1), (223, 590), (0, 1)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (0, 1), (223, 590), (0, 1)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (0, 1), (223, 590), (0, 1)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (0, 1), (223, 590), (0, 1)⟩)
                          (.leaf ⟨(1, 5), (0, 1), (223, 590), (0, 1)⟩))))))))))))

/-- Subtree 0 of the class triple `(5, 7, n2)` passes the check. -/
theorem u5_0_ok : treeOK (.c5, .c7, .n2)
    (rootNode (.c5, .c7, .n2)) u5_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u5_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u5_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u5_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u5_0_g2).2).2))))))))))))

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u0_0_ok
#print axioms OddPerfect.ThreeFreeThree.u1_0_ok
#print axioms OddPerfect.ThreeFreeThree.u2_0_ok
#print axioms OddPerfect.ThreeFreeThree.u3_0_ok
#print axioms OddPerfect.ThreeFreeThree.u4_0_ok
#print axioms OddPerfect.ThreeFreeThree.u5_0_ok
