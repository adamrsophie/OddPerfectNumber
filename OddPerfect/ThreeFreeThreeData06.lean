import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 6

Subtrees of the case analysis certificate for the class triples `(7, 31, big)` (part),
with 101 leaves in all. Each public theorem states that a subtree passes `treeOK` from
explicit constraints. The data was found by a search outside Lean; everything in this
file is rechecked by the kernel through `decide +kernel` on the leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u44_8_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 307⟩ ⟨(109, 393), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 307⟩ ⟨(145, 882), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 307⟩ ⟨(79, 617), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 307⟩ ⟨(57, 487), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 307⟩ ⟨(25, 261), (223, 590), (155, 863), (48, 841)⟩))))) = true := by
  decide +kernel

private theorem u44_8_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 307⟩ ⟨(9, 182), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 307⟩ ⟨(8, 213), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 307⟩ ⟨(2, 119), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 307⟩ ⟨(2, 143), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 307⟩ ⟨(4, 353), (223, 590), (155, 863), (48, 841)⟩))))) = true := by
  decide +kernel

private theorem u44_8_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 307⟩ ⟨(2, 263), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 307⟩ ⟨(2, 335), (223, 590), (155, 863), (48, 841)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 307⟩ ⟨(1, 5), (223, 590), (155, 863), (48, 841)⟩))) = true := by
  decide +kernel

/-- Subtree 8 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_8 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (48, 841)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (48, 841)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (48, 841)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (48, 841)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (48, 841)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (48, 841)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (48, 841)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (48, 841)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (48, 841)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (48, 841)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (48, 841)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (48, 841)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (48, 841)⟩))))))))))))

/-- Subtree 8 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_8_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 307⟩ u44_8 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_8_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_8_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_8_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_8_g2).2).2))))))))))))

private theorem u44_9_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 409⟩ ⟨(109, 393), (223, 590), (155, 863), (9, 182)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 409⟩ ⟨(145, 882), (223, 590), (155, 863), (9, 182)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 409⟩ ⟨(79, 617), (223, 590), (155, 863), (9, 182)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 409⟩ ⟨(57, 487), (223, 590), (155, 863), (9, 182)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 409⟩ ⟨(25, 261), (223, 590), (155, 863), (9, 182)⟩))))) = true := by
  decide +kernel

private theorem u44_9_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 409⟩ ⟨(8, 213), (223, 590), (155, 863), (9, 182)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 409⟩ ⟨(2, 119), (223, 590), (155, 863), (9, 182)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 409⟩ ⟨(2, 143), (223, 590), (155, 863), (9, 182)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 409⟩ ⟨(4, 353), (223, 590), (155, 863), (9, 182)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 409⟩ ⟨(2, 263), (223, 590), (155, 863), (9, 182)⟩))))) = true := by
  decide +kernel

private theorem u44_9_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 409⟩ ⟨(2, 335), (223, 590), (155, 863), (9, 182)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 409⟩ ⟨(1, 5), (223, 590), (155, 863), (9, 182)⟩)) = true := by
  decide +kernel

/-- Subtree 9 of the class triple `(7, 31, big)`, with 12 leaves. -/
def u44_9 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (9, 182)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (9, 182)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (9, 182)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (9, 182)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (9, 182)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (223, 590), (155, 863), (9, 182)⟩)
              (.split 0 3541
                (.leaf ⟨(2, 119), (223, 590), (155, 863), (9, 182)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (223, 590), (155, 863), (9, 182)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (223, 590), (155, 863), (9, 182)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (223, 590), (155, 863), (9, 182)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (223, 590), (155, 863), (9, 182)⟩)
                        (.leaf ⟨(1, 5), (223, 590), (155, 863), (9, 182)⟩)))))))))))

/-- Subtree 9 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_9_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 409⟩ u44_9 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_9_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_9_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_9_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_9_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_9_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_9_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_9_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_9_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_9_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_9_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_9_g2).1)
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_9_g2).2)))))))))))

private theorem u44_10_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 709⟩ ⟨(109, 393), (223, 590), (155, 863), (8, 213)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 709⟩ ⟨(145, 882), (223, 590), (155, 863), (8, 213)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 709⟩ ⟨(79, 617), (223, 590), (155, 863), (8, 213)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 709⟩ ⟨(57, 487), (223, 590), (155, 863), (8, 213)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 709⟩ ⟨(25, 261), (223, 590), (155, 863), (8, 213)⟩))))) = true := by
  decide +kernel

private theorem u44_10_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 709⟩ ⟨(9, 182), (223, 590), (155, 863), (8, 213)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 709⟩ ⟨(2, 119), (223, 590), (155, 863), (8, 213)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 709⟩ ⟨(2, 143), (223, 590), (155, 863), (8, 213)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 709⟩ ⟨(4, 353), (223, 590), (155, 863), (8, 213)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 709⟩ ⟨(2, 263), (223, 590), (155, 863), (8, 213)⟩))))) = true := by
  decide +kernel

private theorem u44_10_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 709⟩ ⟨(2, 335), (223, 590), (155, 863), (8, 213)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 709⟩ ⟨(1, 5), (223, 590), (155, 863), (8, 213)⟩)) = true := by
  decide +kernel

/-- Subtree 10 of the class triple `(7, 31, big)`, with 12 leaves. -/
def u44_10 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (8, 213)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (8, 213)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (8, 213)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (8, 213)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (8, 213)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (8, 213)⟩)
              (.split 0 3541
                (.leaf ⟨(2, 119), (223, 590), (155, 863), (8, 213)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (223, 590), (155, 863), (8, 213)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (223, 590), (155, 863), (8, 213)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (223, 590), (155, 863), (8, 213)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (223, 590), (155, 863), (8, 213)⟩)
                        (.leaf ⟨(1, 5), (223, 590), (155, 863), (8, 213)⟩)))))))))))

/-- Subtree 10 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_10_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 709⟩ u44_10 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_10_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_10_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_10_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_10_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_10_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_10_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_10_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_10_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_10_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_10_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_10_g2).1)
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_10_g2).2)))))))))))

private theorem u44_11_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 727⟩ ⟨(109, 393), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 727⟩ ⟨(145, 882), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 727⟩ ⟨(79, 617), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 727⟩ ⟨(57, 487), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 727⟩ ⟨(25, 261), (223, 590), (155, 863), (26, 701)⟩))))) = true := by
  decide +kernel

private theorem u44_11_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 727⟩ ⟨(9, 182), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 727⟩ ⟨(8, 213), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 727⟩ ⟨(2, 119), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 727⟩ ⟨(2, 143), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 727⟩ ⟨(4, 353), (223, 590), (155, 863), (26, 701)⟩))))) = true := by
  decide +kernel

private theorem u44_11_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 727⟩ ⟨(2, 263), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 727⟩ ⟨(2, 335), (223, 590), (155, 863), (26, 701)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 727⟩ ⟨(1, 5), (223, 590), (155, 863), (26, 701)⟩))) = true := by
  decide +kernel

/-- Subtree 11 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_11 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (26, 701)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (26, 701)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (26, 701)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (26, 701)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (26, 701)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (26, 701)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (26, 701)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (26, 701)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (26, 701)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (26, 701)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (26, 701)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (26, 701)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (26, 701)⟩))))))))))))

/-- Subtree 11 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_11_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 727⟩ u44_11 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_11_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_11_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_11_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_11_g2).2).2))))))))))))

private theorem u44_12_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 991⟩ ⟨(109, 393), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 991⟩ ⟨(145, 882), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 991⟩ ⟨(79, 617), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 991⟩ ⟨(57, 487), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 991⟩ ⟨(25, 261), (223, 590), (155, 863), (25, 787)⟩))))) = true := by
  decide +kernel

private theorem u44_12_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 991⟩ ⟨(9, 182), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 991⟩ ⟨(8, 213), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 991⟩ ⟨(2, 119), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 991⟩ ⟨(2, 143), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 991⟩ ⟨(4, 353), (223, 590), (155, 863), (25, 787)⟩))))) = true := by
  decide +kernel

private theorem u44_12_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 991⟩ ⟨(2, 263), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 991⟩ ⟨(2, 335), (223, 590), (155, 863), (25, 787)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 991⟩ ⟨(1, 5), (223, 590), (155, 863), (25, 787)⟩))) = true := by
  decide +kernel

/-- Subtree 12 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_12 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (25, 787)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (25, 787)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (25, 787)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (25, 787)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (25, 787)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (25, 787)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (25, 787)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (25, 787)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (25, 787)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (25, 787)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (25, 787)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (25, 787)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (25, 787)⟩))))))))))))

/-- Subtree 12 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_12_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 991⟩ u44_12 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_12_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_12_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_12_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_12_g2).2).2))))))))))))

private theorem u44_13_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 1087⟩ ⟨(109, 393), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 1087⟩ ⟨(145, 882), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 1087⟩ ⟨(79, 617), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 1087⟩ ⟨(57, 487), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 1087⟩ ⟨(25, 261), (223, 590), (155, 863), (30, 989)⟩))))) = true := by
  decide +kernel

private theorem u44_13_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 1087⟩ ⟨(9, 182), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 1087⟩ ⟨(8, 213), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 1087⟩ ⟨(2, 119), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 1087⟩ ⟨(2, 143), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 1087⟩ ⟨(4, 353), (223, 590), (155, 863), (30, 989)⟩))))) = true := by
  decide +kernel

private theorem u44_13_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 1087⟩ ⟨(2, 263), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 1087⟩ ⟨(2, 335), (223, 590), (155, 863), (30, 989)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 1087⟩ ⟨(1, 5), (223, 590), (155, 863), (30, 989)⟩))) = true := by
  decide +kernel

/-- Subtree 13 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_13 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (30, 989)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (30, 989)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (30, 989)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (30, 989)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (30, 989)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (30, 989)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (30, 989)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (30, 989)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (30, 989)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (30, 989)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (30, 989)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (30, 989)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (30, 989)⟩))))))))))))

/-- Subtree 13 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_13_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 1087⟩ u44_13 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_13_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_13_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_13_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_13_g2).2).2))))))))))))

private theorem u44_14_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 1723⟩ ⟨(109, 393), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 1723⟩ ⟨(145, 882), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 1723⟩ ⟨(79, 617), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 1723⟩ ⟨(57, 487), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 1723⟩ ⟨(25, 261), (223, 590), (155, 863), (2, 83)⟩))))) = true := by
  decide +kernel

private theorem u44_14_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 1723⟩ ⟨(9, 182), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 1723⟩ ⟨(8, 213), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 1723⟩ ⟨(2, 119), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 1723⟩ ⟨(2, 143), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 1723⟩ ⟨(4, 353), (223, 590), (155, 863), (2, 83)⟩))))) = true := by
  decide +kernel

private theorem u44_14_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 1723⟩ ⟨(2, 263), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 1723⟩ ⟨(2, 335), (223, 590), (155, 863), (2, 83)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 1723⟩ ⟨(1, 5), (223, 590), (155, 863), (2, 83)⟩))) = true := by
  decide +kernel

/-- Subtree 14 of the class triple `(7, 31, big)`, with 13 leaves. -/
def u44_14 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (2, 83)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (2, 83)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (2, 83)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (2, 83)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (2, 83)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (2, 83)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (2, 83)⟩)
                (.split 0 3541
                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (2, 83)⟩)
                  (.split 0 5113
                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (2, 83)⟩)
                    (.split 0 7789
                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (2, 83)⟩)
                      (.split 0 17293
                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (2, 83)⟩)
                        (.split 0 28057
                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (2, 83)⟩)
                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (2, 83)⟩))))))))))))

/-- Subtree 14 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_14_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 1723⟩ u44_14 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_14_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_14_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_14_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g2).2).1)
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_14_g2).2).2))))))))))))

private theorem u44_15_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 3541⟩ ⟨(109, 393), (223, 590), (155, 863), (2, 119)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 3541⟩ ⟨(145, 882), (223, 590), (155, 863), (2, 119)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 3541⟩ ⟨(79, 617), (223, 590), (155, 863), (2, 119)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 3541⟩ ⟨(57, 487), (223, 590), (155, 863), (2, 119)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 3541⟩ ⟨(25, 261), (223, 590), (155, 863), (2, 119)⟩))))) = true := by
  decide +kernel

private theorem u44_15_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 3541⟩ ⟨(9, 182), (223, 590), (155, 863), (2, 119)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 3541⟩ ⟨(8, 213), (223, 590), (155, 863), (2, 119)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 3541⟩ ⟨(2, 143), (223, 590), (155, 863), (2, 119)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 3541⟩ ⟨(4, 353), (223, 590), (155, 863), (2, 119)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 3541⟩ ⟨(2, 263), (223, 590), (155, 863), (2, 119)⟩))))) = true := by
  decide +kernel

private theorem u44_15_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 3541⟩ ⟨(2, 335), (223, 590), (155, 863), (2, 119)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 3541⟩ ⟨(1, 5), (223, 590), (155, 863), (2, 119)⟩)) = true := by
  decide +kernel

/-- Subtree 15 of the class triple `(7, 31, big)`, with 12 leaves. -/
def u44_15 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (2, 119)⟩)
    (.split 0 37
      (.leaf ⟨(145, 882), (223, 590), (155, 863), (2, 119)⟩)
      (.split 0 61
        (.leaf ⟨(79, 617), (223, 590), (155, 863), (2, 119)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (155, 863), (2, 119)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (155, 863), (2, 119)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (155, 863), (2, 119)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (155, 863), (2, 119)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (223, 590), (155, 863), (2, 119)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (223, 590), (155, 863), (2, 119)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (223, 590), (155, 863), (2, 119)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (223, 590), (155, 863), (2, 119)⟩)
                        (.leaf ⟨(1, 5), (223, 590), (155, 863), (2, 119)⟩)))))))))))

/-- Subtree 15 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_15_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .pin 3541⟩ u44_15 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_15_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_15_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_15_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_15_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_15_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_15_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_15_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_15_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_15_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_15_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_15_g2).1)
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_15_g2).2)))))))))))

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u44_8_ok
#print axioms OddPerfect.ThreeFreeThree.u44_9_ok
#print axioms OddPerfect.ThreeFreeThree.u44_10_ok
#print axioms OddPerfect.ThreeFreeThree.u44_11_ok
#print axioms OddPerfect.ThreeFreeThree.u44_12_ok
#print axioms OddPerfect.ThreeFreeThree.u44_13_ok
#print axioms OddPerfect.ThreeFreeThree.u44_14_ok
#print axioms OddPerfect.ThreeFreeThree.u44_15_ok
