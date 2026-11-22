import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 2

Subtrees of the case analysis certificate for the class triples `(5, 7, big)`,
`(5, 13, 19)`, `(5, 13, 31)`, `(5, 13, 37)`, `(5, 13, 43)`, `(5, 13, n2)`, `(5, 13, big)`,
`(5, 19, 31)`, `(5, 19, 37)`, `(5, 19, 43)`, `(5, 19, n2)`, `(5, 19, big)`, `(5, 31, 37)`,
`(5, 31, 43)`, `(5, 31, n2)`, `(5, 31, big)`, `(5, 37, 43)`, `(5, 37, n2)`, `(5, 37, big)`,
`(5, 43, n2)`, `(5, 43, big)`, `(5, n2, n2)`, `(5, n2, big)`, `(5, big, big)`, with 118 leaves
in all. Each public theorem states that a subtree passes `treeOK` from explicit
constraints. The data was found by a search outside Lean; everything in this file is
rechecked by the kernel through `decide +kernel` on the leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u6_0_g0 :
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 61⟩ ⟨(109, 393), (0, 1), (223, 590), (79, 617)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 13, .pin 5, .pin 7, .pin 67⟩ ⟨(109, 393), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 37, .pin 5, .pin 7, .pin 67⟩ ⟨(145, 882), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 61, .pin 5, .pin 7, .pin 67⟩ ⟨(79, 617), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 73, .pin 5, .pin 7, .pin 67⟩ ⟨(57, 487), (0, 1), (223, 590), (27, 221)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g1 :
    (leafOK (.c5, .c7, .big) ⟨.pin 109, .pin 5, .pin 7, .pin 67⟩ ⟨(25, 261), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 409, .pin 5, .pin 7, .pin 67⟩ ⟨(9, 182), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 709, .pin 5, .pin 7, .pin 67⟩ ⟨(8, 213), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 3541, .pin 5, .pin 7, .pin 67⟩ ⟨(2, 119), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 5113, .pin 5, .pin 7, .pin 67⟩ ⟨(2, 143), (0, 1), (223, 590), (27, 221)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g2 :
    (leafOK (.c5, .c7, .big) ⟨.pin 7789, .pin 5, .pin 7, .pin 67⟩ ⟨(4, 353), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 17293, .pin 5, .pin 7, .pin 67⟩ ⟨(2, 263), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 28057, .pin 5, .pin 7, .pin 67⟩ ⟨(2, 335), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 5, .pin 7, .pin 67⟩ ⟨(1, 5), (0, 1), (223, 590), (27, 221)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 73⟩ ⟨(109, 393), (0, 1), (223, 590), (57, 487)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g3 :
    (leafOK (.c5, .c7, .big) ⟨.pin 13, .pin 5, .pin 7, .pin 79⟩ ⟨(109, 393), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 37, .pin 5, .pin 7, .pin 79⟩ ⟨(145, 882), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 61, .pin 5, .pin 7, .pin 79⟩ ⟨(79, 617), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 73, .pin 5, .pin 7, .pin 79⟩ ⟨(57, 487), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 109, .pin 5, .pin 7, .pin 79⟩ ⟨(25, 261), (0, 1), (223, 590), (107, 951)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g4 :
    (leafOK (.c5, .c7, .big) ⟨.pin 409, .pin 5, .pin 7, .pin 79⟩ ⟨(9, 182), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 709, .pin 5, .pin 7, .pin 79⟩ ⟨(8, 213), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 3541, .pin 5, .pin 7, .pin 79⟩ ⟨(2, 119), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 5113, .pin 5, .pin 7, .pin 79⟩ ⟨(2, 143), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 7789, .pin 5, .pin 7, .pin 79⟩ ⟨(4, 353), (0, 1), (223, 590), (107, 951)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g5 :
    (leafOK (.c5, .c7, .big) ⟨.pin 17293, .pin 5, .pin 7, .pin 79⟩ ⟨(2, 263), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 28057, .pin 5, .pin 7, .pin 79⟩ ⟨(2, 335), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 5, .pin 7, .pin 79⟩ ⟨(1, 5), (0, 1), (223, 590), (107, 951)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 109⟩ ⟨(109, 393), (0, 1), (223, 590), (25, 261)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 127⟩ ⟨(109, 393), (0, 1), (223, 590), (26, 293)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g6 :
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 151⟩ ⟨(109, 393), (0, 1), (223, 590), (59, 725)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 13, .pin 5, .pin 7, .pin 307⟩ ⟨(109, 393), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 37, .pin 5, .pin 7, .pin 307⟩ ⟨(145, 882), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 61, .pin 5, .pin 7, .pin 307⟩ ⟨(79, 617), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 73, .pin 5, .pin 7, .pin 307⟩ ⟨(57, 487), (0, 1), (223, 590), (48, 841)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g7 :
    (leafOK (.c5, .c7, .big) ⟨.pin 109, .pin 5, .pin 7, .pin 307⟩ ⟨(25, 261), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 409, .pin 5, .pin 7, .pin 307⟩ ⟨(9, 182), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 709, .pin 5, .pin 7, .pin 307⟩ ⟨(8, 213), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 3541, .pin 5, .pin 7, .pin 307⟩ ⟨(2, 119), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 5113, .pin 5, .pin 7, .pin 307⟩ ⟨(2, 143), (0, 1), (223, 590), (48, 841)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g8 :
    (leafOK (.c5, .c7, .big) ⟨.pin 7789, .pin 5, .pin 7, .pin 307⟩ ⟨(4, 353), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 17293, .pin 5, .pin 7, .pin 307⟩ ⟨(2, 263), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 28057, .pin 5, .pin 7, .pin 307⟩ ⟨(2, 335), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 5, .pin 7, .pin 307⟩ ⟨(1, 5), (0, 1), (223, 590), (48, 841)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 409⟩ ⟨(109, 393), (0, 1), (223, 590), (9, 182)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g9 :
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 709⟩ ⟨(109, 393), (0, 1), (223, 590), (8, 213)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 727⟩ ⟨(109, 393), (0, 1), (223, 590), (26, 701)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 991⟩ ⟨(109, 393), (0, 1), (223, 590), (25, 787)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 1087⟩ ⟨(109, 393), (0, 1), (223, 590), (30, 989)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 1723⟩ ⟨(109, 393), (0, 1), (223, 590), (2, 83)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g10 :
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 3541⟩ ⟨(109, 393), (0, 1), (223, 590), (2, 119)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 4603⟩ ⟨(109, 393), (0, 1), (223, 590), (6, 407)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 5113⟩ ⟨(109, 393), (0, 1), (223, 590), (2, 143)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 7789⟩ ⟨(109, 393), (0, 1), (223, 590), (4, 353)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 8011⟩ ⟨(109, 393), (0, 1), (223, 590), (2, 179)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g11 :
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 10303⟩ ⟨(109, 393), (0, 1), (223, 590), (2, 203)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 17293⟩ ⟨(109, 393), (0, 1), (223, 590), (2, 263)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 28057⟩ ⟨(109, 393), (0, 1), (223, 590), (2, 335)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 30103⟩ ⟨(109, 393), (0, 1), (223, 590), (2, 347)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [], .pin 5, .pin 7, .pin 86143⟩ ⟨(109, 393), (0, 1), (223, 590), (2, 587)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g12 :
    (leafOK (.c5, .c7, .big) ⟨.pin 13, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(109, 393), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 37, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(145, 882), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 61, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(79, 617), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 73, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(57, 487), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 109, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(25, 261), (0, 1), (223, 590), (1, 8)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g13 :
    (leafOK (.c5, .c7, .big) ⟨.pin 409, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(9, 182), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 709, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(8, 213), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 3541, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(2, 119), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 5113, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(2, 143), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 7789, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(4, 353), (0, 1), (223, 590), (1, 8)⟩))))) = true := by
  decide +kernel

private theorem u6_0_g14 :
    (leafOK (.c5, .c7, .big) ⟨.pin 17293, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(2, 263), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.pin 28057, .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(2, 335), (0, 1), (223, 590), (1, 8)⟩ &&
    (leafOK (.c5, .c7, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 5, .pin 7, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(1, 5), (0, 1), (223, 590), (1, 8)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 7, big)`, with 73 leaves. -/
def u6_0 : Tree :=
  .split 3 61
    (.leaf ⟨(109, 393), (0, 1), (223, 590), (79, 617)⟩)
    (.split 3 67
      (.split 0 13
        (.leaf ⟨(109, 393), (0, 1), (223, 590), (27, 221)⟩)
        (.split 0 37
          (.leaf ⟨(145, 882), (0, 1), (223, 590), (27, 221)⟩)
          (.split 0 61
            (.leaf ⟨(79, 617), (0, 1), (223, 590), (27, 221)⟩)
            (.split 0 73
              (.leaf ⟨(57, 487), (0, 1), (223, 590), (27, 221)⟩)
              (.split 0 109
                (.leaf ⟨(25, 261), (0, 1), (223, 590), (27, 221)⟩)
                (.split 0 409
                  (.leaf ⟨(9, 182), (0, 1), (223, 590), (27, 221)⟩)
                  (.split 0 709
                    (.leaf ⟨(8, 213), (0, 1), (223, 590), (27, 221)⟩)
                    (.split 0 3541
                      (.leaf ⟨(2, 119), (0, 1), (223, 590), (27, 221)⟩)
                      (.split 0 5113
                        (.leaf ⟨(2, 143), (0, 1), (223, 590), (27, 221)⟩)
                        (.split 0 7789
                          (.leaf ⟨(4, 353), (0, 1), (223, 590), (27, 221)⟩)
                          (.split 0 17293
                            (.leaf ⟨(2, 263), (0, 1), (223, 590), (27, 221)⟩)
                            (.split 0 28057
                              (.leaf ⟨(2, 335), (0, 1), (223, 590), (27, 221)⟩)
                              (.leaf ⟨(1, 5), (0, 1), (223, 590), (27, 221)⟩)))))))))))))
      (.split 3 73
        (.leaf ⟨(109, 393), (0, 1), (223, 590), (57, 487)⟩)
        (.split 3 79
          (.split 0 13
            (.leaf ⟨(109, 393), (0, 1), (223, 590), (107, 951)⟩)
            (.split 0 37
              (.leaf ⟨(145, 882), (0, 1), (223, 590), (107, 951)⟩)
              (.split 0 61
                (.leaf ⟨(79, 617), (0, 1), (223, 590), (107, 951)⟩)
                (.split 0 73
                  (.leaf ⟨(57, 487), (0, 1), (223, 590), (107, 951)⟩)
                  (.split 0 109
                    (.leaf ⟨(25, 261), (0, 1), (223, 590), (107, 951)⟩)
                    (.split 0 409
                      (.leaf ⟨(9, 182), (0, 1), (223, 590), (107, 951)⟩)
                      (.split 0 709
                        (.leaf ⟨(8, 213), (0, 1), (223, 590), (107, 951)⟩)
                        (.split 0 3541
                          (.leaf ⟨(2, 119), (0, 1), (223, 590), (107, 951)⟩)
                          (.split 0 5113
                            (.leaf ⟨(2, 143), (0, 1), (223, 590), (107, 951)⟩)
                            (.split 0 7789
                              (.leaf ⟨(4, 353), (0, 1), (223, 590), (107, 951)⟩)
                              (.split 0 17293
                                (.leaf ⟨(2, 263), (0, 1), (223, 590), (107, 951)⟩)
                                (.split 0 28057
                                  (.leaf ⟨(2, 335), (0, 1), (223, 590), (107, 951)⟩)
                                  (.leaf ⟨(1, 5), (0, 1), (223, 590), (107, 951)⟩)))))))))))))
          (.split 3 109
            (.leaf ⟨(109, 393), (0, 1), (223, 590), (25, 261)⟩)
            (.split 3 127
              (.leaf ⟨(109, 393), (0, 1), (223, 590), (26, 293)⟩)
              (.split 3 151
                (.leaf ⟨(109, 393), (0, 1), (223, 590), (59, 725)⟩)
                (.split 3 307
                  (.split 0 13
                    (.leaf ⟨(109, 393), (0, 1), (223, 590), (48, 841)⟩)
                    (.split 0 37
                      (.leaf ⟨(145, 882), (0, 1), (223, 590), (48, 841)⟩)
                      (.split 0 61
                        (.leaf ⟨(79, 617), (0, 1), (223, 590), (48, 841)⟩)
                        (.split 0 73
                          (.leaf ⟨(57, 487), (0, 1), (223, 590), (48, 841)⟩)
                          (.split 0 109
                            (.leaf ⟨(25, 261), (0, 1), (223, 590), (48, 841)⟩)
                            (.split 0 409
                              (.leaf ⟨(9, 182), (0, 1), (223, 590), (48, 841)⟩)
                              (.split 0 709
                                (.leaf ⟨(8, 213), (0, 1), (223, 590), (48, 841)⟩)
                                (.split 0 3541
                                  (.leaf ⟨(2, 119), (0, 1), (223, 590), (48, 841)⟩)
                                  (.split 0 5113
                                    (.leaf ⟨(2, 143), (0, 1), (223, 590), (48, 841)⟩)
                                    (.split 0 7789
                                      (.leaf ⟨(4, 353), (0, 1), (223, 590), (48, 841)⟩)
                                      (.split 0 17293
                                        (.leaf ⟨(2, 263), (0, 1), (223, 590), (48, 841)⟩)
                                        (.split 0 28057
                                          (.leaf ⟨(2, 335), (0, 1), (223, 590), (48, 841)⟩)
                                          (.leaf ⟨(1, 5), (0, 1), (223, 590), (48, 841)⟩)))))))))))))
                  (.split 3 409
                    (.leaf ⟨(109, 393), (0, 1), (223, 590), (9, 182)⟩)
                    (.split 3 709
                      (.leaf ⟨(109, 393), (0, 1), (223, 590), (8, 213)⟩)
                      (.split 3 727
                        (.leaf ⟨(109, 393), (0, 1), (223, 590), (26, 701)⟩)
                        (.split 3 991
                          (.leaf ⟨(109, 393), (0, 1), (223, 590), (25, 787)⟩)
                          (.split 3 1087
                            (.leaf ⟨(109, 393), (0, 1), (223, 590), (30, 989)⟩)
                            (.split 3 1723
                              (.leaf ⟨(109, 393), (0, 1), (223, 590), (2, 83)⟩)
                              (.split 3 3541
                                (.leaf ⟨(109, 393), (0, 1), (223, 590), (2, 119)⟩)
                                (.split 3 4603
                                  (.leaf ⟨(109, 393), (0, 1), (223, 590), (6, 407)⟩)
                                  (.split 3 5113
                                    (.leaf ⟨(109, 393), (0, 1), (223, 590), (2, 143)⟩)
                                    (.split 3 7789
                                      (.leaf ⟨(109, 393), (0, 1), (223, 590), (4, 353)⟩)
                                      (.split 3 8011
                                        (.leaf ⟨(109, 393), (0, 1), (223, 590), (2, 179)⟩)
                                        (.split 3 10303
                                          (.leaf ⟨(109, 393), (0, 1), (223, 590), (2, 203)⟩)
                                          (.split 3 17293
                                            (.leaf ⟨(109, 393), (0, 1), (223, 590), (2, 263)⟩)
                                            (.split 3 28057
                                              (.leaf ⟨(109, 393), (0, 1), (223, 590), (2, 335)⟩)
                                              (.split 3 30103
                                                (.leaf ⟨(109, 393), (0, 1), (223, 590), (2, 347)⟩)
                                                (.split 3 86143
                                                  (.leaf ⟨(109, 393), (0, 1), (223, 590), (2, 587)⟩)
                                                  (.split 0 13
                                                    (.leaf ⟨(109, 393), (0, 1), (223, 590), (1, 8)⟩)
                                                    (.split 0 37
                                                      (.leaf ⟨(145, 882), (0, 1), (223, 590), (1, 8)⟩)
                                                      (.split 0 61
                                                        (.leaf ⟨(79, 617), (0, 1), (223, 590), (1, 8)⟩)
                                                        (.split 0 73
                                                          (.leaf ⟨(57, 487), (0, 1), (223, 590), (1, 8)⟩)
                                                          (.split 0 109
                                                            (.leaf ⟨(25, 261), (0, 1), (223, 590), (1, 8)⟩)
                                                            (.split 0 409
                                                              (.leaf ⟨(9, 182), (0, 1), (223, 590), (1, 8)⟩)
                                                              (.split 0 709
                                                                (.leaf ⟨(8, 213), (0, 1), (223, 590), (1, 8)⟩)
                                                                (.split 0 3541
                                                                  (.leaf ⟨(2, 119), (0, 1), (223, 590), (1, 8)⟩)
                                                                  (.split 0 5113
                                                                    (.leaf ⟨(2, 143), (0, 1), (223, 590), (1, 8)⟩)
                                                                    (.split 0 7789
                                                                      (.leaf ⟨(4, 353), (0, 1), (223, 590), (1, 8)⟩)
                                                                      (.split 0 17293
                                                                        (.leaf ⟨(2, 263), (0, 1), (223, 590), (1, 8)⟩)
                                                                        (.split 0 28057
                                                                          (.leaf ⟨(2, 335), (0, 1), (223, 590), (1, 8)⟩)
                                                                          (.leaf ⟨(1, 5), (0, 1), (223, 590), (1, 8)⟩))))))))))))))))))))))))))))))))))))

/-- Subtree 0 of the class triple `(5, 7, big)` passes the check. -/
theorem u6_0_ok : treeOK (.c5, .c7, .big)
    (rootNode (.c5, .c7, .big)) u6_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g0).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g0).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g0).2).2).2).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g0).2).2).2).2)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g1).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g1).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g1).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g1).2).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g1).2).2).2).2)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g2).2).2).1)
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g2).2).2).2).1)))))))))))))
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g2).2).2).2).2)
        (treeOK_split (by decide) rfl
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g3).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g3).2).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g3).2).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g3).2).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g3).2).2).2).2)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g4).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g4).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g4).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g4).2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g4).2).2).2).2)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g5).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g5).2).1)
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g5).2).2).1)))))))))))))
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g5).2).2).2).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g5).2).2).2).2)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g6).1)
                (treeOK_split (by decide) rfl
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g6).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g6).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g6).2).2).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g6).2).2).2).2)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g7).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g7).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g7).2).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g7).2).2).2).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g7).2).2).2).2)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g8).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g8).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g8).2).2).1)
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g8).2).2).2).1)))))))))))))
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g8).2).2).2).2)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g9).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g9).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g9).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g9).2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g9).2).2).2).2)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g10).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g10).2).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g10).2).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g10).2).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g10).2).2).2).2)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g11).1)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g11).2).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g11).2).2).1)
                                              (treeOK_split (by decide) rfl
                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g11).2).2).2).1)
                                                (treeOK_split (by decide) rfl
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g11).2).2).2).2)
                                                  (treeOK_split (by decide) rfl
                                                    (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g12).1)
                                                    (treeOK_split (by decide) rfl
                                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g12).2).1)
                                                      (treeOK_split (by decide) rfl
                                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g12).2).2).1)
                                                        (treeOK_split (by decide) rfl
                                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g12).2).2).2).1)
                                                          (treeOK_split (by decide) rfl
                                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g12).2).2).2).2)
                                                            (treeOK_split (by decide) rfl
                                                              (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g13).1)
                                                              (treeOK_split (by decide) rfl
                                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g13).2).1)
                                                                (treeOK_split (by decide) rfl
                                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g13).2).2).1)
                                                                  (treeOK_split (by decide) rfl
                                                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g13).2).2).2).1)
                                                                    (treeOK_split (by decide) rfl
                                                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g13).2).2).2).2)
                                                                      (treeOK_split (by decide) rfl
                                                                        (treeOK_leaf (Bool.and_eq_true_iff.mp u6_0_g14).1)
                                                                        (treeOK_split (by decide) rfl
                                                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g14).2).1)
                                                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u6_0_g14).2).2))))))))))))))))))))))))))))))))))))

private theorem u7_0_g0 :
    leafOK (.c5, .c13, .c19) ⟨.free .q 13 [], .pin 5, .pin 13, .pin 19⟩ ⟨(1, 5), (0, 1), (109, 393), (209, 911)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 13, 19)`, with 1 leaves. -/
def u7_0 : Tree :=
  .leaf ⟨(1, 5), (0, 1), (109, 393), (209, 911)⟩

/-- Subtree 0 of the class triple `(5, 13, 19)` passes the check. -/
theorem u7_0_ok : treeOK (.c5, .c13, .c19)
    (rootNode (.c5, .c13, .c19)) u7_0 = true :=
  treeOK_leaf u7_0_g0

private theorem u8_0_g0 :
    leafOK (.c5, .c13, .c31) ⟨.free .q 13 [], .pin 5, .pin 13, .pin 31⟩ ⟨(1, 5), (0, 1), (109, 393), (155, 863)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 13, 31)`, with 1 leaves. -/
def u8_0 : Tree :=
  .leaf ⟨(1, 5), (0, 1), (109, 393), (155, 863)⟩

/-- Subtree 0 of the class triple `(5, 13, 31)` passes the check. -/
theorem u8_0_ok : treeOK (.c5, .c13, .c31)
    (rootNode (.c5, .c13, .c31)) u8_0 = true :=
  treeOK_leaf u8_0_g0

private theorem u9_0_g0 :
    leafOK (.c5, .c13, .c37) ⟨.free .q 13 [], .pin 5, .pin 13, .pin 37⟩ ⟨(1, 5), (0, 1), (109, 393), (145, 882)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 13, 37)`, with 1 leaves. -/
def u9_0 : Tree :=
  .leaf ⟨(1, 5), (0, 1), (109, 393), (145, 882)⟩

/-- Subtree 0 of the class triple `(5, 13, 37)` passes the check. -/
theorem u9_0_ok : treeOK (.c5, .c13, .c37)
    (rootNode (.c5, .c13, .c37)) u9_0 = true :=
  treeOK_leaf u9_0_g0

private theorem u10_0_g0 :
    leafOK (.c5, .c13, .c43) ⟨.free .q 13 [], .pin 5, .pin 13, .pin 43⟩ ⟨(1, 5), (0, 1), (109, 393), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 13, 43)`, with 1 leaves. -/
def u10_0 : Tree :=
  .leaf ⟨(1, 5), (0, 1), (109, 393), (61, 400)⟩

/-- Subtree 0 of the class triple `(5, 13, 43)` passes the check. -/
theorem u10_0_ok : treeOK (.c5, .c13, .c43)
    (rootNode (.c5, .c13, .c43)) u10_0 = true :=
  treeOK_leaf u10_0_g0

private theorem u11_0_g0 :
    leafOK (.c5, .c13, .n2) ⟨.free .q 13 [], .pin 5, .pin 13, .free .n2 11 []⟩ ⟨(1, 5), (0, 1), (109, 393), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 13, n2)`, with 1 leaves. -/
def u11_0 : Tree :=
  .leaf ⟨(1, 5), (0, 1), (109, 393), (0, 1)⟩

/-- Subtree 0 of the class triple `(5, 13, n2)` passes the check. -/
theorem u11_0_ok : treeOK (.c5, .c13, .n2)
    (rootNode (.c5, .c13, .n2)) u11_0 = true :=
  treeOK_leaf u11_0_g0

private theorem u12_0_g0 :
    leafOK (.c5, .c13, .big) ⟨.free .q 13 [], .pin 5, .pin 13, .free .big 61 []⟩ ⟨(1, 5), (0, 1), (109, 393), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 13, big)`, with 1 leaves. -/
def u12_0 : Tree :=
  .leaf ⟨(1, 5), (0, 1), (109, 393), (79, 617)⟩

/-- Subtree 0 of the class triple `(5, 13, big)` passes the check. -/
theorem u12_0_ok : treeOK (.c5, .c13, .big)
    (rootNode (.c5, .c13, .big)) u12_0 = true :=
  treeOK_leaf u12_0_g0

private theorem u13_0_g0 :
    leafOK (.c5, .c19, .c31) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 31⟩ ⟨(109, 393), (0, 1), (209, 911), (155, 863)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 19, 31)`, with 1 leaves. -/
def u13_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (209, 911), (155, 863)⟩

/-- Subtree 0 of the class triple `(5, 19, 31)` passes the check. -/
theorem u13_0_ok : treeOK (.c5, .c19, .c31)
    (rootNode (.c5, .c19, .c31)) u13_0 = true :=
  treeOK_leaf u13_0_g0

private theorem u14_0_g0 :
    leafOK (.c5, .c19, .c37) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 37⟩ ⟨(109, 393), (0, 1), (209, 911), (145, 882)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 19, 37)`, with 1 leaves. -/
def u14_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (209, 911), (145, 882)⟩

/-- Subtree 0 of the class triple `(5, 19, 37)` passes the check. -/
theorem u14_0_ok : treeOK (.c5, .c19, .c37)
    (rootNode (.c5, .c19, .c37)) u14_0 = true :=
  treeOK_leaf u14_0_g0

private theorem u15_0_g0 :
    leafOK (.c5, .c19, .c43) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 43⟩ ⟨(109, 393), (0, 1), (209, 911), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 19, 43)`, with 1 leaves. -/
def u15_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (209, 911), (61, 400)⟩

/-- Subtree 0 of the class triple `(5, 19, 43)` passes the check. -/
theorem u15_0_ok : treeOK (.c5, .c19, .c43)
    (rootNode (.c5, .c19, .c43)) u15_0 = true :=
  treeOK_leaf u15_0_g0

private theorem u16_0_g0 :
    leafOK (.c5, .c19, .n2) ⟨.free .q 13 [], .pin 5, .pin 19, .free .n2 11 []⟩ ⟨(109, 393), (0, 1), (209, 911), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 19, n2)`, with 1 leaves. -/
def u16_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (209, 911), (0, 1)⟩

/-- Subtree 0 of the class triple `(5, 19, n2)` passes the check. -/
theorem u16_0_ok : treeOK (.c5, .c19, .n2)
    (rootNode (.c5, .c19, .n2)) u16_0 = true :=
  treeOK_leaf u16_0_g0

private theorem u17_0_g0 :
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 61⟩ ⟨(109, 393), (0, 1), (209, 911), (79, 617)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 67⟩ ⟨(109, 393), (0, 1), (209, 911), (27, 221)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 73⟩ ⟨(109, 393), (0, 1), (209, 911), (57, 487)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 109⟩ ⟨(109, 393), (0, 1), (209, 911), (25, 261)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 151⟩ ⟨(109, 393), (0, 1), (209, 911), (59, 725)⟩))))) = true := by
  decide +kernel

private theorem u17_0_g1 :
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 307⟩ ⟨(109, 393), (0, 1), (209, 911), (48, 841)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 367⟩ ⟨(109, 393), (0, 1), (209, 911), (51, 977)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 709⟩ ⟨(109, 393), (0, 1), (209, 911), (8, 213)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 727⟩ ⟨(109, 393), (0, 1), (209, 911), (26, 701)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 991⟩ ⟨(109, 393), (0, 1), (209, 911), (25, 787)⟩))))) = true := by
  decide +kernel

private theorem u17_0_g2 :
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 1087⟩ ⟨(109, 393), (0, 1), (209, 911), (30, 989)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 1723⟩ ⟨(109, 393), (0, 1), (209, 911), (2, 83)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 2053⟩ ⟨(109, 393), (0, 1), (209, 911), (13, 589)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 3019⟩ ⟨(109, 393), (0, 1), (209, 911), (18, 989)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 3541⟩ ⟨(109, 393), (0, 1), (209, 911), (2, 119)⟩))))) = true := by
  decide +kernel

private theorem u17_0_g3 :
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 5113⟩ ⟨(109, 393), (0, 1), (209, 911), (2, 143)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 8011⟩ ⟨(109, 393), (0, 1), (209, 911), (2, 179)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 10303⟩ ⟨(109, 393), (0, 1), (209, 911), (2, 203)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 17293⟩ ⟨(109, 393), (0, 1), (209, 911), (2, 263)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 28057⟩ ⟨(109, 393), (0, 1), (209, 911), (2, 335)⟩))))) = true := by
  decide +kernel

private theorem u17_0_g4 :
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 30103⟩ ⟨(109, 393), (0, 1), (209, 911), (2, 347)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .pin 86143⟩ ⟨(109, 393), (0, 1), (209, 911), (2, 587)⟩ &&
    (leafOK (.c5, .c19, .big) ⟨.free .q 13 [], .pin 5, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 367, 307, 151, 109, 73, 67, 61]⟩ ⟨(109, 393), (0, 1), (209, 911), (1, 8)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 19, big)`, with 23 leaves. -/
def u17_0 : Tree :=
  .split 3 61
    (.leaf ⟨(109, 393), (0, 1), (209, 911), (79, 617)⟩)
    (.split 3 67
      (.leaf ⟨(109, 393), (0, 1), (209, 911), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(109, 393), (0, 1), (209, 911), (57, 487)⟩)
        (.split 3 109
          (.leaf ⟨(109, 393), (0, 1), (209, 911), (25, 261)⟩)
          (.split 3 151
            (.leaf ⟨(109, 393), (0, 1), (209, 911), (59, 725)⟩)
            (.split 3 307
              (.leaf ⟨(109, 393), (0, 1), (209, 911), (48, 841)⟩)
              (.split 3 367
                (.leaf ⟨(109, 393), (0, 1), (209, 911), (51, 977)⟩)
                (.split 3 709
                  (.leaf ⟨(109, 393), (0, 1), (209, 911), (8, 213)⟩)
                  (.split 3 727
                    (.leaf ⟨(109, 393), (0, 1), (209, 911), (26, 701)⟩)
                    (.split 3 991
                      (.leaf ⟨(109, 393), (0, 1), (209, 911), (25, 787)⟩)
                      (.split 3 1087
                        (.leaf ⟨(109, 393), (0, 1), (209, 911), (30, 989)⟩)
                        (.split 3 1723
                          (.leaf ⟨(109, 393), (0, 1), (209, 911), (2, 83)⟩)
                          (.split 3 2053
                            (.leaf ⟨(109, 393), (0, 1), (209, 911), (13, 589)⟩)
                            (.split 3 3019
                              (.leaf ⟨(109, 393), (0, 1), (209, 911), (18, 989)⟩)
                              (.split 3 3541
                                (.leaf ⟨(109, 393), (0, 1), (209, 911), (2, 119)⟩)
                                (.split 3 5113
                                  (.leaf ⟨(109, 393), (0, 1), (209, 911), (2, 143)⟩)
                                  (.split 3 8011
                                    (.leaf ⟨(109, 393), (0, 1), (209, 911), (2, 179)⟩)
                                    (.split 3 10303
                                      (.leaf ⟨(109, 393), (0, 1), (209, 911), (2, 203)⟩)
                                      (.split 3 17293
                                        (.leaf ⟨(109, 393), (0, 1), (209, 911), (2, 263)⟩)
                                        (.split 3 28057
                                          (.leaf ⟨(109, 393), (0, 1), (209, 911), (2, 335)⟩)
                                          (.split 3 30103
                                            (.leaf ⟨(109, 393), (0, 1), (209, 911), (2, 347)⟩)
                                            (.split 3 86143
                                              (.leaf ⟨(109, 393), (0, 1), (209, 911), (2, 587)⟩)
                                              (.leaf ⟨(109, 393), (0, 1), (209, 911), (1, 8)⟩))))))))))))))))))))))

/-- Subtree 0 of the class triple `(5, 19, big)` passes the check. -/
theorem u17_0_ok : treeOK (.c5, .c19, .big)
    (rootNode (.c5, .c19, .big)) u17_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u17_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u17_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u17_0_g2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g2).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g2).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u17_0_g3).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g3).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g3).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g3).2).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g3).2).2).2).2)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp u17_0_g4).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g4).2).1)
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u17_0_g4).2).2))))))))))))))))))))))

private theorem u18_0_g0 :
    leafOK (.c5, .c31, .c37) ⟨.free .q 13 [], .pin 5, .pin 31, .pin 37⟩ ⟨(109, 393), (0, 1), (155, 863), (145, 882)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 31, 37)`, with 1 leaves. -/
def u18_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (155, 863), (145, 882)⟩

/-- Subtree 0 of the class triple `(5, 31, 37)` passes the check. -/
theorem u18_0_ok : treeOK (.c5, .c31, .c37)
    (rootNode (.c5, .c31, .c37)) u18_0 = true :=
  treeOK_leaf u18_0_g0

private theorem u19_0_g0 :
    leafOK (.c5, .c31, .c43) ⟨.free .q 13 [], .pin 5, .pin 31, .pin 43⟩ ⟨(109, 393), (0, 1), (155, 863), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 31, 43)`, with 1 leaves. -/
def u19_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (155, 863), (61, 400)⟩

/-- Subtree 0 of the class triple `(5, 31, 43)` passes the check. -/
theorem u19_0_ok : treeOK (.c5, .c31, .c43)
    (rootNode (.c5, .c31, .c43)) u19_0 = true :=
  treeOK_leaf u19_0_g0

private theorem u20_0_g0 :
    leafOK (.c5, .c31, .n2) ⟨.free .q 13 [], .pin 5, .pin 31, .free .n2 11 []⟩ ⟨(109, 393), (0, 1), (155, 863), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 31, n2)`, with 1 leaves. -/
def u20_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (155, 863), (0, 1)⟩

/-- Subtree 0 of the class triple `(5, 31, n2)` passes the check. -/
theorem u20_0_ok : treeOK (.c5, .c31, .n2)
    (rootNode (.c5, .c31, .n2)) u20_0 = true :=
  treeOK_leaf u20_0_g0

private theorem u21_0_g0 :
    leafOK (.c5, .c31, .big) ⟨.free .q 13 [], .pin 5, .pin 31, .free .big 61 []⟩ ⟨(109, 393), (0, 1), (155, 863), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 31, big)`, with 1 leaves. -/
def u21_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (155, 863), (79, 617)⟩

/-- Subtree 0 of the class triple `(5, 31, big)` passes the check. -/
theorem u21_0_ok : treeOK (.c5, .c31, .big)
    (rootNode (.c5, .c31, .big)) u21_0 = true :=
  treeOK_leaf u21_0_g0

private theorem u22_0_g0 :
    leafOK (.c5, .c37, .c43) ⟨.free .q 13 [], .pin 5, .pin 37, .pin 43⟩ ⟨(109, 393), (0, 1), (145, 882), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 37, 43)`, with 1 leaves. -/
def u22_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (145, 882), (61, 400)⟩

/-- Subtree 0 of the class triple `(5, 37, 43)` passes the check. -/
theorem u22_0_ok : treeOK (.c5, .c37, .c43)
    (rootNode (.c5, .c37, .c43)) u22_0 = true :=
  treeOK_leaf u22_0_g0

private theorem u23_0_g0 :
    leafOK (.c5, .c37, .n2) ⟨.free .q 13 [], .pin 5, .pin 37, .free .n2 11 []⟩ ⟨(109, 393), (0, 1), (145, 882), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 37, n2)`, with 1 leaves. -/
def u23_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (145, 882), (0, 1)⟩

/-- Subtree 0 of the class triple `(5, 37, n2)` passes the check. -/
theorem u23_0_ok : treeOK (.c5, .c37, .n2)
    (rootNode (.c5, .c37, .n2)) u23_0 = true :=
  treeOK_leaf u23_0_g0

private theorem u24_0_g0 :
    leafOK (.c5, .c37, .big) ⟨.free .q 13 [], .pin 5, .pin 37, .free .big 61 []⟩ ⟨(109, 393), (0, 1), (145, 882), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 37, big)`, with 1 leaves. -/
def u24_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (145, 882), (79, 617)⟩

/-- Subtree 0 of the class triple `(5, 37, big)` passes the check. -/
theorem u24_0_ok : treeOK (.c5, .c37, .big)
    (rootNode (.c5, .c37, .big)) u24_0 = true :=
  treeOK_leaf u24_0_g0

private theorem u25_0_g0 :
    leafOK (.c5, .c43, .n2) ⟨.free .q 13 [], .pin 5, .pin 43, .free .n2 11 []⟩ ⟨(109, 393), (0, 1), (61, 400), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 43, n2)`, with 1 leaves. -/
def u25_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (61, 400), (0, 1)⟩

/-- Subtree 0 of the class triple `(5, 43, n2)` passes the check. -/
theorem u25_0_ok : treeOK (.c5, .c43, .n2)
    (rootNode (.c5, .c43, .n2)) u25_0 = true :=
  treeOK_leaf u25_0_g0

private theorem u26_0_g0 :
    leafOK (.c5, .c43, .big) ⟨.free .q 13 [], .pin 5, .pin 43, .free .big 61 []⟩ ⟨(109, 393), (0, 1), (61, 400), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, 43, big)`, with 1 leaves. -/
def u26_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (61, 400), (79, 617)⟩

/-- Subtree 0 of the class triple `(5, 43, big)` passes the check. -/
theorem u26_0_ok : treeOK (.c5, .c43, .big)
    (rootNode (.c5, .c43, .big)) u26_0 = true :=
  treeOK_leaf u26_0_g0

private theorem u27_0_g0 :
    leafOK (.c5, .n2, .n2) ⟨.free .q 13 [], .pin 5, .free .n2 11 [], .free .n2 11 []⟩ ⟨(109, 393), (0, 1), (0, 1), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, n2, n2)`, with 1 leaves. -/
def u27_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (0, 1), (0, 1)⟩

/-- Subtree 0 of the class triple `(5, n2, n2)` passes the check. -/
theorem u27_0_ok : treeOK (.c5, .n2, .n2)
    (rootNode (.c5, .n2, .n2)) u27_0 = true :=
  treeOK_leaf u27_0_g0

private theorem u28_0_g0 :
    leafOK (.c5, .n2, .big) ⟨.free .q 13 [], .pin 5, .free .n2 11 [], .free .big 61 []⟩ ⟨(109, 393), (0, 1), (0, 1), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, n2, big)`, with 1 leaves. -/
def u28_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (0, 1), (79, 617)⟩

/-- Subtree 0 of the class triple `(5, n2, big)` passes the check. -/
theorem u28_0_ok : treeOK (.c5, .n2, .big)
    (rootNode (.c5, .n2, .big)) u28_0 = true :=
  treeOK_leaf u28_0_g0

private theorem u29_0_g0 :
    leafOK (.c5, .big, .big) ⟨.free .q 13 [], .pin 5, .free .big 61 [], .free .big 61 []⟩ ⟨(109, 393), (0, 1), (79, 617), (1, 8)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(5, big, big)`, with 1 leaves. -/
def u29_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (79, 617), (1, 8)⟩

/-- Subtree 0 of the class triple `(5, big, big)` passes the check. -/
theorem u29_0_ok : treeOK (.c5, .big, .big)
    (rootNode (.c5, .big, .big)) u29_0 = true :=
  treeOK_leaf u29_0_g0

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u6_0_ok
#print axioms OddPerfect.ThreeFreeThree.u7_0_ok
#print axioms OddPerfect.ThreeFreeThree.u8_0_ok
#print axioms OddPerfect.ThreeFreeThree.u9_0_ok
#print axioms OddPerfect.ThreeFreeThree.u10_0_ok
#print axioms OddPerfect.ThreeFreeThree.u11_0_ok
#print axioms OddPerfect.ThreeFreeThree.u12_0_ok
#print axioms OddPerfect.ThreeFreeThree.u13_0_ok
#print axioms OddPerfect.ThreeFreeThree.u14_0_ok
#print axioms OddPerfect.ThreeFreeThree.u15_0_ok
#print axioms OddPerfect.ThreeFreeThree.u16_0_ok
#print axioms OddPerfect.ThreeFreeThree.u17_0_ok
#print axioms OddPerfect.ThreeFreeThree.u18_0_ok
#print axioms OddPerfect.ThreeFreeThree.u19_0_ok
#print axioms OddPerfect.ThreeFreeThree.u20_0_ok
#print axioms OddPerfect.ThreeFreeThree.u21_0_ok
#print axioms OddPerfect.ThreeFreeThree.u22_0_ok
#print axioms OddPerfect.ThreeFreeThree.u23_0_ok
#print axioms OddPerfect.ThreeFreeThree.u24_0_ok
#print axioms OddPerfect.ThreeFreeThree.u25_0_ok
#print axioms OddPerfect.ThreeFreeThree.u26_0_ok
#print axioms OddPerfect.ThreeFreeThree.u27_0_ok
#print axioms OddPerfect.ThreeFreeThree.u28_0_ok
#print axioms OddPerfect.ThreeFreeThree.u29_0_ok
