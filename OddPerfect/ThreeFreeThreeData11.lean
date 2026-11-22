import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 11

Subtrees of the case analysis certificate for the class triples `(31, big, big)`,
`(37, 43, n2)`, `(37, 43, big)`, `(37, n2, n2)`, `(37, n2, big)`, `(37, big, big)`,
`(43, n2, n2)`, `(43, n2, big)`, `(43, big, big)`, `(n2, n2, n2)`, `(n2, n2, big)`,
`(n2, big, big)`, `(big, big, big)`, with 85 leaves in all. Each public theorem states
that a subtree passes `treeOK` from explicit constraints. The data was found by a
search outside Lean; everything in this file is rechecked by the kernel through
`decide +kernel` on the leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u89_0_g0 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 67⟩ ⟨(109, 393), (155, 863), (79, 617), (27, 221)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 73⟩ ⟨(109, 393), (155, 863), (79, 617), (57, 487)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 109⟩ ⟨(109, 393), (155, 863), (79, 617), (25, 261)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 151⟩ ⟨(109, 393), (155, 863), (79, 617), (59, 725)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 307⟩ ⟨(109, 393), (155, 863), (79, 617), (48, 841)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g1 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 709⟩ ⟨(109, 393), (155, 863), (79, 617), (8, 213)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 727⟩ ⟨(109, 393), (155, 863), (79, 617), (26, 701)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 991⟩ ⟨(109, 393), (155, 863), (79, 617), (25, 787)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 1087⟩ ⟨(109, 393), (155, 863), (79, 617), (30, 989)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 1723⟩ ⟨(109, 393), (155, 863), (79, 617), (2, 83)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g2 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 3541⟩ ⟨(109, 393), (155, 863), (79, 617), (2, 119)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 5113⟩ ⟨(109, 393), (155, 863), (79, 617), (2, 143)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 8011⟩ ⟨(109, 393), (155, 863), (79, 617), (2, 179)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 10303⟩ ⟨(109, 393), (155, 863), (79, 617), (2, 203)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 17293⟩ ⟨(109, 393), (155, 863), (79, 617), (2, 263)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g3 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 28057⟩ ⟨(109, 393), (155, 863), (79, 617), (2, 335)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 30103⟩ ⟨(109, 393), (155, 863), (79, 617), (2, 347)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .pin 86143⟩ ⟨(109, 393), (155, 863), (79, 617), (2, 587)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 61, .free .big 62 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67]⟩ ⟨(109, 393), (155, 863), (79, 617), (1, 8)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 73⟩ ⟨(109, 393), (155, 863), (27, 221), (57, 487)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g4 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 109⟩ ⟨(109, 393), (155, 863), (27, 221), (25, 261)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 151⟩ ⟨(109, 393), (155, 863), (27, 221), (59, 725)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 307⟩ ⟨(109, 393), (155, 863), (27, 221), (48, 841)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 709⟩ ⟨(109, 393), (155, 863), (27, 221), (8, 213)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 727⟩ ⟨(109, 393), (155, 863), (27, 221), (26, 701)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g5 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 991⟩ ⟨(109, 393), (155, 863), (27, 221), (25, 787)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 1087⟩ ⟨(109, 393), (155, 863), (27, 221), (30, 989)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 1723⟩ ⟨(109, 393), (155, 863), (27, 221), (2, 83)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 3541⟩ ⟨(109, 393), (155, 863), (27, 221), (2, 119)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 5113⟩ ⟨(109, 393), (155, 863), (27, 221), (2, 143)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g6 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 8011⟩ ⟨(109, 393), (155, 863), (27, 221), (2, 179)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 10303⟩ ⟨(109, 393), (155, 863), (27, 221), (2, 203)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 17293⟩ ⟨(109, 393), (155, 863), (27, 221), (2, 263)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 28057⟩ ⟨(109, 393), (155, 863), (27, 221), (2, 335)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 30103⟩ ⟨(109, 393), (155, 863), (27, 221), (2, 347)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g7 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .pin 86143⟩ ⟨(109, 393), (155, 863), (27, 221), (2, 587)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 67, .free .big 68 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73]⟩ ⟨(109, 393), (155, 863), (27, 221), (101, 845)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 73, .free .big 74 []⟩ ⟨(109, 393), (155, 863), (57, 487), (85, 741)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 109, .free .big 110 []⟩ ⟨(109, 393), (155, 863), (25, 261), (91, 963)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 151, .free .big 152 []⟩ ⟨(109, 393), (155, 863), (59, 725), (22, 273)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g8 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 307, .free .big 308 []⟩ ⟨(109, 393), (155, 863), (48, 841), (33, 581)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 709, .free .big 710 []⟩ ⟨(109, 393), (155, 863), (8, 213), (22, 587)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 727, .free .big 728 []⟩ ⟨(109, 393), (155, 863), (26, 701), (1, 27)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 991, .free .big 992 []⟩ ⟨(109, 393), (155, 863), (25, 787), (19, 599)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 1087, .free .big 1088 []⟩ ⟨(109, 393), (155, 863), (30, 989), (1, 33)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g9 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 1723, .free .big 1724 []⟩ ⟨(109, 393), (155, 863), (2, 83), (24, 997)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 3541, .free .big 3542 []⟩ ⟨(109, 393), (155, 863), (2, 119), (2, 119)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 5113, .free .big 5114 []⟩ ⟨(109, 393), (155, 863), (2, 143), (2, 143)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 8011, .free .big 8012 []⟩ ⟨(109, 393), (155, 863), (2, 179), (2, 179)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 10303, .free .big 10304 []⟩ ⟨(109, 393), (155, 863), (2, 203), (2, 203)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g10 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 17293, .free .big 17294 []⟩ ⟨(109, 393), (155, 863), (2, 263), (2, 263)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 28057, .free .big 28058 []⟩ ⟨(109, 393), (155, 863), (2, 335), (2, 335)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 30103, .free .big 30104 []⟩ ⟨(109, 393), (155, 863), (2, 347), (2, 347)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .pin 86143, .free .big 86144 []⟩ ⟨(109, 393), (155, 863), (2, 587), (2, 587)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 67⟩ ⟨(109, 393), (155, 863), (1, 8), (27, 221)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g11 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 73⟩ ⟨(109, 393), (155, 863), (1, 8), (57, 487)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 109⟩ ⟨(109, 393), (155, 863), (1, 8), (25, 261)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 151⟩ ⟨(109, 393), (155, 863), (1, 8), (59, 725)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 307⟩ ⟨(109, 393), (155, 863), (1, 8), (48, 841)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 709⟩ ⟨(109, 393), (155, 863), (1, 8), (8, 213)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g12 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 727⟩ ⟨(109, 393), (155, 863), (1, 8), (26, 701)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 991⟩ ⟨(109, 393), (155, 863), (1, 8), (25, 787)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 1087⟩ ⟨(109, 393), (155, 863), (1, 8), (30, 989)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 1723⟩ ⟨(109, 393), (155, 863), (1, 8), (2, 83)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 3541⟩ ⟨(109, 393), (155, 863), (1, 8), (2, 119)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g13 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 5113⟩ ⟨(109, 393), (155, 863), (1, 8), (2, 143)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 8011⟩ ⟨(109, 393), (155, 863), (1, 8), (2, 179)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 10303⟩ ⟨(109, 393), (155, 863), (1, 8), (2, 203)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 17293⟩ ⟨(109, 393), (155, 863), (1, 8), (2, 263)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 28057⟩ ⟨(109, 393), (155, 863), (1, 8), (2, 335)⟩))))) = true := by
  decide +kernel

private theorem u89_0_g14 :
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 30103⟩ ⟨(109, 393), (155, 863), (1, 8), (2, 347)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .pin 86143⟩ ⟨(109, 393), (155, 863), (1, 8), (2, 587)⟩ &&
    (leafOK (.c31, .big, .big) ⟨.free .q 13 [], .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67, 61], .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 5113, 3541, 1723, 1087, 991, 727, 709, 307, 151, 109, 73, 67]⟩ ⟨(109, 393), (155, 863), (1, 8), (101, 845)⟩))) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(31, big, big)`, with 73 leaves. -/
def u89_0 : Tree :=
  .split 2 61
    (.split 3 67
      (.leaf ⟨(109, 393), (155, 863), (79, 617), (27, 221)⟩)
      (.split 3 73
        (.leaf ⟨(109, 393), (155, 863), (79, 617), (57, 487)⟩)
        (.split 3 109
          (.leaf ⟨(109, 393), (155, 863), (79, 617), (25, 261)⟩)
          (.split 3 151
            (.leaf ⟨(109, 393), (155, 863), (79, 617), (59, 725)⟩)
            (.split 3 307
              (.leaf ⟨(109, 393), (155, 863), (79, 617), (48, 841)⟩)
              (.split 3 709
                (.leaf ⟨(109, 393), (155, 863), (79, 617), (8, 213)⟩)
                (.split 3 727
                  (.leaf ⟨(109, 393), (155, 863), (79, 617), (26, 701)⟩)
                  (.split 3 991
                    (.leaf ⟨(109, 393), (155, 863), (79, 617), (25, 787)⟩)
                    (.split 3 1087
                      (.leaf ⟨(109, 393), (155, 863), (79, 617), (30, 989)⟩)
                      (.split 3 1723
                        (.leaf ⟨(109, 393), (155, 863), (79, 617), (2, 83)⟩)
                        (.split 3 3541
                          (.leaf ⟨(109, 393), (155, 863), (79, 617), (2, 119)⟩)
                          (.split 3 5113
                            (.leaf ⟨(109, 393), (155, 863), (79, 617), (2, 143)⟩)
                            (.split 3 8011
                              (.leaf ⟨(109, 393), (155, 863), (79, 617), (2, 179)⟩)
                              (.split 3 10303
                                (.leaf ⟨(109, 393), (155, 863), (79, 617), (2, 203)⟩)
                                (.split 3 17293
                                  (.leaf ⟨(109, 393), (155, 863), (79, 617), (2, 263)⟩)
                                  (.split 3 28057
                                    (.leaf ⟨(109, 393), (155, 863), (79, 617), (2, 335)⟩)
                                    (.split 3 30103
                                      (.leaf ⟨(109, 393), (155, 863), (79, 617), (2, 347)⟩)
                                      (.split 3 86143
                                        (.leaf ⟨(109, 393), (155, 863), (79, 617), (2, 587)⟩)
                                        (.leaf ⟨(109, 393), (155, 863), (79, 617), (1, 8)⟩)))))))))))))))))))
    (.split 2 67
      (.split 3 73
        (.leaf ⟨(109, 393), (155, 863), (27, 221), (57, 487)⟩)
        (.split 3 109
          (.leaf ⟨(109, 393), (155, 863), (27, 221), (25, 261)⟩)
          (.split 3 151
            (.leaf ⟨(109, 393), (155, 863), (27, 221), (59, 725)⟩)
            (.split 3 307
              (.leaf ⟨(109, 393), (155, 863), (27, 221), (48, 841)⟩)
              (.split 3 709
                (.leaf ⟨(109, 393), (155, 863), (27, 221), (8, 213)⟩)
                (.split 3 727
                  (.leaf ⟨(109, 393), (155, 863), (27, 221), (26, 701)⟩)
                  (.split 3 991
                    (.leaf ⟨(109, 393), (155, 863), (27, 221), (25, 787)⟩)
                    (.split 3 1087
                      (.leaf ⟨(109, 393), (155, 863), (27, 221), (30, 989)⟩)
                      (.split 3 1723
                        (.leaf ⟨(109, 393), (155, 863), (27, 221), (2, 83)⟩)
                        (.split 3 3541
                          (.leaf ⟨(109, 393), (155, 863), (27, 221), (2, 119)⟩)
                          (.split 3 5113
                            (.leaf ⟨(109, 393), (155, 863), (27, 221), (2, 143)⟩)
                            (.split 3 8011
                              (.leaf ⟨(109, 393), (155, 863), (27, 221), (2, 179)⟩)
                              (.split 3 10303
                                (.leaf ⟨(109, 393), (155, 863), (27, 221), (2, 203)⟩)
                                (.split 3 17293
                                  (.leaf ⟨(109, 393), (155, 863), (27, 221), (2, 263)⟩)
                                  (.split 3 28057
                                    (.leaf ⟨(109, 393), (155, 863), (27, 221), (2, 335)⟩)
                                    (.split 3 30103
                                      (.leaf ⟨(109, 393), (155, 863), (27, 221), (2, 347)⟩)
                                      (.split 3 86143
                                        (.leaf ⟨(109, 393), (155, 863), (27, 221), (2, 587)⟩)
                                        (.leaf ⟨(109, 393), (155, 863), (27, 221), (101, 845)⟩))))))))))))))))))
      (.split 2 73
        (.leaf ⟨(109, 393), (155, 863), (57, 487), (85, 741)⟩)
        (.split 2 109
          (.leaf ⟨(109, 393), (155, 863), (25, 261), (91, 963)⟩)
          (.split 2 151
            (.leaf ⟨(109, 393), (155, 863), (59, 725), (22, 273)⟩)
            (.split 2 307
              (.leaf ⟨(109, 393), (155, 863), (48, 841), (33, 581)⟩)
              (.split 2 709
                (.leaf ⟨(109, 393), (155, 863), (8, 213), (22, 587)⟩)
                (.split 2 727
                  (.leaf ⟨(109, 393), (155, 863), (26, 701), (1, 27)⟩)
                  (.split 2 991
                    (.leaf ⟨(109, 393), (155, 863), (25, 787), (19, 599)⟩)
                    (.split 2 1087
                      (.leaf ⟨(109, 393), (155, 863), (30, 989), (1, 33)⟩)
                      (.split 2 1723
                        (.leaf ⟨(109, 393), (155, 863), (2, 83), (24, 997)⟩)
                        (.split 2 3541
                          (.leaf ⟨(109, 393), (155, 863), (2, 119), (2, 119)⟩)
                          (.split 2 5113
                            (.leaf ⟨(109, 393), (155, 863), (2, 143), (2, 143)⟩)
                            (.split 2 8011
                              (.leaf ⟨(109, 393), (155, 863), (2, 179), (2, 179)⟩)
                              (.split 2 10303
                                (.leaf ⟨(109, 393), (155, 863), (2, 203), (2, 203)⟩)
                                (.split 2 17293
                                  (.leaf ⟨(109, 393), (155, 863), (2, 263), (2, 263)⟩)
                                  (.split 2 28057
                                    (.leaf ⟨(109, 393), (155, 863), (2, 335), (2, 335)⟩)
                                    (.split 2 30103
                                      (.leaf ⟨(109, 393), (155, 863), (2, 347), (2, 347)⟩)
                                      (.split 2 86143
                                        (.leaf ⟨(109, 393), (155, 863), (2, 587), (2, 587)⟩)
                                        (.split 3 67
                                          (.leaf ⟨(109, 393), (155, 863), (1, 8), (27, 221)⟩)
                                          (.split 3 73
                                            (.leaf ⟨(109, 393), (155, 863), (1, 8), (57, 487)⟩)
                                            (.split 3 109
                                              (.leaf ⟨(109, 393), (155, 863), (1, 8), (25, 261)⟩)
                                              (.split 3 151
                                                (.leaf ⟨(109, 393), (155, 863), (1, 8), (59, 725)⟩)
                                                (.split 3 307
                                                  (.leaf ⟨(109, 393), (155, 863), (1, 8), (48, 841)⟩)
                                                  (.split 3 709
                                                    (.leaf ⟨(109, 393), (155, 863), (1, 8), (8, 213)⟩)
                                                    (.split 3 727
                                                      (.leaf ⟨(109, 393), (155, 863), (1, 8), (26, 701)⟩)
                                                      (.split 3 991
                                                        (.leaf ⟨(109, 393), (155, 863), (1, 8), (25, 787)⟩)
                                                        (.split 3 1087
                                                          (.leaf ⟨(109, 393), (155, 863), (1, 8), (30, 989)⟩)
                                                          (.split 3 1723
                                                            (.leaf ⟨(109, 393), (155, 863), (1, 8), (2, 83)⟩)
                                                            (.split 3 3541
                                                              (.leaf ⟨(109, 393), (155, 863), (1, 8), (2, 119)⟩)
                                                              (.split 3 5113
                                                                (.leaf ⟨(109, 393), (155, 863), (1, 8), (2, 143)⟩)
                                                                (.split 3 8011
                                                                  (.leaf ⟨(109, 393), (155, 863), (1, 8), (2, 179)⟩)
                                                                  (.split 3 10303
                                                                    (.leaf ⟨(109, 393), (155, 863), (1, 8), (2, 203)⟩)
                                                                    (.split 3 17293
                                                                      (.leaf ⟨(109, 393), (155, 863), (1, 8), (2, 263)⟩)
                                                                      (.split 3 28057
                                                                        (.leaf ⟨(109, 393), (155, 863), (1, 8), (2, 335)⟩)
                                                                        (.split 3 30103
                                                                          (.leaf ⟨(109, 393), (155, 863), (1, 8), (2, 347)⟩)
                                                                          (.split 3 86143
                                                                            (.leaf ⟨(109, 393), (155, 863), (1, 8), (2, 587)⟩)
                                                                            (.leaf ⟨(109, 393), (155, 863), (1, 8), (101, 845)⟩)))))))))))))))))))))))))))))))))))))

/-- Subtree 0 of the class triple `(31, big, big)` passes the check. -/
theorem u89_0_ok : treeOK (.c31, .big, .big)
    (rootNode (.c31, .big, .big)) u89_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g0).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g0).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g0).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g0).2).2).2).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g0).2).2).2).2)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g1).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g1).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g1).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g1).2).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g1).2).2).2).2)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g2).2).2).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g2).2).2).2).2)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g3).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g3).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g3).2).2).1)
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g3).2).2).2).1)))))))))))))))))))
    (treeOK_split (by decide) rfl
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g3).2).2).2).2)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g4).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g4).2).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g4).2).2).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g4).2).2).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g4).2).2).2).2)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g5).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g5).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g5).2).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g5).2).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g5).2).2).2).2)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g6).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g6).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g6).2).2).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g6).2).2).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g6).2).2).2).2)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g7).1)
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g7).2).1))))))))))))))))))
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g7).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g7).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g7).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g8).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g8).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g8).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g8).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g8).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g9).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g9).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g9).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g9).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g9).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g10).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g10).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g10).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g10).2).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g10).2).2).2).2)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g11).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g11).2).1)
                                              (treeOK_split (by decide) rfl
                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g11).2).2).1)
                                                (treeOK_split (by decide) rfl
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g11).2).2).2).1)
                                                  (treeOK_split (by decide) rfl
                                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g11).2).2).2).2)
                                                    (treeOK_split (by decide) rfl
                                                      (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g12).1)
                                                      (treeOK_split (by decide) rfl
                                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g12).2).1)
                                                        (treeOK_split (by decide) rfl
                                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g12).2).2).1)
                                                          (treeOK_split (by decide) rfl
                                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g12).2).2).2).1)
                                                            (treeOK_split (by decide) rfl
                                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g12).2).2).2).2)
                                                              (treeOK_split (by decide) rfl
                                                                (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g13).1)
                                                                (treeOK_split (by decide) rfl
                                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g13).2).1)
                                                                  (treeOK_split (by decide) rfl
                                                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g13).2).2).1)
                                                                    (treeOK_split (by decide) rfl
                                                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g13).2).2).2).1)
                                                                      (treeOK_split (by decide) rfl
                                                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g13).2).2).2).2)
                                                                        (treeOK_split (by decide) rfl
                                                                          (treeOK_leaf (Bool.and_eq_true_iff.mp u89_0_g14).1)
                                                                          (treeOK_split (by decide) rfl
                                                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g14).2).1)
                                                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u89_0_g14).2).2)))))))))))))))))))))))))))))))))))))

private theorem u90_0_g0 :
    leafOK (.c37, .c43, .n2) ⟨.free .q 13 [], .pin 37, .pin 43, .free .n2 11 []⟩ ⟨(109, 393), (145, 882), (61, 400), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(37, 43, n2)`, with 1 leaves. -/
def u90_0 : Tree :=
  .leaf ⟨(109, 393), (145, 882), (61, 400), (0, 1)⟩

/-- Subtree 0 of the class triple `(37, 43, n2)` passes the check. -/
theorem u90_0_ok : treeOK (.c37, .c43, .n2)
    (rootNode (.c37, .c43, .n2)) u90_0 = true :=
  treeOK_leaf u90_0_g0

private theorem u91_0_g0 :
    leafOK (.c37, .c43, .big) ⟨.free .q 13 [], .pin 37, .pin 43, .free .big 61 []⟩ ⟨(109, 393), (145, 882), (61, 400), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(37, 43, big)`, with 1 leaves. -/
def u91_0 : Tree :=
  .leaf ⟨(109, 393), (145, 882), (61, 400), (79, 617)⟩

/-- Subtree 0 of the class triple `(37, 43, big)` passes the check. -/
theorem u91_0_ok : treeOK (.c37, .c43, .big)
    (rootNode (.c37, .c43, .big)) u91_0 = true :=
  treeOK_leaf u91_0_g0

private theorem u92_0_g0 :
    leafOK (.c37, .n2, .n2) ⟨.free .q 13 [], .pin 37, .free .n2 11 [], .free .n2 11 []⟩ ⟨(109, 393), (145, 882), (0, 1), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(37, n2, n2)`, with 1 leaves. -/
def u92_0 : Tree :=
  .leaf ⟨(109, 393), (145, 882), (0, 1), (0, 1)⟩

/-- Subtree 0 of the class triple `(37, n2, n2)` passes the check. -/
theorem u92_0_ok : treeOK (.c37, .n2, .n2)
    (rootNode (.c37, .n2, .n2)) u92_0 = true :=
  treeOK_leaf u92_0_g0

private theorem u93_0_g0 :
    leafOK (.c37, .n2, .big) ⟨.free .q 13 [], .pin 37, .free .n2 11 [], .free .big 61 []⟩ ⟨(109, 393), (145, 882), (0, 1), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(37, n2, big)`, with 1 leaves. -/
def u93_0 : Tree :=
  .leaf ⟨(109, 393), (145, 882), (0, 1), (79, 617)⟩

/-- Subtree 0 of the class triple `(37, n2, big)` passes the check. -/
theorem u93_0_ok : treeOK (.c37, .n2, .big)
    (rootNode (.c37, .n2, .big)) u93_0 = true :=
  treeOK_leaf u93_0_g0

private theorem u94_0_g0 :
    leafOK (.c37, .big, .big) ⟨.free .q 13 [], .pin 37, .free .big 61 [], .free .big 61 []⟩ ⟨(109, 393), (145, 882), (79, 617), (1, 8)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(37, big, big)`, with 1 leaves. -/
def u94_0 : Tree :=
  .leaf ⟨(109, 393), (145, 882), (79, 617), (1, 8)⟩

/-- Subtree 0 of the class triple `(37, big, big)` passes the check. -/
theorem u94_0_ok : treeOK (.c37, .big, .big)
    (rootNode (.c37, .big, .big)) u94_0 = true :=
  treeOK_leaf u94_0_g0

private theorem u95_0_g0 :
    leafOK (.c43, .n2, .n2) ⟨.free .q 13 [], .pin 43, .free .n2 11 [], .free .n2 11 []⟩ ⟨(109, 393), (61, 400), (0, 1), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(43, n2, n2)`, with 1 leaves. -/
def u95_0 : Tree :=
  .leaf ⟨(109, 393), (61, 400), (0, 1), (0, 1)⟩

/-- Subtree 0 of the class triple `(43, n2, n2)` passes the check. -/
theorem u95_0_ok : treeOK (.c43, .n2, .n2)
    (rootNode (.c43, .n2, .n2)) u95_0 = true :=
  treeOK_leaf u95_0_g0

private theorem u96_0_g0 :
    leafOK (.c43, .n2, .big) ⟨.free .q 13 [], .pin 43, .free .n2 11 [], .free .big 61 []⟩ ⟨(109, 393), (61, 400), (0, 1), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(43, n2, big)`, with 1 leaves. -/
def u96_0 : Tree :=
  .leaf ⟨(109, 393), (61, 400), (0, 1), (79, 617)⟩

/-- Subtree 0 of the class triple `(43, n2, big)` passes the check. -/
theorem u96_0_ok : treeOK (.c43, .n2, .big)
    (rootNode (.c43, .n2, .big)) u96_0 = true :=
  treeOK_leaf u96_0_g0

private theorem u97_0_g0 :
    leafOK (.c43, .big, .big) ⟨.free .q 13 [], .pin 43, .free .big 61 [], .free .big 61 []⟩ ⟨(109, 393), (61, 400), (79, 617), (1, 8)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(43, big, big)`, with 1 leaves. -/
def u97_0 : Tree :=
  .leaf ⟨(109, 393), (61, 400), (79, 617), (1, 8)⟩

/-- Subtree 0 of the class triple `(43, big, big)` passes the check. -/
theorem u97_0_ok : treeOK (.c43, .big, .big)
    (rootNode (.c43, .big, .big)) u97_0 = true :=
  treeOK_leaf u97_0_g0

private theorem u98_0_g0 :
    leafOK (.n2, .n2, .n2) ⟨.free .q 13 [], .free .n2 11 [], .free .n2 11 [], .free .n2 11 []⟩ ⟨(109, 393), (0, 1), (0, 1), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(n2, n2, n2)`, with 1 leaves. -/
def u98_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (0, 1), (0, 1)⟩

/-- Subtree 0 of the class triple `(n2, n2, n2)` passes the check. -/
theorem u98_0_ok : treeOK (.n2, .n2, .n2)
    (rootNode (.n2, .n2, .n2)) u98_0 = true :=
  treeOK_leaf u98_0_g0

private theorem u99_0_g0 :
    leafOK (.n2, .n2, .big) ⟨.free .q 13 [], .free .n2 11 [], .free .n2 11 [], .free .big 61 []⟩ ⟨(109, 393), (0, 1), (0, 1), (79, 617)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(n2, n2, big)`, with 1 leaves. -/
def u99_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (0, 1), (79, 617)⟩

/-- Subtree 0 of the class triple `(n2, n2, big)` passes the check. -/
theorem u99_0_ok : treeOK (.n2, .n2, .big)
    (rootNode (.n2, .n2, .big)) u99_0 = true :=
  treeOK_leaf u99_0_g0

private theorem u100_0_g0 :
    leafOK (.n2, .big, .big) ⟨.free .q 13 [], .free .n2 11 [], .free .big 61 [], .free .big 61 []⟩ ⟨(109, 393), (0, 1), (79, 617), (1, 8)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(n2, big, big)`, with 1 leaves. -/
def u100_0 : Tree :=
  .leaf ⟨(109, 393), (0, 1), (79, 617), (1, 8)⟩

/-- Subtree 0 of the class triple `(n2, big, big)` passes the check. -/
theorem u100_0_ok : treeOK (.n2, .big, .big)
    (rootNode (.n2, .big, .big)) u100_0 = true :=
  treeOK_leaf u100_0_g0

private theorem u101_0_g0 :
    leafOK (.big, .big, .big) ⟨.free .q 13 [], .free .big 61 [], .free .big 61 [], .free .big 61 []⟩ ⟨(109, 393), (79, 617), (1, 8), (27, 221)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(big, big, big)`, with 1 leaves. -/
def u101_0 : Tree :=
  .leaf ⟨(109, 393), (79, 617), (1, 8), (27, 221)⟩

/-- Subtree 0 of the class triple `(big, big, big)` passes the check. -/
theorem u101_0_ok : treeOK (.big, .big, .big)
    (rootNode (.big, .big, .big)) u101_0 = true :=
  treeOK_leaf u101_0_g0

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u89_0_ok
#print axioms OddPerfect.ThreeFreeThree.u90_0_ok
#print axioms OddPerfect.ThreeFreeThree.u91_0_ok
#print axioms OddPerfect.ThreeFreeThree.u92_0_ok
#print axioms OddPerfect.ThreeFreeThree.u93_0_ok
#print axioms OddPerfect.ThreeFreeThree.u94_0_ok
#print axioms OddPerfect.ThreeFreeThree.u95_0_ok
#print axioms OddPerfect.ThreeFreeThree.u96_0_ok
#print axioms OddPerfect.ThreeFreeThree.u97_0_ok
#print axioms OddPerfect.ThreeFreeThree.u98_0_ok
#print axioms OddPerfect.ThreeFreeThree.u99_0_ok
#print axioms OddPerfect.ThreeFreeThree.u100_0_ok
#print axioms OddPerfect.ThreeFreeThree.u101_0_ok
