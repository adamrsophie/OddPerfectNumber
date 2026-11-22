import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 4

Subtrees of the case analysis certificate for the class triples `(7, 19, big)`,
`(7, 31, 37)`, with 129 leaves in all. Each public theorem states that a subtree passes
`treeOK` from explicit constraints. The data was found by a search outside Lean;
everything in this file is rechecked by the kernel through `decide +kernel` on the
leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u40_0_g0 :
    (leafOK (.c7, .c19, .big) ⟨.pin 13, .pin 7, .pin 19, .pin 61⟩ ⟨(109, 393), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 37, .pin 7, .pin 19, .pin 61⟩ ⟨(145, 882), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 73, .pin 7, .pin 19, .pin 61⟩ ⟨(57, 487), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 109, .pin 7, .pin 19, .pin 61⟩ ⟨(25, 261), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 409, .pin 7, .pin 19, .pin 61⟩ ⟨(9, 182), (223, 590), (209, 911), (79, 617)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g1 :
    (leafOK (.c7, .c19, .big) ⟨.pin 709, .pin 7, .pin 19, .pin 61⟩ ⟨(8, 213), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 2053, .pin 7, .pin 19, .pin 61⟩ ⟨(13, 589), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 3541, .pin 7, .pin 19, .pin 61⟩ ⟨(2, 119), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 5113, .pin 7, .pin 19, .pin 61⟩ ⟨(2, 143), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 7789, .pin 7, .pin 19, .pin 61⟩ ⟨(4, 353), (223, 590), (209, 911), (79, 617)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g2 :
    (leafOK (.c7, .c19, .big) ⟨.pin 17293, .pin 7, .pin 19, .pin 61⟩ ⟨(2, 263), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 28057, .pin 7, .pin 19, .pin 61⟩ ⟨(2, 335), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 37, 13], .pin 7, .pin 19, .pin 61⟩ ⟨(1, 5), (223, 590), (209, 911), (79, 617)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 13, .pin 7, .pin 19, .pin 67⟩ ⟨(109, 393), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 37, .pin 7, .pin 19, .pin 67⟩ ⟨(145, 882), (223, 590), (209, 911), (27, 221)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g3 :
    (leafOK (.c7, .c19, .big) ⟨.pin 61, .pin 7, .pin 19, .pin 67⟩ ⟨(79, 617), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 73, .pin 7, .pin 19, .pin 67⟩ ⟨(57, 487), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 109, .pin 7, .pin 19, .pin 67⟩ ⟨(25, 261), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 409, .pin 7, .pin 19, .pin 67⟩ ⟨(9, 182), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 709, .pin 7, .pin 19, .pin 67⟩ ⟨(8, 213), (223, 590), (209, 911), (27, 221)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g4 :
    (leafOK (.c7, .c19, .big) ⟨.pin 2053, .pin 7, .pin 19, .pin 67⟩ ⟨(13, 589), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 3541, .pin 7, .pin 19, .pin 67⟩ ⟨(2, 119), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 5113, .pin 7, .pin 19, .pin 67⟩ ⟨(2, 143), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 7789, .pin 7, .pin 19, .pin 67⟩ ⟨(4, 353), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 17293, .pin 7, .pin 19, .pin 67⟩ ⟨(2, 263), (223, 590), (209, 911), (27, 221)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g5 :
    (leafOK (.c7, .c19, .big) ⟨.pin 28057, .pin 7, .pin 19, .pin 67⟩ ⟨(2, 335), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 19, .pin 67⟩ ⟨(1, 5), (223, 590), (209, 911), (27, 221)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 13, .pin 7, .pin 19, .pin 73⟩ ⟨(109, 393), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 37, .pin 7, .pin 19, .pin 73⟩ ⟨(145, 882), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 61, .pin 7, .pin 19, .pin 73⟩ ⟨(79, 617), (223, 590), (209, 911), (57, 487)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g6 :
    (leafOK (.c7, .c19, .big) ⟨.pin 109, .pin 7, .pin 19, .pin 73⟩ ⟨(25, 261), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 409, .pin 7, .pin 19, .pin 73⟩ ⟨(9, 182), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 709, .pin 7, .pin 19, .pin 73⟩ ⟨(8, 213), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 2053, .pin 7, .pin 19, .pin 73⟩ ⟨(13, 589), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 3541, .pin 7, .pin 19, .pin 73⟩ ⟨(2, 119), (223, 590), (209, 911), (57, 487)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g7 :
    (leafOK (.c7, .c19, .big) ⟨.pin 5113, .pin 7, .pin 19, .pin 73⟩ ⟨(2, 143), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 7789, .pin 7, .pin 19, .pin 73⟩ ⟨(4, 353), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 17293, .pin 7, .pin 19, .pin 73⟩ ⟨(2, 263), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 28057, .pin 7, .pin 19, .pin 73⟩ ⟨(2, 335), (223, 590), (209, 911), (57, 487)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 61, 37, 13], .pin 7, .pin 19, .pin 73⟩ ⟨(1, 5), (223, 590), (209, 911), (57, 487)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g8 :
    (leafOK (.c7, .c19, .big) ⟨.pin 13, .pin 7, .pin 19, .pin 79⟩ ⟨(109, 393), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 37, .pin 7, .pin 19, .pin 79⟩ ⟨(145, 882), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 61, .pin 7, .pin 19, .pin 79⟩ ⟨(79, 617), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 73, .pin 7, .pin 19, .pin 79⟩ ⟨(57, 487), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 109, .pin 7, .pin 19, .pin 79⟩ ⟨(25, 261), (223, 590), (209, 911), (107, 951)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g9 :
    (leafOK (.c7, .c19, .big) ⟨.pin 409, .pin 7, .pin 19, .pin 79⟩ ⟨(9, 182), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 709, .pin 7, .pin 19, .pin 79⟩ ⟨(8, 213), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 2053, .pin 7, .pin 19, .pin 79⟩ ⟨(13, 589), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 3541, .pin 7, .pin 19, .pin 79⟩ ⟨(2, 119), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 5113, .pin 7, .pin 19, .pin 79⟩ ⟨(2, 143), (223, 590), (209, 911), (107, 951)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g10 :
    (leafOK (.c7, .c19, .big) ⟨.pin 7789, .pin 7, .pin 19, .pin 79⟩ ⟨(4, 353), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 17293, .pin 7, .pin 19, .pin 79⟩ ⟨(2, 263), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 28057, .pin 7, .pin 19, .pin 79⟩ ⟨(2, 335), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 19, .pin 79⟩ ⟨(1, 5), (223, 590), (209, 911), (107, 951)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 109⟩ ⟨(109, 393), (223, 590), (209, 911), (25, 261)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g11 :
    (leafOK (.c7, .c19, .big) ⟨.pin 13, .pin 7, .pin 19, .pin 127⟩ ⟨(109, 393), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 37, .pin 7, .pin 19, .pin 127⟩ ⟨(145, 882), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 61, .pin 7, .pin 19, .pin 127⟩ ⟨(79, 617), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 73, .pin 7, .pin 19, .pin 127⟩ ⟨(57, 487), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 109, .pin 7, .pin 19, .pin 127⟩ ⟨(25, 261), (223, 590), (209, 911), (26, 293)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g12 :
    (leafOK (.c7, .c19, .big) ⟨.pin 409, .pin 7, .pin 19, .pin 127⟩ ⟨(9, 182), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 709, .pin 7, .pin 19, .pin 127⟩ ⟨(8, 213), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 2053, .pin 7, .pin 19, .pin 127⟩ ⟨(13, 589), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 3541, .pin 7, .pin 19, .pin 127⟩ ⟨(2, 119), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 5113, .pin 7, .pin 19, .pin 127⟩ ⟨(2, 143), (223, 590), (209, 911), (26, 293)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g13 :
    (leafOK (.c7, .c19, .big) ⟨.pin 7789, .pin 7, .pin 19, .pin 127⟩ ⟨(4, 353), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 17293, .pin 7, .pin 19, .pin 127⟩ ⟨(2, 263), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 28057, .pin 7, .pin 19, .pin 127⟩ ⟨(2, 335), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 19, .pin 127⟩ ⟨(1, 5), (223, 590), (209, 911), (26, 293)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 151⟩ ⟨(109, 393), (223, 590), (209, 911), (59, 725)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g14 :
    (leafOK (.c7, .c19, .big) ⟨.pin 13, .pin 7, .pin 19, .pin 307⟩ ⟨(109, 393), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 37, .pin 7, .pin 19, .pin 307⟩ ⟨(145, 882), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 61, .pin 7, .pin 19, .pin 307⟩ ⟨(79, 617), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 73, .pin 7, .pin 19, .pin 307⟩ ⟨(57, 487), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 109, .pin 7, .pin 19, .pin 307⟩ ⟨(25, 261), (223, 590), (209, 911), (48, 841)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g15 :
    (leafOK (.c7, .c19, .big) ⟨.pin 409, .pin 7, .pin 19, .pin 307⟩ ⟨(9, 182), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 709, .pin 7, .pin 19, .pin 307⟩ ⟨(8, 213), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 2053, .pin 7, .pin 19, .pin 307⟩ ⟨(13, 589), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 3541, .pin 7, .pin 19, .pin 307⟩ ⟨(2, 119), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 5113, .pin 7, .pin 19, .pin 307⟩ ⟨(2, 143), (223, 590), (209, 911), (48, 841)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g16 :
    (leafOK (.c7, .c19, .big) ⟨.pin 7789, .pin 7, .pin 19, .pin 307⟩ ⟨(4, 353), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 17293, .pin 7, .pin 19, .pin 307⟩ ⟨(2, 263), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 28057, .pin 7, .pin 19, .pin 307⟩ ⟨(2, 335), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 19, .pin 307⟩ ⟨(1, 5), (223, 590), (209, 911), (48, 841)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 367⟩ ⟨(109, 393), (223, 590), (209, 911), (51, 977)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g17 :
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 409⟩ ⟨(109, 393), (223, 590), (209, 911), (9, 182)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 709⟩ ⟨(109, 393), (223, 590), (209, 911), (8, 213)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 727⟩ ⟨(109, 393), (223, 590), (209, 911), (26, 701)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 991⟩ ⟨(109, 393), (223, 590), (209, 911), (25, 787)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 1087⟩ ⟨(109, 393), (223, 590), (209, 911), (30, 989)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g18 :
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 1723⟩ ⟨(109, 393), (223, 590), (209, 911), (2, 83)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 2053⟩ ⟨(109, 393), (223, 590), (209, 911), (13, 589)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 3019⟩ ⟨(109, 393), (223, 590), (209, 911), (18, 989)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 3541⟩ ⟨(109, 393), (223, 590), (209, 911), (2, 119)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 4603⟩ ⟨(109, 393), (223, 590), (209, 911), (6, 407)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g19 :
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 5113⟩ ⟨(109, 393), (223, 590), (209, 911), (2, 143)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 7789⟩ ⟨(109, 393), (223, 590), (209, 911), (4, 353)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 8011⟩ ⟨(109, 393), (223, 590), (209, 911), (2, 179)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 10303⟩ ⟨(109, 393), (223, 590), (209, 911), (2, 203)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 17293⟩ ⟨(109, 393), (223, 590), (209, 911), (2, 263)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g20 :
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 28057⟩ ⟨(109, 393), (223, 590), (209, 911), (2, 335)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 30103⟩ ⟨(109, 393), (223, 590), (209, 911), (2, 347)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 86143⟩ ⟨(109, 393), (223, 590), (209, 911), (2, 587)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 13, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(109, 393), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 37, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(145, 882), (223, 590), (209, 911), (1, 8)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g21 :
    (leafOK (.c7, .c19, .big) ⟨.pin 61, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(79, 617), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 73, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(57, 487), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 109, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(25, 261), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 409, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(9, 182), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 709, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(8, 213), (223, 590), (209, 911), (1, 8)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g22 :
    (leafOK (.c7, .c19, .big) ⟨.pin 2053, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(13, 589), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 3541, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(2, 119), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 5113, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(2, 143), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 7789, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(4, 353), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.pin 17293, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(2, 263), (223, 590), (209, 911), (1, 8)⟩))))) = true := by
  decide +kernel

private theorem u40_0_g23 :
    (leafOK (.c7, .c19, .big) ⟨.pin 28057, .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(2, 335), (223, 590), (209, 911), (1, 8)⟩ &&
    (leafOK (.c7, .c19, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 2053, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 19, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 3019, 2053, 1723, 1087, 991, 727, 709, 409, 367, 307, 151, 127, 109, 79, 73, 67, 61]⟩ ⟨(1, 5), (223, 590), (209, 911), (1, 8)⟩)) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 19, big)`, with 117 leaves. -/
def u40_0 : Tree :=
  .split 3 61
    (.split 0 13
      (.leaf ⟨(109, 393), (223, 590), (209, 911), (79, 617)⟩)
      (.split 0 37
        (.leaf ⟨(145, 882), (223, 590), (209, 911), (79, 617)⟩)
        (.split 0 73
          (.leaf ⟨(57, 487), (223, 590), (209, 911), (79, 617)⟩)
          (.split 0 109
            (.leaf ⟨(25, 261), (223, 590), (209, 911), (79, 617)⟩)
            (.split 0 409
              (.leaf ⟨(9, 182), (223, 590), (209, 911), (79, 617)⟩)
              (.split 0 709
                (.leaf ⟨(8, 213), (223, 590), (209, 911), (79, 617)⟩)
                (.split 0 2053
                  (.leaf ⟨(13, 589), (223, 590), (209, 911), (79, 617)⟩)
                  (.split 0 3541
                    (.leaf ⟨(2, 119), (223, 590), (209, 911), (79, 617)⟩)
                    (.split 0 5113
                      (.leaf ⟨(2, 143), (223, 590), (209, 911), (79, 617)⟩)
                      (.split 0 7789
                        (.leaf ⟨(4, 353), (223, 590), (209, 911), (79, 617)⟩)
                        (.split 0 17293
                          (.leaf ⟨(2, 263), (223, 590), (209, 911), (79, 617)⟩)
                          (.split 0 28057
                            (.leaf ⟨(2, 335), (223, 590), (209, 911), (79, 617)⟩)
                            (.leaf ⟨(1, 5), (223, 590), (209, 911), (79, 617)⟩)))))))))))))
    (.split 3 67
      (.split 0 13
        (.leaf ⟨(109, 393), (223, 590), (209, 911), (27, 221)⟩)
        (.split 0 37
          (.leaf ⟨(145, 882), (223, 590), (209, 911), (27, 221)⟩)
          (.split 0 61
            (.leaf ⟨(79, 617), (223, 590), (209, 911), (27, 221)⟩)
            (.split 0 73
              (.leaf ⟨(57, 487), (223, 590), (209, 911), (27, 221)⟩)
              (.split 0 109
                (.leaf ⟨(25, 261), (223, 590), (209, 911), (27, 221)⟩)
                (.split 0 409
                  (.leaf ⟨(9, 182), (223, 590), (209, 911), (27, 221)⟩)
                  (.split 0 709
                    (.leaf ⟨(8, 213), (223, 590), (209, 911), (27, 221)⟩)
                    (.split 0 2053
                      (.leaf ⟨(13, 589), (223, 590), (209, 911), (27, 221)⟩)
                      (.split 0 3541
                        (.leaf ⟨(2, 119), (223, 590), (209, 911), (27, 221)⟩)
                        (.split 0 5113
                          (.leaf ⟨(2, 143), (223, 590), (209, 911), (27, 221)⟩)
                          (.split 0 7789
                            (.leaf ⟨(4, 353), (223, 590), (209, 911), (27, 221)⟩)
                            (.split 0 17293
                              (.leaf ⟨(2, 263), (223, 590), (209, 911), (27, 221)⟩)
                              (.split 0 28057
                                (.leaf ⟨(2, 335), (223, 590), (209, 911), (27, 221)⟩)
                                (.leaf ⟨(1, 5), (223, 590), (209, 911), (27, 221)⟩))))))))))))))
      (.split 3 73
        (.split 0 13
          (.leaf ⟨(109, 393), (223, 590), (209, 911), (57, 487)⟩)
          (.split 0 37
            (.leaf ⟨(145, 882), (223, 590), (209, 911), (57, 487)⟩)
            (.split 0 61
              (.leaf ⟨(79, 617), (223, 590), (209, 911), (57, 487)⟩)
              (.split 0 109
                (.leaf ⟨(25, 261), (223, 590), (209, 911), (57, 487)⟩)
                (.split 0 409
                  (.leaf ⟨(9, 182), (223, 590), (209, 911), (57, 487)⟩)
                  (.split 0 709
                    (.leaf ⟨(8, 213), (223, 590), (209, 911), (57, 487)⟩)
                    (.split 0 2053
                      (.leaf ⟨(13, 589), (223, 590), (209, 911), (57, 487)⟩)
                      (.split 0 3541
                        (.leaf ⟨(2, 119), (223, 590), (209, 911), (57, 487)⟩)
                        (.split 0 5113
                          (.leaf ⟨(2, 143), (223, 590), (209, 911), (57, 487)⟩)
                          (.split 0 7789
                            (.leaf ⟨(4, 353), (223, 590), (209, 911), (57, 487)⟩)
                            (.split 0 17293
                              (.leaf ⟨(2, 263), (223, 590), (209, 911), (57, 487)⟩)
                              (.split 0 28057
                                (.leaf ⟨(2, 335), (223, 590), (209, 911), (57, 487)⟩)
                                (.leaf ⟨(1, 5), (223, 590), (209, 911), (57, 487)⟩)))))))))))))
        (.split 3 79
          (.split 0 13
            (.leaf ⟨(109, 393), (223, 590), (209, 911), (107, 951)⟩)
            (.split 0 37
              (.leaf ⟨(145, 882), (223, 590), (209, 911), (107, 951)⟩)
              (.split 0 61
                (.leaf ⟨(79, 617), (223, 590), (209, 911), (107, 951)⟩)
                (.split 0 73
                  (.leaf ⟨(57, 487), (223, 590), (209, 911), (107, 951)⟩)
                  (.split 0 109
                    (.leaf ⟨(25, 261), (223, 590), (209, 911), (107, 951)⟩)
                    (.split 0 409
                      (.leaf ⟨(9, 182), (223, 590), (209, 911), (107, 951)⟩)
                      (.split 0 709
                        (.leaf ⟨(8, 213), (223, 590), (209, 911), (107, 951)⟩)
                        (.split 0 2053
                          (.leaf ⟨(13, 589), (223, 590), (209, 911), (107, 951)⟩)
                          (.split 0 3541
                            (.leaf ⟨(2, 119), (223, 590), (209, 911), (107, 951)⟩)
                            (.split 0 5113
                              (.leaf ⟨(2, 143), (223, 590), (209, 911), (107, 951)⟩)
                              (.split 0 7789
                                (.leaf ⟨(4, 353), (223, 590), (209, 911), (107, 951)⟩)
                                (.split 0 17293
                                  (.leaf ⟨(2, 263), (223, 590), (209, 911), (107, 951)⟩)
                                  (.split 0 28057
                                    (.leaf ⟨(2, 335), (223, 590), (209, 911), (107, 951)⟩)
                                    (.leaf ⟨(1, 5), (223, 590), (209, 911), (107, 951)⟩))))))))))))))
          (.split 3 109
            (.leaf ⟨(109, 393), (223, 590), (209, 911), (25, 261)⟩)
            (.split 3 127
              (.split 0 13
                (.leaf ⟨(109, 393), (223, 590), (209, 911), (26, 293)⟩)
                (.split 0 37
                  (.leaf ⟨(145, 882), (223, 590), (209, 911), (26, 293)⟩)
                  (.split 0 61
                    (.leaf ⟨(79, 617), (223, 590), (209, 911), (26, 293)⟩)
                    (.split 0 73
                      (.leaf ⟨(57, 487), (223, 590), (209, 911), (26, 293)⟩)
                      (.split 0 109
                        (.leaf ⟨(25, 261), (223, 590), (209, 911), (26, 293)⟩)
                        (.split 0 409
                          (.leaf ⟨(9, 182), (223, 590), (209, 911), (26, 293)⟩)
                          (.split 0 709
                            (.leaf ⟨(8, 213), (223, 590), (209, 911), (26, 293)⟩)
                            (.split 0 2053
                              (.leaf ⟨(13, 589), (223, 590), (209, 911), (26, 293)⟩)
                              (.split 0 3541
                                (.leaf ⟨(2, 119), (223, 590), (209, 911), (26, 293)⟩)
                                (.split 0 5113
                                  (.leaf ⟨(2, 143), (223, 590), (209, 911), (26, 293)⟩)
                                  (.split 0 7789
                                    (.leaf ⟨(4, 353), (223, 590), (209, 911), (26, 293)⟩)
                                    (.split 0 17293
                                      (.leaf ⟨(2, 263), (223, 590), (209, 911), (26, 293)⟩)
                                      (.split 0 28057
                                        (.leaf ⟨(2, 335), (223, 590), (209, 911), (26, 293)⟩)
                                        (.leaf ⟨(1, 5), (223, 590), (209, 911), (26, 293)⟩))))))))))))))
              (.split 3 151
                (.leaf ⟨(109, 393), (223, 590), (209, 911), (59, 725)⟩)
                (.split 3 307
                  (.split 0 13
                    (.leaf ⟨(109, 393), (223, 590), (209, 911), (48, 841)⟩)
                    (.split 0 37
                      (.leaf ⟨(145, 882), (223, 590), (209, 911), (48, 841)⟩)
                      (.split 0 61
                        (.leaf ⟨(79, 617), (223, 590), (209, 911), (48, 841)⟩)
                        (.split 0 73
                          (.leaf ⟨(57, 487), (223, 590), (209, 911), (48, 841)⟩)
                          (.split 0 109
                            (.leaf ⟨(25, 261), (223, 590), (209, 911), (48, 841)⟩)
                            (.split 0 409
                              (.leaf ⟨(9, 182), (223, 590), (209, 911), (48, 841)⟩)
                              (.split 0 709
                                (.leaf ⟨(8, 213), (223, 590), (209, 911), (48, 841)⟩)
                                (.split 0 2053
                                  (.leaf ⟨(13, 589), (223, 590), (209, 911), (48, 841)⟩)
                                  (.split 0 3541
                                    (.leaf ⟨(2, 119), (223, 590), (209, 911), (48, 841)⟩)
                                    (.split 0 5113
                                      (.leaf ⟨(2, 143), (223, 590), (209, 911), (48, 841)⟩)
                                      (.split 0 7789
                                        (.leaf ⟨(4, 353), (223, 590), (209, 911), (48, 841)⟩)
                                        (.split 0 17293
                                          (.leaf ⟨(2, 263), (223, 590), (209, 911), (48, 841)⟩)
                                          (.split 0 28057
                                            (.leaf ⟨(2, 335), (223, 590), (209, 911), (48, 841)⟩)
                                            (.leaf ⟨(1, 5), (223, 590), (209, 911), (48, 841)⟩))))))))))))))
                  (.split 3 367
                    (.leaf ⟨(109, 393), (223, 590), (209, 911), (51, 977)⟩)
                    (.split 3 409
                      (.leaf ⟨(109, 393), (223, 590), (209, 911), (9, 182)⟩)
                      (.split 3 709
                        (.leaf ⟨(109, 393), (223, 590), (209, 911), (8, 213)⟩)
                        (.split 3 727
                          (.leaf ⟨(109, 393), (223, 590), (209, 911), (26, 701)⟩)
                          (.split 3 991
                            (.leaf ⟨(109, 393), (223, 590), (209, 911), (25, 787)⟩)
                            (.split 3 1087
                              (.leaf ⟨(109, 393), (223, 590), (209, 911), (30, 989)⟩)
                              (.split 3 1723
                                (.leaf ⟨(109, 393), (223, 590), (209, 911), (2, 83)⟩)
                                (.split 3 2053
                                  (.leaf ⟨(109, 393), (223, 590), (209, 911), (13, 589)⟩)
                                  (.split 3 3019
                                    (.leaf ⟨(109, 393), (223, 590), (209, 911), (18, 989)⟩)
                                    (.split 3 3541
                                      (.leaf ⟨(109, 393), (223, 590), (209, 911), (2, 119)⟩)
                                      (.split 3 4603
                                        (.leaf ⟨(109, 393), (223, 590), (209, 911), (6, 407)⟩)
                                        (.split 3 5113
                                          (.leaf ⟨(109, 393), (223, 590), (209, 911), (2, 143)⟩)
                                          (.split 3 7789
                                            (.leaf ⟨(109, 393), (223, 590), (209, 911), (4, 353)⟩)
                                            (.split 3 8011
                                              (.leaf ⟨(109, 393), (223, 590), (209, 911), (2, 179)⟩)
                                              (.split 3 10303
                                                (.leaf ⟨(109, 393), (223, 590), (209, 911), (2, 203)⟩)
                                                (.split 3 17293
                                                  (.leaf ⟨(109, 393), (223, 590), (209, 911), (2, 263)⟩)
                                                  (.split 3 28057
                                                    (.leaf ⟨(109, 393), (223, 590), (209, 911), (2, 335)⟩)
                                                    (.split 3 30103
                                                      (.leaf ⟨(109, 393), (223, 590), (209, 911), (2, 347)⟩)
                                                      (.split 3 86143
                                                        (.leaf ⟨(109, 393), (223, 590), (209, 911), (2, 587)⟩)
                                                        (.split 0 13
                                                          (.leaf ⟨(109, 393), (223, 590), (209, 911), (1, 8)⟩)
                                                          (.split 0 37
                                                            (.leaf ⟨(145, 882), (223, 590), (209, 911), (1, 8)⟩)
                                                            (.split 0 61
                                                              (.leaf ⟨(79, 617), (223, 590), (209, 911), (1, 8)⟩)
                                                              (.split 0 73
                                                                (.leaf ⟨(57, 487), (223, 590), (209, 911), (1, 8)⟩)
                                                                (.split 0 109
                                                                  (.leaf ⟨(25, 261), (223, 590), (209, 911), (1, 8)⟩)
                                                                  (.split 0 409
                                                                    (.leaf ⟨(9, 182), (223, 590), (209, 911), (1, 8)⟩)
                                                                    (.split 0 709
                                                                      (.leaf ⟨(8, 213), (223, 590), (209, 911), (1, 8)⟩)
                                                                      (.split 0 2053
                                                                        (.leaf ⟨(13, 589), (223, 590), (209, 911), (1, 8)⟩)
                                                                        (.split 0 3541
                                                                          (.leaf ⟨(2, 119), (223, 590), (209, 911), (1, 8)⟩)
                                                                          (.split 0 5113
                                                                            (.leaf ⟨(2, 143), (223, 590), (209, 911), (1, 8)⟩)
                                                                            (.split 0 7789
                                                                              (.leaf ⟨(4, 353), (223, 590), (209, 911), (1, 8)⟩)
                                                                              (.split 0 17293
                                                                                (.leaf ⟨(2, 263), (223, 590), (209, 911), (1, 8)⟩)
                                                                                (.split 0 28057
                                                                                  (.leaf ⟨(2, 335), (223, 590), (209, 911), (1, 8)⟩)
                                                                                  (.leaf ⟨(1, 5), (223, 590), (209, 911), (1, 8)⟩))))))))))))))))))))))))))))))))))))))))

/-- Subtree 0 of the class triple `(7, 19, big)` passes the check. -/
theorem u40_0_ok : treeOK (.c7, .c19, .big)
    (rootNode (.c7, .c19, .big)) u40_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g0).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g0).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g0).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g0).2).2).2).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g0).2).2).2).2)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g1).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g1).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g1).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g1).2).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g1).2).2).2).2)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g2).2).1)
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g2).2).2).1)))))))))))))
    (treeOK_split (by decide) rfl
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g2).2).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g2).2).2).2).2)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g3).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g3).2).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g3).2).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g3).2).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g3).2).2).2).2)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g4).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g4).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g4).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g4).2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g4).2).2).2).2)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g5).1)
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g5).2).1))))))))))))))
      (treeOK_split (by decide) rfl
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g5).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g5).2).2).2).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g5).2).2).2).2)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g6).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g6).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g6).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g6).2).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g6).2).2).2).2)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g7).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g7).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g7).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g7).2).2).2).1)
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g7).2).2).2).2)))))))))))))
        (treeOK_split (by decide) rfl
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g8).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g8).2).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g8).2).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g8).2).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g8).2).2).2).2)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g9).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g9).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g9).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g9).2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g9).2).2).2).2)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g10).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g10).2).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g10).2).2).1)
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g10).2).2).2).1))))))))))))))
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g10).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g11).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g11).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g11).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g11).2).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g11).2).2).2).2)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g12).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g12).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g12).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g12).2).2).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g12).2).2).2).2)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g13).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g13).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g13).2).2).1)
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g13).2).2).2).1))))))))))))))
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g13).2).2).2).2)
                (treeOK_split (by decide) rfl
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g14).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g14).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g14).2).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g14).2).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g14).2).2).2).2)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g15).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g15).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g15).2).2).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g15).2).2).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g15).2).2).2).2)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g16).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g16).2).1)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g16).2).2).1)
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g16).2).2).2).1))))))))))))))
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g16).2).2).2).2)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g17).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g17).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g17).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g17).2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g17).2).2).2).2)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g18).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g18).2).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g18).2).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g18).2).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g18).2).2).2).2)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g19).1)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g19).2).1)
                                            (treeOK_split (by decide) rfl
                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g19).2).2).1)
                                              (treeOK_split (by decide) rfl
                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g19).2).2).2).1)
                                                (treeOK_split (by decide) rfl
                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g19).2).2).2).2)
                                                  (treeOK_split (by decide) rfl
                                                    (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g20).1)
                                                    (treeOK_split (by decide) rfl
                                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g20).2).1)
                                                      (treeOK_split (by decide) rfl
                                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g20).2).2).1)
                                                        (treeOK_split (by decide) rfl
                                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g20).2).2).2).1)
                                                          (treeOK_split (by decide) rfl
                                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g20).2).2).2).2)
                                                            (treeOK_split (by decide) rfl
                                                              (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g21).1)
                                                              (treeOK_split (by decide) rfl
                                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g21).2).1)
                                                                (treeOK_split (by decide) rfl
                                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g21).2).2).1)
                                                                  (treeOK_split (by decide) rfl
                                                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g21).2).2).2).1)
                                                                    (treeOK_split (by decide) rfl
                                                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g21).2).2).2).2)
                                                                      (treeOK_split (by decide) rfl
                                                                        (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g22).1)
                                                                        (treeOK_split (by decide) rfl
                                                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g22).2).1)
                                                                          (treeOK_split (by decide) rfl
                                                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g22).2).2).1)
                                                                            (treeOK_split (by decide) rfl
                                                                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g22).2).2).2).1)
                                                                              (treeOK_split (by decide) rfl
                                                                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u40_0_g22).2).2).2).2)
                                                                                (treeOK_split (by decide) rfl
                                                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g23).1)
                                                                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u40_0_g23).2))))))))))))))))))))))))))))))))))))))))

private theorem u41_0_g0 :
    (leafOK (.c7, .c31, .c37) ⟨.pin 13, .pin 7, .pin 31, .pin 37⟩ ⟨(109, 393), (223, 590), (155, 863), (145, 882)⟩ &&
    (leafOK (.c7, .c31, .c37) ⟨.pin 61, .pin 7, .pin 31, .pin 37⟩ ⟨(79, 617), (223, 590), (155, 863), (145, 882)⟩ &&
    (leafOK (.c7, .c31, .c37) ⟨.pin 73, .pin 7, .pin 31, .pin 37⟩ ⟨(57, 487), (223, 590), (155, 863), (145, 882)⟩ &&
    (leafOK (.c7, .c31, .c37) ⟨.pin 109, .pin 7, .pin 31, .pin 37⟩ ⟨(25, 261), (223, 590), (155, 863), (145, 882)⟩ &&
    (leafOK (.c7, .c31, .c37) ⟨.pin 409, .pin 7, .pin 31, .pin 37⟩ ⟨(9, 182), (223, 590), (155, 863), (145, 882)⟩))))) = true := by
  decide +kernel

private theorem u41_0_g1 :
    (leafOK (.c7, .c31, .c37) ⟨.pin 709, .pin 7, .pin 31, .pin 37⟩ ⟨(8, 213), (223, 590), (155, 863), (145, 882)⟩ &&
    (leafOK (.c7, .c31, .c37) ⟨.pin 3541, .pin 7, .pin 31, .pin 37⟩ ⟨(2, 119), (223, 590), (155, 863), (145, 882)⟩ &&
    (leafOK (.c7, .c31, .c37) ⟨.pin 5113, .pin 7, .pin 31, .pin 37⟩ ⟨(2, 143), (223, 590), (155, 863), (145, 882)⟩ &&
    (leafOK (.c7, .c31, .c37) ⟨.pin 7789, .pin 7, .pin 31, .pin 37⟩ ⟨(4, 353), (223, 590), (155, 863), (145, 882)⟩ &&
    (leafOK (.c7, .c31, .c37) ⟨.pin 17293, .pin 7, .pin 31, .pin 37⟩ ⟨(2, 263), (223, 590), (155, 863), (145, 882)⟩))))) = true := by
  decide +kernel

private theorem u41_0_g2 :
    (leafOK (.c7, .c31, .c37) ⟨.pin 28057, .pin 7, .pin 31, .pin 37⟩ ⟨(2, 335), (223, 590), (155, 863), (145, 882)⟩ &&
    (leafOK (.c7, .c31, .c37) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 13], .pin 7, .pin 31, .pin 37⟩ ⟨(1, 5), (223, 590), (155, 863), (145, 882)⟩)) = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 31, 37)`, with 12 leaves. -/
def u41_0 : Tree :=
  .split 0 13
    (.leaf ⟨(109, 393), (223, 590), (155, 863), (145, 882)⟩)
    (.split 0 61
      (.leaf ⟨(79, 617), (223, 590), (155, 863), (145, 882)⟩)
      (.split 0 73
        (.leaf ⟨(57, 487), (223, 590), (155, 863), (145, 882)⟩)
        (.split 0 109
          (.leaf ⟨(25, 261), (223, 590), (155, 863), (145, 882)⟩)
          (.split 0 409
            (.leaf ⟨(9, 182), (223, 590), (155, 863), (145, 882)⟩)
            (.split 0 709
              (.leaf ⟨(8, 213), (223, 590), (155, 863), (145, 882)⟩)
              (.split 0 3541
                (.leaf ⟨(2, 119), (223, 590), (155, 863), (145, 882)⟩)
                (.split 0 5113
                  (.leaf ⟨(2, 143), (223, 590), (155, 863), (145, 882)⟩)
                  (.split 0 7789
                    (.leaf ⟨(4, 353), (223, 590), (155, 863), (145, 882)⟩)
                    (.split 0 17293
                      (.leaf ⟨(2, 263), (223, 590), (155, 863), (145, 882)⟩)
                      (.split 0 28057
                        (.leaf ⟨(2, 335), (223, 590), (155, 863), (145, 882)⟩)
                        (.leaf ⟨(1, 5), (223, 590), (155, 863), (145, 882)⟩)))))))))))

/-- Subtree 0 of the class triple `(7, 31, 37)` passes the check. -/
theorem u41_0_ok : treeOK (.c7, .c31, .c37)
    (rootNode (.c7, .c31, .c37)) u41_0 = true :=
  treeOK_split (by decide) rfl
    (treeOK_leaf (Bool.and_eq_true_iff.mp u41_0_g0).1)
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u41_0_g0).2).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u41_0_g0).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u41_0_g0).2).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u41_0_g0).2).2).2).2)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u41_0_g1).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u41_0_g1).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u41_0_g1).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u41_0_g1).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u41_0_g1).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u41_0_g2).1)
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u41_0_g2).2)))))))))))

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u40_0_ok
#print axioms OddPerfect.ThreeFreeThree.u41_0_ok
