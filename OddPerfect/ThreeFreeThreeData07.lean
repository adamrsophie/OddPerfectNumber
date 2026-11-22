import OddPerfect.ThreeFreeThreeChecker

/-!
# Data for three exceptional primes, part 7

Subtrees of the case analysis certificate for the class triples `(7, 31, big)` (part),
`(7, 37, 43)`, `(7, 37, n2)`, with 128 leaves in all. Each public theorem states that a
subtree passes `treeOK` from explicit constraints. The data was found by a search
outside Lean; everything in this file is rechecked by the kernel through `decide
+kernel` on the leaf checks.
-/

namespace OddPerfect

namespace ThreeFreeThree

private theorem u44_16_g0 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 4603⟩ ⟨(109, 393), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 4603⟩ ⟨(145, 882), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 4603⟩ ⟨(79, 617), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 4603⟩ ⟨(57, 487), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 4603⟩ ⟨(25, 261), (223, 590), (155, 863), (6, 407)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g1 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 4603⟩ ⟨(9, 182), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 4603⟩ ⟨(8, 213), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 4603⟩ ⟨(2, 119), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 4603⟩ ⟨(2, 143), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 4603⟩ ⟨(4, 353), (223, 590), (155, 863), (6, 407)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g2 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 4603⟩ ⟨(2, 263), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 4603⟩ ⟨(2, 335), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 4603⟩ ⟨(1, 5), (223, 590), (155, 863), (6, 407)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 5113⟩ ⟨(109, 393), (223, 590), (155, 863), (2, 143)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 5113⟩ ⟨(145, 882), (223, 590), (155, 863), (2, 143)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g3 :
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 5113⟩ ⟨(79, 617), (223, 590), (155, 863), (2, 143)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 5113⟩ ⟨(57, 487), (223, 590), (155, 863), (2, 143)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 5113⟩ ⟨(25, 261), (223, 590), (155, 863), (2, 143)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 5113⟩ ⟨(9, 182), (223, 590), (155, 863), (2, 143)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 5113⟩ ⟨(8, 213), (223, 590), (155, 863), (2, 143)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g4 :
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 5113⟩ ⟨(2, 119), (223, 590), (155, 863), (2, 143)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 5113⟩ ⟨(4, 353), (223, 590), (155, 863), (2, 143)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 5113⟩ ⟨(2, 263), (223, 590), (155, 863), (2, 143)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 5113⟩ ⟨(2, 335), (223, 590), (155, 863), (2, 143)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 5113⟩ ⟨(1, 5), (223, 590), (155, 863), (2, 143)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g5 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 7789⟩ ⟨(109, 393), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 7789⟩ ⟨(145, 882), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 7789⟩ ⟨(79, 617), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 7789⟩ ⟨(57, 487), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 7789⟩ ⟨(25, 261), (223, 590), (155, 863), (4, 353)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g6 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 7789⟩ ⟨(9, 182), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 7789⟩ ⟨(8, 213), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 7789⟩ ⟨(2, 119), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 7789⟩ ⟨(2, 143), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 7789⟩ ⟨(2, 263), (223, 590), (155, 863), (4, 353)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g7 :
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 7789⟩ ⟨(2, 335), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 7789⟩ ⟨(1, 5), (223, 590), (155, 863), (4, 353)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 8011⟩ ⟨(109, 393), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 8011⟩ ⟨(145, 882), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 8011⟩ ⟨(79, 617), (223, 590), (155, 863), (2, 179)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g8 :
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 8011⟩ ⟨(57, 487), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 8011⟩ ⟨(25, 261), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 8011⟩ ⟨(9, 182), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 8011⟩ ⟨(8, 213), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 8011⟩ ⟨(2, 119), (223, 590), (155, 863), (2, 179)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g9 :
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 8011⟩ ⟨(2, 143), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 8011⟩ ⟨(4, 353), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 8011⟩ ⟨(2, 263), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 8011⟩ ⟨(2, 335), (223, 590), (155, 863), (2, 179)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 8011⟩ ⟨(1, 5), (223, 590), (155, 863), (2, 179)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g10 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 10303⟩ ⟨(109, 393), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 10303⟩ ⟨(145, 882), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 10303⟩ ⟨(79, 617), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 10303⟩ ⟨(57, 487), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 10303⟩ ⟨(25, 261), (223, 590), (155, 863), (2, 203)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g11 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 10303⟩ ⟨(9, 182), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 10303⟩ ⟨(8, 213), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 10303⟩ ⟨(2, 119), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 10303⟩ ⟨(2, 143), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 10303⟩ ⟨(4, 353), (223, 590), (155, 863), (2, 203)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g12 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 10303⟩ ⟨(2, 263), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 10303⟩ ⟨(2, 335), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 10303⟩ ⟨(1, 5), (223, 590), (155, 863), (2, 203)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 17293⟩ ⟨(109, 393), (223, 590), (155, 863), (2, 263)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 17293⟩ ⟨(145, 882), (223, 590), (155, 863), (2, 263)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g13 :
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 17293⟩ ⟨(79, 617), (223, 590), (155, 863), (2, 263)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 17293⟩ ⟨(57, 487), (223, 590), (155, 863), (2, 263)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 17293⟩ ⟨(25, 261), (223, 590), (155, 863), (2, 263)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 17293⟩ ⟨(9, 182), (223, 590), (155, 863), (2, 263)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 17293⟩ ⟨(8, 213), (223, 590), (155, 863), (2, 263)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g14 :
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 17293⟩ ⟨(2, 119), (223, 590), (155, 863), (2, 263)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 17293⟩ ⟨(2, 143), (223, 590), (155, 863), (2, 263)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 17293⟩ ⟨(4, 353), (223, 590), (155, 863), (2, 263)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 17293⟩ ⟨(2, 335), (223, 590), (155, 863), (2, 263)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 17293⟩ ⟨(1, 5), (223, 590), (155, 863), (2, 263)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g15 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 28057⟩ ⟨(109, 393), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 28057⟩ ⟨(145, 882), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 28057⟩ ⟨(79, 617), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 28057⟩ ⟨(57, 487), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 28057⟩ ⟨(25, 261), (223, 590), (155, 863), (2, 335)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g16 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 28057⟩ ⟨(9, 182), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 28057⟩ ⟨(8, 213), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 28057⟩ ⟨(2, 119), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 28057⟩ ⟨(2, 143), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 28057⟩ ⟨(4, 353), (223, 590), (155, 863), (2, 335)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g17 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 28057⟩ ⟨(2, 263), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 28057⟩ ⟨(1, 5), (223, 590), (155, 863), (2, 335)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 30103⟩ ⟨(109, 393), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 30103⟩ ⟨(145, 882), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 30103⟩ ⟨(79, 617), (223, 590), (155, 863), (2, 347)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g18 :
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 30103⟩ ⟨(57, 487), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 30103⟩ ⟨(25, 261), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 30103⟩ ⟨(9, 182), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 30103⟩ ⟨(8, 213), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 30103⟩ ⟨(2, 119), (223, 590), (155, 863), (2, 347)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g19 :
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 30103⟩ ⟨(2, 143), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 30103⟩ ⟨(4, 353), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 30103⟩ ⟨(2, 263), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 30103⟩ ⟨(2, 335), (223, 590), (155, 863), (2, 347)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 30103⟩ ⟨(1, 5), (223, 590), (155, 863), (2, 347)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g20 :
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .pin 86143⟩ ⟨(109, 393), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .pin 86143⟩ ⟨(145, 882), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .pin 86143⟩ ⟨(79, 617), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .pin 86143⟩ ⟨(57, 487), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .pin 86143⟩ ⟨(25, 261), (223, 590), (155, 863), (2, 587)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g21 :
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .pin 86143⟩ ⟨(9, 182), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .pin 86143⟩ ⟨(8, 213), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .pin 86143⟩ ⟨(2, 119), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .pin 86143⟩ ⟨(2, 143), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .pin 86143⟩ ⟨(4, 353), (223, 590), (155, 863), (2, 587)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g22 :
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .pin 86143⟩ ⟨(2, 263), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .pin 86143⟩ ⟨(2, 335), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .pin 86143⟩ ⟨(1, 5), (223, 590), (155, 863), (2, 587)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 13, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(109, 393), (223, 590), (155, 863), (1, 8)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 37, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(145, 882), (223, 590), (155, 863), (1, 8)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g23 :
    (leafOK (.c7, .c31, .big) ⟨.pin 61, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(79, 617), (223, 590), (155, 863), (1, 8)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 73, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(57, 487), (223, 590), (155, 863), (1, 8)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 109, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(25, 261), (223, 590), (155, 863), (1, 8)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 409, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(9, 182), (223, 590), (155, 863), (1, 8)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 709, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(8, 213), (223, 590), (155, 863), (1, 8)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g24 :
    (leafOK (.c7, .c31, .big) ⟨.pin 3541, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(2, 119), (223, 590), (155, 863), (1, 8)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 5113, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(2, 143), (223, 590), (155, 863), (1, 8)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 7789, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(4, 353), (223, 590), (155, 863), (1, 8)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 17293, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(2, 263), (223, 590), (155, 863), (1, 8)⟩ &&
    (leafOK (.c7, .c31, .big) ⟨.pin 28057, .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(2, 335), (223, 590), (155, 863), (1, 8)⟩))))) = true := by
  decide +kernel

private theorem u44_16_g25 :
    leafOK (.c7, .c31, .big) ⟨.free .q 13 [28057, 17293, 7789, 5113, 3541, 709, 409, 109, 73, 61, 37, 13], .pin 7, .pin 31, .free .big 61 [86143, 30103, 28057, 17293, 10303, 8011, 7789, 5113, 4603, 3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ ⟨(1, 5), (223, 590), (155, 863), (1, 8)⟩ = true := by
  decide +kernel

/-- Subtree 16 of the class triple `(7, 31, big)`, with 126 leaves. -/
def u44_16 : Tree :=
  .split 3 4603
    (.split 0 13
      (.leaf ⟨(109, 393), (223, 590), (155, 863), (6, 407)⟩)
      (.split 0 37
        (.leaf ⟨(145, 882), (223, 590), (155, 863), (6, 407)⟩)
        (.split 0 61
          (.leaf ⟨(79, 617), (223, 590), (155, 863), (6, 407)⟩)
          (.split 0 73
            (.leaf ⟨(57, 487), (223, 590), (155, 863), (6, 407)⟩)
            (.split 0 109
              (.leaf ⟨(25, 261), (223, 590), (155, 863), (6, 407)⟩)
              (.split 0 409
                (.leaf ⟨(9, 182), (223, 590), (155, 863), (6, 407)⟩)
                (.split 0 709
                  (.leaf ⟨(8, 213), (223, 590), (155, 863), (6, 407)⟩)
                  (.split 0 3541
                    (.leaf ⟨(2, 119), (223, 590), (155, 863), (6, 407)⟩)
                    (.split 0 5113
                      (.leaf ⟨(2, 143), (223, 590), (155, 863), (6, 407)⟩)
                      (.split 0 7789
                        (.leaf ⟨(4, 353), (223, 590), (155, 863), (6, 407)⟩)
                        (.split 0 17293
                          (.leaf ⟨(2, 263), (223, 590), (155, 863), (6, 407)⟩)
                          (.split 0 28057
                            (.leaf ⟨(2, 335), (223, 590), (155, 863), (6, 407)⟩)
                            (.leaf ⟨(1, 5), (223, 590), (155, 863), (6, 407)⟩)))))))))))))
    (.split 3 5113
      (.split 0 13
        (.leaf ⟨(109, 393), (223, 590), (155, 863), (2, 143)⟩)
        (.split 0 37
          (.leaf ⟨(145, 882), (223, 590), (155, 863), (2, 143)⟩)
          (.split 0 61
            (.leaf ⟨(79, 617), (223, 590), (155, 863), (2, 143)⟩)
            (.split 0 73
              (.leaf ⟨(57, 487), (223, 590), (155, 863), (2, 143)⟩)
              (.split 0 109
                (.leaf ⟨(25, 261), (223, 590), (155, 863), (2, 143)⟩)
                (.split 0 409
                  (.leaf ⟨(9, 182), (223, 590), (155, 863), (2, 143)⟩)
                  (.split 0 709
                    (.leaf ⟨(8, 213), (223, 590), (155, 863), (2, 143)⟩)
                    (.split 0 3541
                      (.leaf ⟨(2, 119), (223, 590), (155, 863), (2, 143)⟩)
                      (.split 0 7789
                        (.leaf ⟨(4, 353), (223, 590), (155, 863), (2, 143)⟩)
                        (.split 0 17293
                          (.leaf ⟨(2, 263), (223, 590), (155, 863), (2, 143)⟩)
                          (.split 0 28057
                            (.leaf ⟨(2, 335), (223, 590), (155, 863), (2, 143)⟩)
                            (.leaf ⟨(1, 5), (223, 590), (155, 863), (2, 143)⟩))))))))))))
      (.split 3 7789
        (.split 0 13
          (.leaf ⟨(109, 393), (223, 590), (155, 863), (4, 353)⟩)
          (.split 0 37
            (.leaf ⟨(145, 882), (223, 590), (155, 863), (4, 353)⟩)
            (.split 0 61
              (.leaf ⟨(79, 617), (223, 590), (155, 863), (4, 353)⟩)
              (.split 0 73
                (.leaf ⟨(57, 487), (223, 590), (155, 863), (4, 353)⟩)
                (.split 0 109
                  (.leaf ⟨(25, 261), (223, 590), (155, 863), (4, 353)⟩)
                  (.split 0 409
                    (.leaf ⟨(9, 182), (223, 590), (155, 863), (4, 353)⟩)
                    (.split 0 709
                      (.leaf ⟨(8, 213), (223, 590), (155, 863), (4, 353)⟩)
                      (.split 0 3541
                        (.leaf ⟨(2, 119), (223, 590), (155, 863), (4, 353)⟩)
                        (.split 0 5113
                          (.leaf ⟨(2, 143), (223, 590), (155, 863), (4, 353)⟩)
                          (.split 0 17293
                            (.leaf ⟨(2, 263), (223, 590), (155, 863), (4, 353)⟩)
                            (.split 0 28057
                              (.leaf ⟨(2, 335), (223, 590), (155, 863), (4, 353)⟩)
                              (.leaf ⟨(1, 5), (223, 590), (155, 863), (4, 353)⟩))))))))))))
        (.split 3 8011
          (.split 0 13
            (.leaf ⟨(109, 393), (223, 590), (155, 863), (2, 179)⟩)
            (.split 0 37
              (.leaf ⟨(145, 882), (223, 590), (155, 863), (2, 179)⟩)
              (.split 0 61
                (.leaf ⟨(79, 617), (223, 590), (155, 863), (2, 179)⟩)
                (.split 0 73
                  (.leaf ⟨(57, 487), (223, 590), (155, 863), (2, 179)⟩)
                  (.split 0 109
                    (.leaf ⟨(25, 261), (223, 590), (155, 863), (2, 179)⟩)
                    (.split 0 409
                      (.leaf ⟨(9, 182), (223, 590), (155, 863), (2, 179)⟩)
                      (.split 0 709
                        (.leaf ⟨(8, 213), (223, 590), (155, 863), (2, 179)⟩)
                        (.split 0 3541
                          (.leaf ⟨(2, 119), (223, 590), (155, 863), (2, 179)⟩)
                          (.split 0 5113
                            (.leaf ⟨(2, 143), (223, 590), (155, 863), (2, 179)⟩)
                            (.split 0 7789
                              (.leaf ⟨(4, 353), (223, 590), (155, 863), (2, 179)⟩)
                              (.split 0 17293
                                (.leaf ⟨(2, 263), (223, 590), (155, 863), (2, 179)⟩)
                                (.split 0 28057
                                  (.leaf ⟨(2, 335), (223, 590), (155, 863), (2, 179)⟩)
                                  (.leaf ⟨(1, 5), (223, 590), (155, 863), (2, 179)⟩)))))))))))))
          (.split 3 10303
            (.split 0 13
              (.leaf ⟨(109, 393), (223, 590), (155, 863), (2, 203)⟩)
              (.split 0 37
                (.leaf ⟨(145, 882), (223, 590), (155, 863), (2, 203)⟩)
                (.split 0 61
                  (.leaf ⟨(79, 617), (223, 590), (155, 863), (2, 203)⟩)
                  (.split 0 73
                    (.leaf ⟨(57, 487), (223, 590), (155, 863), (2, 203)⟩)
                    (.split 0 109
                      (.leaf ⟨(25, 261), (223, 590), (155, 863), (2, 203)⟩)
                      (.split 0 409
                        (.leaf ⟨(9, 182), (223, 590), (155, 863), (2, 203)⟩)
                        (.split 0 709
                          (.leaf ⟨(8, 213), (223, 590), (155, 863), (2, 203)⟩)
                          (.split 0 3541
                            (.leaf ⟨(2, 119), (223, 590), (155, 863), (2, 203)⟩)
                            (.split 0 5113
                              (.leaf ⟨(2, 143), (223, 590), (155, 863), (2, 203)⟩)
                              (.split 0 7789
                                (.leaf ⟨(4, 353), (223, 590), (155, 863), (2, 203)⟩)
                                (.split 0 17293
                                  (.leaf ⟨(2, 263), (223, 590), (155, 863), (2, 203)⟩)
                                  (.split 0 28057
                                    (.leaf ⟨(2, 335), (223, 590), (155, 863), (2, 203)⟩)
                                    (.leaf ⟨(1, 5), (223, 590), (155, 863), (2, 203)⟩)))))))))))))
            (.split 3 17293
              (.split 0 13
                (.leaf ⟨(109, 393), (223, 590), (155, 863), (2, 263)⟩)
                (.split 0 37
                  (.leaf ⟨(145, 882), (223, 590), (155, 863), (2, 263)⟩)
                  (.split 0 61
                    (.leaf ⟨(79, 617), (223, 590), (155, 863), (2, 263)⟩)
                    (.split 0 73
                      (.leaf ⟨(57, 487), (223, 590), (155, 863), (2, 263)⟩)
                      (.split 0 109
                        (.leaf ⟨(25, 261), (223, 590), (155, 863), (2, 263)⟩)
                        (.split 0 409
                          (.leaf ⟨(9, 182), (223, 590), (155, 863), (2, 263)⟩)
                          (.split 0 709
                            (.leaf ⟨(8, 213), (223, 590), (155, 863), (2, 263)⟩)
                            (.split 0 3541
                              (.leaf ⟨(2, 119), (223, 590), (155, 863), (2, 263)⟩)
                              (.split 0 5113
                                (.leaf ⟨(2, 143), (223, 590), (155, 863), (2, 263)⟩)
                                (.split 0 7789
                                  (.leaf ⟨(4, 353), (223, 590), (155, 863), (2, 263)⟩)
                                  (.split 0 28057
                                    (.leaf ⟨(2, 335), (223, 590), (155, 863), (2, 263)⟩)
                                    (.leaf ⟨(1, 5), (223, 590), (155, 863), (2, 263)⟩))))))))))))
              (.split 3 28057
                (.split 0 13
                  (.leaf ⟨(109, 393), (223, 590), (155, 863), (2, 335)⟩)
                  (.split 0 37
                    (.leaf ⟨(145, 882), (223, 590), (155, 863), (2, 335)⟩)
                    (.split 0 61
                      (.leaf ⟨(79, 617), (223, 590), (155, 863), (2, 335)⟩)
                      (.split 0 73
                        (.leaf ⟨(57, 487), (223, 590), (155, 863), (2, 335)⟩)
                        (.split 0 109
                          (.leaf ⟨(25, 261), (223, 590), (155, 863), (2, 335)⟩)
                          (.split 0 409
                            (.leaf ⟨(9, 182), (223, 590), (155, 863), (2, 335)⟩)
                            (.split 0 709
                              (.leaf ⟨(8, 213), (223, 590), (155, 863), (2, 335)⟩)
                              (.split 0 3541
                                (.leaf ⟨(2, 119), (223, 590), (155, 863), (2, 335)⟩)
                                (.split 0 5113
                                  (.leaf ⟨(2, 143), (223, 590), (155, 863), (2, 335)⟩)
                                  (.split 0 7789
                                    (.leaf ⟨(4, 353), (223, 590), (155, 863), (2, 335)⟩)
                                    (.split 0 17293
                                      (.leaf ⟨(2, 263), (223, 590), (155, 863), (2, 335)⟩)
                                      (.leaf ⟨(1, 5), (223, 590), (155, 863), (2, 335)⟩))))))))))))
                (.split 3 30103
                  (.split 0 13
                    (.leaf ⟨(109, 393), (223, 590), (155, 863), (2, 347)⟩)
                    (.split 0 37
                      (.leaf ⟨(145, 882), (223, 590), (155, 863), (2, 347)⟩)
                      (.split 0 61
                        (.leaf ⟨(79, 617), (223, 590), (155, 863), (2, 347)⟩)
                        (.split 0 73
                          (.leaf ⟨(57, 487), (223, 590), (155, 863), (2, 347)⟩)
                          (.split 0 109
                            (.leaf ⟨(25, 261), (223, 590), (155, 863), (2, 347)⟩)
                            (.split 0 409
                              (.leaf ⟨(9, 182), (223, 590), (155, 863), (2, 347)⟩)
                              (.split 0 709
                                (.leaf ⟨(8, 213), (223, 590), (155, 863), (2, 347)⟩)
                                (.split 0 3541
                                  (.leaf ⟨(2, 119), (223, 590), (155, 863), (2, 347)⟩)
                                  (.split 0 5113
                                    (.leaf ⟨(2, 143), (223, 590), (155, 863), (2, 347)⟩)
                                    (.split 0 7789
                                      (.leaf ⟨(4, 353), (223, 590), (155, 863), (2, 347)⟩)
                                      (.split 0 17293
                                        (.leaf ⟨(2, 263), (223, 590), (155, 863), (2, 347)⟩)
                                        (.split 0 28057
                                          (.leaf ⟨(2, 335), (223, 590), (155, 863), (2, 347)⟩)
                                          (.leaf ⟨(1, 5), (223, 590), (155, 863), (2, 347)⟩)))))))))))))
                  (.split 3 86143
                    (.split 0 13
                      (.leaf ⟨(109, 393), (223, 590), (155, 863), (2, 587)⟩)
                      (.split 0 37
                        (.leaf ⟨(145, 882), (223, 590), (155, 863), (2, 587)⟩)
                        (.split 0 61
                          (.leaf ⟨(79, 617), (223, 590), (155, 863), (2, 587)⟩)
                          (.split 0 73
                            (.leaf ⟨(57, 487), (223, 590), (155, 863), (2, 587)⟩)
                            (.split 0 109
                              (.leaf ⟨(25, 261), (223, 590), (155, 863), (2, 587)⟩)
                              (.split 0 409
                                (.leaf ⟨(9, 182), (223, 590), (155, 863), (2, 587)⟩)
                                (.split 0 709
                                  (.leaf ⟨(8, 213), (223, 590), (155, 863), (2, 587)⟩)
                                  (.split 0 3541
                                    (.leaf ⟨(2, 119), (223, 590), (155, 863), (2, 587)⟩)
                                    (.split 0 5113
                                      (.leaf ⟨(2, 143), (223, 590), (155, 863), (2, 587)⟩)
                                      (.split 0 7789
                                        (.leaf ⟨(4, 353), (223, 590), (155, 863), (2, 587)⟩)
                                        (.split 0 17293
                                          (.leaf ⟨(2, 263), (223, 590), (155, 863), (2, 587)⟩)
                                          (.split 0 28057
                                            (.leaf ⟨(2, 335), (223, 590), (155, 863), (2, 587)⟩)
                                            (.leaf ⟨(1, 5), (223, 590), (155, 863), (2, 587)⟩)))))))))))))
                    (.split 0 13
                      (.leaf ⟨(109, 393), (223, 590), (155, 863), (1, 8)⟩)
                      (.split 0 37
                        (.leaf ⟨(145, 882), (223, 590), (155, 863), (1, 8)⟩)
                        (.split 0 61
                          (.leaf ⟨(79, 617), (223, 590), (155, 863), (1, 8)⟩)
                          (.split 0 73
                            (.leaf ⟨(57, 487), (223, 590), (155, 863), (1, 8)⟩)
                            (.split 0 109
                              (.leaf ⟨(25, 261), (223, 590), (155, 863), (1, 8)⟩)
                              (.split 0 409
                                (.leaf ⟨(9, 182), (223, 590), (155, 863), (1, 8)⟩)
                                (.split 0 709
                                  (.leaf ⟨(8, 213), (223, 590), (155, 863), (1, 8)⟩)
                                  (.split 0 3541
                                    (.leaf ⟨(2, 119), (223, 590), (155, 863), (1, 8)⟩)
                                    (.split 0 5113
                                      (.leaf ⟨(2, 143), (223, 590), (155, 863), (1, 8)⟩)
                                      (.split 0 7789
                                        (.leaf ⟨(4, 353), (223, 590), (155, 863), (1, 8)⟩)
                                        (.split 0 17293
                                          (.leaf ⟨(2, 263), (223, 590), (155, 863), (1, 8)⟩)
                                          (.split 0 28057
                                            (.leaf ⟨(2, 335), (223, 590), (155, 863), (1, 8)⟩)
                                            (.leaf ⟨(1, 5), (223, 590), (155, 863), (1, 8)⟩)))))))))))))))))))))

/-- Subtree 16 of the class triple `(7, 31, big)` passes the check. -/
theorem u44_16_ok : treeOK (.c7, .c31, .big)
    ⟨.free .q 13 [], .pin 7, .pin 31, .free .big 61 [3541, 1723, 1087, 991, 727, 709, 409, 307, 151, 127, 109, 103, 79, 73, 67, 61]⟩ u44_16 = true :=
  treeOK_split (by decide) rfl
    (treeOK_split (by decide) rfl
      (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g0).1)
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g0).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g0).2).2).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g0).2).2).2).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g0).2).2).2).2)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g1).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g1).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g1).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g1).2).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g1).2).2).2).2)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g2).2).1)
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g2).2).2).1)))))))))))))
    (treeOK_split (by decide) rfl
      (treeOK_split (by decide) rfl
        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g2).2).2).2).1)
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g2).2).2).2).2)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g3).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g3).2).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g3).2).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g3).2).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g3).2).2).2).2)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g4).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g4).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g4).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g4).2).2).2).1)
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g4).2).2).2).2))))))))))))
      (treeOK_split (by decide) rfl
        (treeOK_split (by decide) rfl
          (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g5).1)
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g5).2).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g5).2).2).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g5).2).2).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g5).2).2).2).2)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g6).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g6).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g6).2).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g6).2).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g6).2).2).2).2)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g7).1)
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g7).2).1))))))))))))
        (treeOK_split (by decide) rfl
          (treeOK_split (by decide) rfl
            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g7).2).2).1)
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g7).2).2).2).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g7).2).2).2).2)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g8).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g8).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g8).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g8).2).2).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g8).2).2).2).2)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g9).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g9).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g9).2).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g9).2).2).2).1)
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g9).2).2).2).2)))))))))))))
          (treeOK_split (by decide) rfl
            (treeOK_split (by decide) rfl
              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g10).1)
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g10).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g10).2).2).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g10).2).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g10).2).2).2).2)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g11).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g11).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g11).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g11).2).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g11).2).2).2).2)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g12).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g12).2).1)
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g12).2).2).1)))))))))))))
            (treeOK_split (by decide) rfl
              (treeOK_split (by decide) rfl
                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g12).2).2).2).1)
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g12).2).2).2).2)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g13).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g13).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g13).2).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g13).2).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g13).2).2).2).2)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g14).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g14).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g14).2).2).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g14).2).2).2).1)
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g14).2).2).2).2))))))))))))
              (treeOK_split (by decide) rfl
                (treeOK_split (by decide) rfl
                  (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g15).1)
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g15).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g15).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g15).2).2).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g15).2).2).2).2)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g16).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g16).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g16).2).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g16).2).2).2).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g16).2).2).2).2)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g17).1)
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g17).2).1))))))))))))
                (treeOK_split (by decide) rfl
                  (treeOK_split (by decide) rfl
                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g17).2).2).1)
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g17).2).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g17).2).2).2).2)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g18).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g18).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g18).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g18).2).2).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g18).2).2).2).2)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g19).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g19).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g19).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g19).2).2).2).1)
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g19).2).2).2).2)))))))))))))
                  (treeOK_split (by decide) rfl
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g20).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g20).2).1)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g20).2).2).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g20).2).2).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g20).2).2).2).2)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g21).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g21).2).1)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g21).2).2).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g21).2).2).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g21).2).2).2).2)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g22).1)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g22).2).1)
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g22).2).2).1)))))))))))))
                    (treeOK_split (by decide) rfl
                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g22).2).2).2).1)
                      (treeOK_split (by decide) rfl
                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g22).2).2).2).2)
                        (treeOK_split (by decide) rfl
                          (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g23).1)
                          (treeOK_split (by decide) rfl
                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g23).2).1)
                            (treeOK_split (by decide) rfl
                              (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g23).2).2).1)
                              (treeOK_split (by decide) rfl
                                (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g23).2).2).2).1)
                                (treeOK_split (by decide) rfl
                                  (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g23).2).2).2).2)
                                  (treeOK_split (by decide) rfl
                                    (treeOK_leaf (Bool.and_eq_true_iff.mp u44_16_g24).1)
                                    (treeOK_split (by decide) rfl
                                      (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g24).2).1)
                                      (treeOK_split (by decide) rfl
                                        (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g24).2).2).1)
                                        (treeOK_split (by decide) rfl
                                          (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g24).2).2).2).1)
                                          (treeOK_split (by decide) rfl
                                            (treeOK_leaf (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp u44_16_g24).2).2).2).2)
                                            (treeOK_leaf u44_16_g25)))))))))))))))))))))

private theorem u45_0_g0 :
    leafOK (.c7, .c37, .c43) ⟨.free .q 13 [], .pin 7, .pin 37, .pin 43⟩ ⟨(109, 393), (223, 590), (145, 882), (61, 400)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 37, 43)`, with 1 leaves. -/
def u45_0 : Tree :=
  .leaf ⟨(109, 393), (223, 590), (145, 882), (61, 400)⟩

/-- Subtree 0 of the class triple `(7, 37, 43)` passes the check. -/
theorem u45_0_ok : treeOK (.c7, .c37, .c43)
    (rootNode (.c7, .c37, .c43)) u45_0 = true :=
  treeOK_leaf u45_0_g0

private theorem u46_0_g0 :
    leafOK (.c7, .c37, .n2) ⟨.free .q 13 [], .pin 7, .pin 37, .free .n2 11 []⟩ ⟨(109, 393), (223, 590), (145, 882), (0, 1)⟩ = true := by
  decide +kernel

/-- Subtree 0 of the class triple `(7, 37, n2)`, with 1 leaves. -/
def u46_0 : Tree :=
  .leaf ⟨(109, 393), (223, 590), (145, 882), (0, 1)⟩

/-- Subtree 0 of the class triple `(7, 37, n2)` passes the check. -/
theorem u46_0_ok : treeOK (.c7, .c37, .n2)
    (rootNode (.c7, .c37, .n2)) u46_0 = true :=
  treeOK_leaf u46_0_g0

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.u44_16_ok
#print axioms OddPerfect.ThreeFreeThree.u45_0_ok
#print axioms OddPerfect.ThreeFreeThree.u46_0_ok
