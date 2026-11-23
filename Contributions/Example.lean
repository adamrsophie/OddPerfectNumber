import OddPerfect.Steps

/-!
Format example for contributions: one file, one theorem named after its step, in the
namespace `OddPerfect.Proofs`, whose statement is exactly the step.
-/

namespace OddPerfect.Proofs

theorem Example : OddPerfect.Steps.Example := by
  intro N h h2
  have h1 := Nat.odd_iff.mp h.odd
  omega

end OddPerfect.Proofs
