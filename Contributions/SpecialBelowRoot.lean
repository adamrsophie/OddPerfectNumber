import OddPerfect.Steps
import OddPerfect.SpecialBelowAll

/-!
Proof of the step `SpecialBelowRoot`: in Euler's form `N = q * m ^ 2` with `q ∤ m`, the special
prime is below `m`. This is `special_lt_root` of `OddPerfect/SpecialBelowAll.lean` at special
exponent `1`.
-/

namespace OddPerfect.Proofs

theorem SpecialBelowRoot : OddPerfect.Steps.SpecialBelowRoot := by
  intro N q m h hq hN hqm
  exact OddPerfect.special_lt_root (k := 1) h hq (by rw [pow_one]; exact hN) hqm

end OddPerfect.Proofs
