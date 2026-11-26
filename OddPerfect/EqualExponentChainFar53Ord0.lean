import OddPerfect.EqualExponentChainFar53Data

/-!
# Equal exponent chains: `l = 53`, piece 0

Piece 0 of the tree for `l = 53` when `53` is ordinary.
The certificate was found by an untrusted search and is checked by `decide +kernel`.
Restricted family result; no published source was checked; novelty not verified.
-/

namespace OddPerfect.EqChain

/-- Piece 0 of the tree for `l = 53` is accepted. -/
theorem ord53_run0 :
    runC 53 pc53 [cut53_1] ⟨[53], [53], none, 2⟩ ord53_0 = true := by
  decide +kernel

end OddPerfect.EqChain

#print axioms OddPerfect.EqChain.ord53_run0
