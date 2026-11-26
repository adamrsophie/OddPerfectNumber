import OddPerfect.EqualExponentChainFar67Data

/-!
# Equal exponent chains: `l = 67`, piece 0

Piece 0 of the tree for `l = 67` when `67` is ordinary.
The certificate was found by an untrusted search and is checked by `decide +kernel`.
Restricted family result; no published source was checked; novelty not verified.
-/

namespace OddPerfect.EqChain

/-- Piece 0 of the tree for `l = 67` is accepted. -/
theorem ord67_run0 :
    runC 67 pc67 [cut67_1] ⟨[67], [67], none, 2⟩ ord67_0 = true := by
  decide +kernel

end OddPerfect.EqChain

#print axioms OddPerfect.EqChain.ord67_run0
