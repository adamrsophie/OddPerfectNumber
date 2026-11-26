import OddPerfect.EqualExponentChainFar67Data

/-!
# Equal exponent chains: `l = 67`, piece 1

Piece 1 of the tree for `l = 67` when `67` is ordinary.
The certificate was found by an untrusted search and is checked by `decide +kernel`.
Restricted family result; no published source was checked; novelty not verified.
-/

namespace OddPerfect.EqChain

/-- Piece 1 of the tree for `l = 67` is accepted. -/
theorem ord67_run1 :
    runC 67 pc67 [cut67_2] cut67_1 ord67_1 = true := by
  decide +kernel

end OddPerfect.EqChain

#print axioms OddPerfect.EqChain.ord67_run1
