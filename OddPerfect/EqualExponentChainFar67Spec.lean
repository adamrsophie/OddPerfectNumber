import OddPerfect.EqualExponentChainFar67Data

/-!
# Equal exponent chains: `l = 67`, the special case

The tree for `l = 67` when `67` is the special prime.
The certificate was found by an untrusted search and is checked by `decide +kernel`.
Restricted family result; no published source was checked; novelty not verified.
-/

namespace OddPerfect.EqChain

/-- The tree for `l = 67` when `67` is the special prime is accepted. -/
theorem spec67_run : run 67 pc67 ⟨[], [], some 67, 2⟩ spec67 = true := by
  decide +kernel

end OddPerfect.EqChain

#print axioms OddPerfect.EqChain.spec67_run
