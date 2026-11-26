import OddPerfect.EqualExponentChainFar53Data

/-!
# Equal exponent chains: `l = 53`, the special case

The tree for `l = 53` when `53` is the special prime.
The certificate was found by an untrusted search and is checked by `decide +kernel`.
Restricted family result; no published source was checked; novelty not verified.
-/

namespace OddPerfect.EqChain

/-- The tree for `l = 53` when `53` is the special prime is accepted. -/
theorem spec53_run : run 53 pc53 ⟨[], [], some 53, 2⟩ spec53 = true := by
  decide +kernel

end OddPerfect.EqChain

#print axioms OddPerfect.EqChain.spec53_run
