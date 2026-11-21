import OddPerfect.OmegaSevenEngine

/-!
# Pilot run of the engine `OmegaSevenEngine.run`

One kernel run of the verified search of `OddPerfect/OmegaSevenEngine.lean` on the prefix
`3, 5, 13` of an odd perfect number with exactly six distinct prime factors: the three smallest
prime factors are `3, 5, 13` and three more prime factors exceed `13`. The state is written as
the child that `OmegaSevenSearch.closed_of_window` produces from the state
`[⟨3, 2, false⟩, ⟨5, 1, false⟩]` with `4` further primes. The exact Python mirror of the engine
(`engine.py` in the scratch folder of this module) visits `4415` nodes on this state.
-/

namespace OddPerfect.OmegaSevenEngine

open OmegaSixSearch (Ent kmin)

set_option maxRecDepth 100000 in
/-- Six prime factors with `3, 5, 13` the three smallest is impossible. -/
theorem closed_3_5_13 :
    OmegaSevenSearch.Closed ([⟨3, 2, false⟩, ⟨5, 1, false⟩] ++ [⟨13, kmin 13, false⟩]) (4 - 1) 13 :=
  closed_of_run (f := 60) (by decide +kernel)

end OddPerfect.OmegaSevenEngine

#print axioms OddPerfect.OmegaSevenEngine.closed_3_5_13
