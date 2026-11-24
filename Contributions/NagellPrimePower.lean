import OddPerfect.Steps
import OddPerfect.NagellPrime

/-!
Proof of the step `NagellPrimePower`: for primes `p`, `r` the equation `p ^ 2 + p + 1 = r ^ a`
forces `a = 1`. This is `nagellPrimePower` of `OddPerfect/NagellPrime.lean`.
-/

namespace OddPerfect.Proofs

theorem NagellPrimePower : OddPerfect.Steps.NagellPrimePower := by
  intro p r a hp hr ha h
  exact OddPerfect.nagellPrimePower p r a hp hr ha h

end OddPerfect.Proofs
