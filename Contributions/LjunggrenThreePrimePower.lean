import OddPerfect.Steps
import OddPerfect.ThreeRowPrime

/-!
Proof of the step `LjunggrenThreePrimePower`: for primes `p`, `r` the equation
`p ^ 2 + p + 1 = 3 * r ^ a` forces `a ≤ 2`. This is `ljunggrenThreePrimePower` of
`OddPerfect/ThreeRowPrime.lean`.
-/

namespace OddPerfect.Proofs

theorem LjunggrenThreePrimePower : OddPerfect.Steps.LjunggrenThreePrimePower := by
  intro p r a hp hr ha h
  exact OddPerfect.ljunggrenThreePrimePower p r a hp hr ha h

end OddPerfect.Proofs
