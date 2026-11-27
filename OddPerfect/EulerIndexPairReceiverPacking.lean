import OddPerfect.EulerIndexPairReceiverBound
import OddPerfect.EulerIndexPairReceiverCore
import OddPerfect.DisjointReceiverTail

/-!
# Two prime Euler index, branch `v = 1`: receiver certificates with an unbounded pure tail

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, oriented by a frame `PairFrame N q r s t u`, in the branch `v = 1`.

* `PairFrame.false_of_packRow`: a certificate accepted by `ReceiverSieve.packRow` for the
  receiver `u` is impossible. The outsiders whose row is a pure power of `u` are not bounded
  in number; for each kept row length one center is removed
  (`exists_center_of_common_receiver`), and the rest contributes at most
  `(5 ^ (d - 1) - 1) / (5 ^ (d - 1) - 2)` to `∏ p / (p - 1)`.

The frame theorems `PairFrame.absent_of_tests`, `PairFrame.pure_outsider_row` and
`PairFrame.core_card_le` and the checker are in `OddPerfect.EulerIndexPairReceiverCore`.
Each receiver needs its own finite certificate; no uniform statement over all receivers is
proved. The branch `v = 0` and the family are not excluded.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open ReceiverSieve

variable {N q m r s t u : ℕ}

/-- An accepted receiver certificate is impossible. -/
theorem PairFrame.false_of_packRow (F : PairFrame N q r s t u) (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hv : σ 1 (t ^ N.factorization t) = q * u) {A : List (ℕ × List ℕ)} {L : List ℕ}
    (hrow : packRow u A L = true) : False :=
  F.false_of_packRow_of_tail h hq hN hqm hr hs hrs hJ hv
    (fun _ _ _ _ hd hd3 hu hud hB hS => exists_center_of_common_receiver hd hd3 hu hud hB hS)
    hrow

end OddPerfect

#print axioms OddPerfect.PairFrame.false_of_packRow
