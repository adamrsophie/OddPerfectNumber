import OddPerfect.ImpureRowFourBase
import OddPerfect.ImpureRowCount

/-!
# A common odd prime index `l ≥ 523` forces four rows that are not prime powers

Let `N` be an odd perfect number with special prime `q`, and suppose one prime `l ≥ 523`
divides every ordinary index `e_p + 1`. Then any finite set `M` containing every ordinary prime
whose row `σ(p ^ e_p)` is not a prime power has at least four elements
(`four_le_card_of_pure_outside`). The counts for smaller `l` are in `ImpureRowCount`.

The argument is the packing bound of `ImpureRowCount`, followed by a case analysis on the
three remaining centers: `{3, 5, 7}` gives `105 ∣ N`; `{3, 5, c}` with `c ∈ {11, 13}` gives a
divisor of abundancy above `2` unless `5` is the special prime with exponent `1`, a case the
packing bound also excludes. See `ImpureRowFourBase`.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. Nothing is said when no odd prime divides every ordinary index.
The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- **(C) At least four impure rows.** Let `N` be an odd perfect number with special prime `q`
and `l ≥ 523` a prime dividing `e_p + 1` for every prime factor `p ≠ q`. If `M` is a finite set
such that every prime factor `p ≠ q` outside `M` has a row `σ(p ^ e_p)` that is a prime power,
then `M` has at least four elements.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. The cases `l < 523` are not covered (see `ImpureRowCount` for
`l ≥ 7` and `l ≥ 31`), and nothing is said when no odd prime divides every ordinary index. The
odd perfect number conjecture remains open. -/
theorem four_le_card_of_pure_outside {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl523 : 523 ≤ l)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : 4 ≤ M.card :=
  four_le_card_of_pure_outside_of packingStatement_holds h hq hodd hl hl523 hidx M hM

end OddPerfect

#print axioms OddPerfect.four_le_card_of_pure_outside
