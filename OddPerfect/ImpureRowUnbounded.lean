import OddPerfect.AbundancyGap
import OddPerfect.ImpureRowUnboundedBase

/-!
# The number of impure rows grows with the common index prime

Let `N` be an odd perfect number with special prime `q` and let `l` be an odd prime dividing
every ordinary index `e_p + 1` (`p ≠ q` a prime factor of `N`). The row of `p` is
`σ(p ^ e_p)`; it is impure when it is not a prime power.

`exists_index_bound_of_impure_rows`: for every `K` there is a bound `L` such that `l ≥ L`
forces at least `K` ordinary primes with an impure row. The module joins the gap statement
(`exists_abundancy_gap`) with the reduction (`exists_index_bound_of_impure_rows_of`).

The bound `L` is not explicit: the proof gives no value. For every odd prime `l` the landed
count is four (`four_le_card_of_pure_outside_all`); this module says nothing more for a fixed
`l`.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. The common index family is not excluded, and the odd perfect
number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The gap statement holds for every `K`. -/
theorem abundancyGapStatement_holds (K : ℕ) : AbundancyGapStatement K :=
  exists_abundancy_gap K

/-- **The number of impure rows is unbounded as the common index prime grows.** For every `K`
there is `L` such that: if `N` is odd perfect with special prime `q`, a prime `l ≥ L` divides
every ordinary index, and `M` contains every ordinary prime whose row is not a prime power,
then `M` has at least `K` elements. The bound `L` is not explicit. Restricted result; no
published source was checked; novelty not verified. The family is not excluded. -/
theorem exists_index_bound_of_impure_rows (K : ℕ) :
    ∃ L : ℕ, ∀ {N q l : ℕ}, OddPerfect N → q.Prime → Odd (N.factorization q) → l.Prime →
      L ≤ l → (∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) →
      ∀ M : Finset ℕ, (∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
        ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) → K ≤ M.card :=
  exists_index_bound_of_impure_rows_of abundancyGapStatement_holds K

end OddPerfect

#print axioms OddPerfect.exists_index_bound_of_impure_rows
