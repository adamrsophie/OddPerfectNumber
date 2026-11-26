import OddPerfect.ImpureRowCountSmall
import OddPerfect.ImpureRowCountFour
import OddPerfect.McDaniel

/-!
# A common odd prime index forces four rows that are not prime powers

Let `N` be an odd perfect number with special prime `q`, and suppose one odd prime `l` divides
every ordinary index `e_p + 1`. Then any finite set `M` containing every ordinary prime whose
row `σ(p ^ e_p)` is not a prime power has at least four elements
(`four_le_card_of_pure_outside_all`). This joins three landed results: for `l = 3` the
hypothesis is contradictory (`mcdaniel`), for `5 ≤ l ≤ 521` the count is
`four_le_card_of_pure_outside_small` (finite trees checked by the kernel), and for `l ≥ 523` it
is `four_le_card_of_pure_outside` (the packing bound).

Restricted result (one odd prime divides every ordinary index); no published source was
checked for the count of four; novelty not verified. The family itself is not excluded, and
nothing is said when no odd prime divides every ordinary index. The odd perfect number
conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- **At least four impure rows for every odd prime index.** Let `N` be an odd perfect number
with special prime `q` and `l` an odd prime dividing `e_p + 1` for every prime factor `p ≠ q`.
If `M` is a finite set such that every prime factor `p ≠ q` outside `M` has a row `σ(p ^ e_p)`
that is a prime power, then `M` has at least four elements.

Restricted result (one odd prime divides every ordinary index); no published source was
checked for the count of four; novelty not verified. The common index family is not excluded
by this statement, and nothing is said when no odd prime divides every ordinary index. The odd
perfect number conjecture remains open. -/
theorem four_le_card_of_pure_outside_all {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : 4 ≤ M.card := by
  have h2 := hl.two_le
  rcases Nat.lt_or_ge l 5 with h5 | h5
  · have hl4 : l ≠ 4 := fun he => absurd (he ▸ hl) (by norm_num)
    have hl3 : l = 3 := by omega
    subst hl3
    exact (mcdaniel h hq hodd fun p hp hpq => by have := hidx p hp hpq; omega).elim
  · rcases Nat.lt_or_ge l 522 with h522 | h522
    · exact four_le_card_of_pure_outside_small h hq hodd hl h5 (by omega) hidx M hM
    · have hne : l ≠ 522 := fun he => absurd (he ▸ hl) (by norm_num)
      exact four_le_card_of_pure_outside h hq hodd hl (by omega) hidx M hM

end OddPerfect

#print axioms OddPerfect.four_le_card_of_pure_outside_all
