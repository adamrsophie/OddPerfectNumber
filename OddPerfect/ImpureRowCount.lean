import OddPerfect.ImpureRowBase
import OddPerfect.PureCoverPacking

/-!
# A common odd prime in every ordinary index forces several rows that are not prime powers

Let `N` be an odd perfect number with special prime `q`, and suppose one odd prime `l` divides
every ordinary index `e_p + 1` (`p ≠ q` a prime factor of `N`). The theorem
`not_all_pure_common_index` says that then some ordinary row `σ(p ^ e_p)` is not a prime power
(an impure row). This module counts them: any finite set `M` containing every ordinary prime
with an impure row has

* (A) at least two elements when `l ≥ 7` (`two_le_card_of_pure_outside`),
* (B) at least three elements when `l ≥ 31` (`three_le_card_of_pure_outside`);

and (D) one ordinary prime `d` may be exempt from both the index and the purity condition when
`l ≥ 13` (`not_all_pure_common_index_one_hole`). The count (C), four elements for `l ≥ 523`, is
in `ImpureRowCountFour`.

Argument. Every pure row outside `M ∪ {q}` has index exactly `l` and its receiver lies in
`M ∪ {q}` (`impureRow_cover`). The packing theorem `exists_centers_of_pure_cover` then bounds
`∏ p/(p-1)` over the prime factors of `N` by the product over a few centers, one of which is
`l` (as `l ∣ N`), times an explicit factor; for the stated ranges of `l` this is below `2`,
against `2 < ∏ p/(p-1)`.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. Nothing is said when no odd prime divides every ordinary index.
The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The packing statement holds (`exists_centers_of_pure_cover`). -/
theorem packingStatement_holds : PackingStatement :=
  fun hl hl2 hS hX hK hcov => exists_centers_of_pure_cover hl hl2 hS hX hK hcov

/-- **(A) At least two impure rows.** Let `N` be an odd perfect number with special prime `q`
and `l ≥ 7` a prime dividing `e_p + 1` for every prime factor `p ≠ q`. If `M` is a finite set
such that every prime factor `p ≠ q` outside `M` has a row `σ(p ^ e_p)` that is a prime power,
then `M` has at least two elements; so at least two ordinary rows are not prime powers.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. The cases `l < 7` are not covered, and nothing is said when no
odd prime divides every ordinary index. The odd perfect number conjecture remains open. -/
theorem two_le_card_of_pure_outside {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl7 : 7 ≤ l)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : 2 ≤ M.card :=
  two_le_card_of_pure_outside_of packingStatement_holds h hq hodd hl hl7 hidx M hM

/-- **(B) At least three impure rows.** Let `N` be an odd perfect number with special prime
`q` and `l ≥ 31` a prime dividing `e_p + 1` for every prime factor `p ≠ q`. If `M` is a finite
set such that every prime factor `p ≠ q` outside `M` has a row `σ(p ^ e_p)` that is a prime
power, then `M` has at least three elements.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. The cases `l < 31` are not covered (for `7 ≤ l` see
`two_le_card_of_pure_outside`), and nothing is said when no odd prime divides every ordinary
index. The odd perfect number conjecture remains open. -/
theorem three_le_card_of_pure_outside {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl31 : 31 ≤ l)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : 3 ≤ M.card :=
  three_le_card_of_pure_outside_of packingStatement_holds h hq hodd hl hl31 hidx M hM

/-- **(D) All ordinary rows pure and a common index prime, with one exempt prime.** Let `N` be
an odd perfect number with special prime `q`, `l ≥ 13` a prime and `d` any number. It is
impossible that every prime factor `p ∉ {q, d}` has `l ∣ e_p + 1` and a row `σ(p ^ e_p)` that is
a prime power. Nothing is assumed about the prime `d` (its index and its row are free).

Restricted result (one odd prime divides every ordinary index but one); no published source
was checked; novelty not verified. The cases `l < 13` are not covered, and nothing is said when
no odd prime divides all but one ordinary index. The odd perfect number conjecture remains
open. -/
theorem not_all_pure_common_index_one_hole {N q l d : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl13 : 13 ≤ l)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → l ∣ N.factorization p + 1)
    (hpure : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : False :=
  not_all_pure_common_index_one_hole_of packingStatement_holds h hq hodd hl hl13 hidx hpure

end OddPerfect

#print axioms OddPerfect.packingStatement_holds
#print axioms OddPerfect.two_le_card_of_pure_outside
#print axioms OddPerfect.three_le_card_of_pure_outside
#print axioms OddPerfect.not_all_pure_common_index_one_hole
