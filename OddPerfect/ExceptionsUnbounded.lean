import OddPerfect.AbundancyGapGeneral
import OddPerfect.ExceptionsUnboundedBase
import OddPerfect.OmegaSevenFinal

/-!
# Any bounded number of exceptions to a common index prime, for large `l`

For every `s` there is a bound `L` such that for every prime `l ≥ L`: if every prime factor
`p` of an odd perfect number `N` outside a set `E` of at most `s` numbers has `l ∣ e_p + 1`,
and some prime factor of `N` lies outside `E`, then `l ∣ N`.

This module joins the gap statement for prime powers of Euler form
(`exists_abundancy_gap_general`) with the reduction `exists_index_bound_of_exceptions_of`.
For at most six exceptions the hypothesis that a prime factor lies outside `E` holds for
every odd perfect number, since it has at least seven prime factors.

Restricted result: the bound `L` is not explicit (the proof gives no value), so for each
fixed `l` this says nothing about a given number of exceptions; the landed modules give
`l ≥ 23` for two exceptions and `l ≥ 359` for three. No published source was checked;
novelty not verified. The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The gap statement of `ExceptionsUnboundedBase` holds for every `s`. -/
theorem generalGapStatement_holds (s : ℕ) : GeneralGapStatement s :=
  exists_abundancy_gap_general s

/-- For every `s` there is a bound `L` such that for every prime `l ≥ L`: if every prime
factor of an odd perfect number `N` outside a set `E` of at most `s` numbers has an index
divisible by `l`, and some prime factor of `N` lies outside `E`, then `l` divides `N`.
Restricted result; the bound `L` is not explicit; no published source was checked; novelty
not verified. The odd perfect number conjecture remains open. -/
theorem exists_index_bound_of_exceptions (s : ℕ) :
    ∃ L : ℕ, ∀ {N l : ℕ}, OddPerfect N → l.Prime → L ≤ l →
      ∀ E : Finset ℕ, E.card ≤ s → (∃ p ∈ N.primeFactors, p ∉ E) →
        (∀ p ∈ N.primeFactors, p ∉ E → l ∣ N.factorization p + 1) → l ∣ N :=
  exists_index_bound_of_exceptions_of generalGapStatement_holds s

/-- At most six exceptions: there is a bound `L` such that for every prime `l ≥ L`, an odd
perfect number all of whose prime factors outside a set `E` of at most six numbers have an
index divisible by `l` is divisible by `l`. Restricted result; the bound `L` is not explicit;
no published source was checked; novelty not verified. The odd perfect number conjecture
remains open. -/
theorem exists_index_bound_of_six_exceptions :
    ∃ L : ℕ, ∀ {N l : ℕ}, OddPerfect N → l.Prime → L ≤ l →
      ∀ E : Finset ℕ, E.card ≤ 6 →
        (∀ p ∈ N.primeFactors, p ∉ E → l ∣ N.factorization p + 1) → l ∣ N := by
  obtain ⟨L, hL⟩ := exists_index_bound_of_exceptions 6
  refine ⟨L, fun {N l} h hl hLl E hE hcomp => hL h hl hLl E hE ?_ hcomp⟩
  by_contra hno
  have hsub : N.primeFactors ⊆ E := fun p hp => by
    by_contra hpE
    exact hno ⟨p, hp, hpE⟩
  have h7 := seven_le_card_primeFactors h
  have := Finset.card_le_card hsub
  omega

end OddPerfect

#print axioms OddPerfect.generalGapStatement_holds
#print axioms OddPerfect.exists_index_bound_of_exceptions
#print axioms OddPerfect.exists_index_bound_of_six_exceptions
