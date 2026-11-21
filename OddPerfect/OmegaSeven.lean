import OddPerfect.OmegaSix
import OddPerfect.SpecialPrime

/-!
# Odd perfect numbers with exactly six prime factors

This file works toward Hagis (1980) and Chein (1979): an odd perfect number has at least seven
distinct prime factors. It runs the verified branch and bound search `OmegaSixSearch.solve` of
`OddPerfect/OmegaSix.lean` (Gradshtein and Kühnel), with its soundness theorem `solve_sound`,
from new root states.

A search state is a list of entries `(p, k, ex)`: `p` is a prime factor of `N` whose exponent
is exactly `k` (when `ex`) or at least `k`; there are `j` further prime factors, all above `m`.
See `OddPerfect/OmegaSix.lean` for the rules.

Results, for an odd perfect number `N` with exactly six distinct prime factors:
* `fifteen_dvd_of_card_eq_six`: `15 ∣ N`.
* `exists_prime_dvd_of_card_eq_six`: moreover some prime `p` with `11 ≤ p ≤ 31` divides `N`,
  so the third smallest prime factor is one of `11, 13, 17, 19, 23, 29, 31`.

The searches are split into one kernel check per child of the top states (`closed_of_window`),
which keeps each check small. The step from a state to its children is the enumeration lemma
`OmegaSixSearch.enum_sound`. The full theorem
`7 ≤ ω(N)` is not proved here: the remaining prefixes `3, 5, p` with `11 ≤ p ≤ 31` need over
500 thousand search nodes outside `p = 17`, and the prefix `3, 5, 17` (with `257` and `65537`
next) does not close at all, since the abundancy bounds of the Fermat primes stay below `2` for
every exponent.
-/

namespace OddPerfect.OmegaSevenSearch

open OmegaSixSearch
open Cert (geom)

variable {N : ℕ}

/-- A root state: `3` is a prime factor with exponent at least two, and every other prime
factor exceeds `m`. -/
private theorem holds_root3 (h : OddPerfect N) (h3 : 3 ∈ N.primeFactors) {m : ℕ}
    (hm : ∀ q ∈ N.primeFactors, q ≠ 3 → m < q) :
    Holds N [⟨3, 2, false⟩] (N.primeFactors.card - 1) m := by
  have hpos : 0 < N.primeFactors.card := Finset.card_pos.mpr ⟨3, h3⟩
  refine ⟨h, by simp, ?_, by simp; omega, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨h3, kmin_le h h3, fun h => by simp at h⟩
  · intro q hq hn
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn
    exact hm q hq hn

/-- A root state: `3` and `5` are prime factors, with exponents at least two and one, and every
other prime factor exceeds `m`. -/
private theorem holds_root35 (h : OddPerfect N) (h3 : 3 ∈ N.primeFactors)
    (h5 : 5 ∈ N.primeFactors) {m : ℕ} (hm : ∀ q ∈ N.primeFactors, q ≠ 3 → q ≠ 5 → m < q) :
    Holds N [⟨3, 2, false⟩, ⟨5, 1, false⟩] (N.primeFactors.card - 2) m := by
  have h2 : 2 ≤ N.primeFactors.card := by
    have : ({3, 5} : Finset ℕ) ⊆ N.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    simpa using Finset.card_le_card this
  refine ⟨h, by simp, ?_, by simp; omega, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨h3, kmin_le h h3, fun h => by simp at h⟩
    · exact ⟨h5, kmin_le h h5, fun h => by simp at h⟩
  · intro q hq hn
    simp only [List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hn
    exact hm q hq hn.1 hn.2

/-- The candidate next primes of a state: the primes in the window `[lowB, minB bounds]`. -/
def window (l : List Ent) (j m : ℕ) : List ℕ :=
  (List.range' (lowB l j m) (minB (bounds l j m) + 1 - lowB l j m)).filter isPrimeQ

/-- A state is closed when no number satisfies it. -/
def Closed (l : List Ent) (j m : ℕ) : Prop := ∀ N, ¬ Holds N l j m

/-- An accepted state is closed. -/
theorem closed_of_solve (f : ℕ) {l : List Ent} {j m : ℕ} (h : solve f l j m = true) :
    Closed l j m := fun _ => solve_sound f l j m h

/-- A state with a bounded next prime is closed when every child in its window is closed. -/
theorem closed_of_window {l : List Ent} {j m : ℕ} (hj : j ≠ 0) (hb : bounds l j m ≠ [])
    (h : ∀ q ∈ window l j m, Closed (l ++ [⟨q, kmin q, false⟩]) (j - 1) q) : Closed l j m := by
  intro N H
  obtain ⟨q, hlo, hhi, hp, H'⟩ := enum_sound H hj hb
  refine h q ?_ N H'
  rw [window, List.mem_filter, List.mem_range'_1]
  exact ⟨by omega, hp⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The prefix `3, 7, 11` (as the three smallest prime factors) is closed for six primes. -/
theorem closed_3_7_11 :
    Closed ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩] ++ [⟨11, kmin 11, false⟩]) (5 - 1 - 1) 11 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩] ++ [⟨11, kmin 11, false⟩])
      (5 - 1 - 1) 11 = [13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73] by
    decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact closed_of_solve 30 (by decide +kernel)

/-- The prefix `3, 7, 13` is closed for six primes. -/
theorem closed_3_7_13 :
    Closed ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩] ++ [⟨13, kmin 13, false⟩]) (5 - 1 - 1) 13 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩] ++ [⟨13, kmin 13, false⟩])
      (5 - 1 - 1) 13 = [17, 19, 23, 29, 31, 37, 41, 43, 47, 53] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact closed_of_solve 30 (by decide +kernel)

/-- The prefix `3, 7` is closed for six primes. -/
theorem closed_3_7 : Closed ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩]) (5 - 1) 7 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩]) (5 - 1) 7 =
      [11, 13, 17, 19, 23, 29] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨closed_3_7_11, closed_3_7_13, ?_, ?_, ?_, ?_⟩ <;>
    exact closed_of_solve 30 (by decide +kernel)

/-- Six prime factors with `3` the smallest and all others above `5` is impossible. -/
theorem closed_no_five : Closed [⟨3, 2, false⟩] 5 5 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window [⟨3, 2, false⟩] 5 5 = [7, 11, 13, 17] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨closed_3_7, ?_, ?_, ?_⟩ <;>
    exact closed_of_solve 30 (by decide +kernel)

/-- Six prime factors with `3, 5` the two smallest and all others above `31` is impossible. -/
theorem closed_three_five_big : Closed [⟨3, 2, false⟩, ⟨5, 1, false⟩] 4 31 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window [⟨3, 2, false⟩, ⟨5, 1, false⟩] 4 31 = [37, 41, 43, 47, 53, 59, 61] by
    decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact closed_of_solve 30 (by decide +kernel)

end OddPerfect.OmegaSevenSearch

namespace OddPerfect

open OmegaSevenSearch

private theorem three_mem_of_card_eq_six {N : ℕ} (h : OddPerfect N)
    (h6 : N.primeFactors.card = 6) : 3 ∈ N.primeFactors := by
  by_contra h3
  have := seven_le_card_primeFactors_of_not_three_dvd h
    (fun hd => h3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hd, h.ne_zero⟩))
  omega

private theorem odd_ne_two_of_mem {N q : ℕ} (h : OddPerfect N) (hq : q ∈ N.primeFactors) :
    q ≠ 2 := fun e => h.not_two_dvd (e ▸ Nat.dvd_of_mem_primeFactors hq)

private theorem five_mem_of_card_eq_six {N : ℕ} (h : OddPerfect N)
    (h6 : N.primeFactors.card = 6) : 5 ∈ N.primeFactors := by
  have h3 := three_mem_of_card_eq_six h h6
  by_contra h5
  have H := holds_root3 h h3 (m := 5) (by
    intro q hq hq3
    have hqp := Nat.prime_of_mem_primeFactors hq
    have := odd_ne_two_of_mem h hq
    have := hqp.two_le
    by_contra hle
    interval_cases q <;> simp_all
    norm_num at hqp)
  rw [h6] at H
  exact closed_no_five N H

/-- An odd perfect number with exactly six distinct prime factors is divisible by `15`. -/
theorem fifteen_dvd_of_card_eq_six {N : ℕ} (h : OddPerfect N) (h6 : N.primeFactors.card = 6) :
    15 ∣ N :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (Nat.dvd_of_mem_primeFactors (three_mem_of_card_eq_six h h6))
    (Nat.dvd_of_mem_primeFactors (five_mem_of_card_eq_six h h6))

/-- An odd perfect number with exactly six distinct prime factors is divisible by `3`, by `5`,
and by a prime `p` with `11 ≤ p ≤ 31`. Equivalently, its third smallest prime factor is one of
`11, 13, 17, 19, 23, 29, 31` (it is not `7`, since `105 ∤ N`). -/
theorem exists_prime_dvd_of_card_eq_six {N : ℕ} (h : OddPerfect N)
    (h6 : N.primeFactors.card = 6) :
    3 ∣ N ∧ 5 ∣ N ∧ ∃ p, p.Prime ∧ 11 ≤ p ∧ p ≤ 31 ∧ p ∣ N := by
  have h3 := three_mem_of_card_eq_six h h6
  have h5 := five_mem_of_card_eq_six h h6
  refine ⟨Nat.dvd_of_mem_primeFactors h3, Nat.dvd_of_mem_primeFactors h5, ?_⟩
  by_contra hno
  push Not at hno
  have h7 : 7 ∉ N.primeFactors := by
    intro h7
    apply not_105_dvd h
    have h15 : 15 ∣ N := fifteen_dvd_of_card_eq_six h h6
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h15 (Nat.dvd_of_mem_primeFactors h7)
  have H := holds_root35 h h3 h5 (m := 31) (by
    intro q hq hq3 hq5
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqN := Nat.dvd_of_mem_primeFactors hq
    have := odd_ne_two_of_mem h hq
    have := hqp.two_le
    by_contra hle
    have hlt : ¬ (11 ≤ q ∧ q ≤ 31) := fun hh => absurd hqN (hno q hqp hh.1 hh.2)
    interval_cases q <;> simp_all <;> norm_num at hqp)
  rw [h6] at H
  exact closed_three_five_big N H

end OddPerfect

#print axioms OddPerfect.OmegaSevenSearch.closed_of_solve
#print axioms OddPerfect.OmegaSevenSearch.closed_of_window
#print axioms OddPerfect.OmegaSevenSearch.closed_3_7_11
#print axioms OddPerfect.OmegaSevenSearch.closed_3_7_13
#print axioms OddPerfect.OmegaSevenSearch.closed_3_7
#print axioms OddPerfect.OmegaSevenSearch.closed_no_five
#print axioms OddPerfect.OmegaSevenSearch.closed_three_five_big
#print axioms OddPerfect.fifteen_dvd_of_card_eq_six
#print axioms OddPerfect.exists_prime_dvd_of_card_eq_six
