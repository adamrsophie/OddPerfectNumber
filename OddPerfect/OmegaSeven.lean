import OddPerfect.OmegaSix
import OddPerfect.SpecialPrime

/-!
# Odd perfect numbers with exactly six prime factors

This file works toward the theorem of
C. Pomerance (Odd perfect numbers are divisible by at least seven distinct primes, Acta Arith. 25
(1973/74), 265 to 300): an odd perfect number has at least seven
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
which keeps each check small; a child of more than 1200 search nodes of the Python mirror is
cut further along its prime window or its exponent split (`scripts/OmegaSeven/split.py`).
The step from a state to its children is the enumeration lemma
`OmegaSixSearch.enum_sound`. The full theorem
`7 ≤ ω(N)` is not proved here: the remaining prefixes `3, 5, p` with `11 ≤ p ≤ 31` need over
500 thousand search nodes outside `p = 17`, and the prefix `3, 5, 17` (with `257` and `65537`
next) does not close at all, since the abundancy bounds of the Fermat primes stay below `2` for
every exponent.
-/

set_option Elab.async false

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

/-- One step of the search through its prime window (as in `OddPerfect/OmegaSix.lean`): when
`j ≠ 0` and the window branch of `solve` is taken, it suffices to close every prime `q` of the
window. -/
private theorem solve_of_window {f : ℕ} {l : List Ent} {j m a n : ℕ} (hj : j ≠ 0)
    (hb : bounds l j m ≠ [] ∧ (minB (bounds l j m) ≤ lowB l j m + W ∨ allEx l = true ∨ 2 ≤ j))
    (ha : lowB l j m = a) (hn : minB (bounds l j m) + 1 - lowB l j m = n)
    (h : ∀ q ∈ List.range' a n, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true) :
    solve (f + 1) l j m = true := by
  rw [solve.eq_2, if_neg hj, if_pos hb]
  simp only [Bool.or_eq_true, List.all_eq_true]
  right
  intro q hq
  rw [hn, ha] at hq
  cases hp : isPrimeQ q
  · simp
  · exact Or.inr (h q hq hp)

/-- A window split into two consecutive parts. -/
private theorem win_split {f : ℕ} {l : List Ent} {j a b k n2 n : ℕ}
    (h1 : ∀ q ∈ List.range' a k, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true)
    (h2 : ∀ q ∈ List.range' b n2, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true)
    (hk : a + k = b) (hn : k + n2 = n) :
    ∀ q ∈ List.range' a n, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true := by
  intro q hq
  rw [List.mem_range'_1] at hq
  by_cases hqb : q < b
  · exact h1 q (List.mem_range'_1.mpr ⟨hq.1, by omega⟩)
  · exact h2 q (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

/-- A window of one prime `b`, closed by a separate check of its child state. -/
private theorem win_one {f : ℕ} {l : List Ent} {j b : ℕ}
    (hc : solve f (l ++ [⟨b, kmin b, false⟩]) (j - 1) b = true) :
    ∀ q ∈ List.range' b 1, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true := by
  intro q hq _
  rw [List.mem_range'_1] at hq
  obtain rfl : q = b := by omega
  exact hc

/-- One step of the search through its exponent split: when `j ≠ 0`, the window branch of
`solve` is not taken and some entry is inexact, it suffices to close both split states. -/
private theorem solve_of_split {f : ℕ} {l l1 l2 : List Ent} {j m : ℕ} (hj : j ≠ 0)
    (hb : ¬ (bounds l j m ≠ [] ∧ (minB (bounds l j m) ≤ lowB l j m + W ∨ allEx l = true ∨ 2 ≤ j)))
    (hx : allEx l = false)
    (h1 : l.set (pick l) ⟨(l.getD (pick l) ⟨0, 0, true⟩).p, (l.getD (pick l) ⟨0, 0, true⟩).k,
      true⟩ = l1)
    (h2 : l.set (pick l) ⟨(l.getD (pick l) ⟨0, 0, true⟩).p,
      nextValid (l.getD (pick l) ⟨0, 0, true⟩).p (l.getD (pick l) ⟨0, 0, true⟩).k, false⟩ = l2)
    (s1 : solve f l1 j m = true) (s2 : solve f l2 j m = true) : solve (f + 1) l j m = true := by
  rw [solve.eq_2, if_neg hj, if_neg hb, hx, h1, h2, s1, s2]
  simp

set_option maxRecDepth 100000 in
/-- Window `[14, 859)` (mirror nodes: 1200). -/
private theorem c3_7_11_13xx_w14 : ∀ q ∈ List.range' 14 845,
    isPrimeQ q = true → solve 27 ([⟨3, 2, true⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨13, 1, true⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[859, 1080)` (mirror nodes: 402). -/
private theorem c3_7_11_13xx_w859 : ∀ q ∈ List.range' 859 221,
    isPrimeQ q = true → solve 27 ([⟨3, 2, true⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨13, 1, true⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

/-- The exact case of the split, through its window (mirror nodes: 1603). -/
private theorem c3_7_11_13xx : solve 28 [⟨3, 2, true⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨13, 1, true⟩] 2 13 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split c3_7_11_13xx_w14
      c3_7_11_13xx_w859 rfl rfl)

set_option maxRecDepth 100000 in
/-- The next exponent of the split (mirror nodes: 5). -/
private theorem c3_7_11_13xy : solve 28 [⟨3, 2, true⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨13, 2, false⟩] 2 13 = true := by decide +kernel

/-- The exact case of the split, through its exponent split (mirror nodes: 1609). -/
private theorem c3_7_11_13x : solve 29 [⟨3, 2, true⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨13, 1, false⟩] 2 13 = true :=
  solve_of_split (by decide) (by decide +kernel) (by decide +kernel) rfl rfl c3_7_11_13xx c3_7_11_13xy

set_option maxRecDepth 100000 in
/-- The next exponent of the split (mirror nodes: 1). -/
private theorem c3_7_11_13y : solve 29 [⟨3, 4, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨13, 1, false⟩] 2 13 = true := by decide +kernel

/-- The child `13`, through its exponent split (mirror nodes: 1611). -/
private theorem c3_7_11_13 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨13, 1, false⟩] 2 13 = true :=
  solve_of_split (by decide) (by decide +kernel) (by decide +kernel) rfl rfl c3_7_11_13x c3_7_11_13y

set_option maxRecDepth 100000 in
/-- The child `17` (mirror nodes: 3). -/
private theorem c3_7_11_17 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨17, 1, false⟩] 2 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `19` (mirror nodes: 3). -/
private theorem c3_7_11_19 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨19, 2, false⟩] 2 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `23` (mirror nodes: 7). -/
private theorem c3_7_11_23 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨23, 2, false⟩] 2 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[30, 353)` (mirror nodes: 1192). -/
private theorem c3_7_11_29_w30 : ∀ q ∈ List.range' 30 323,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨29, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[353, 461)` (mirror nodes: 1172). -/
private theorem c3_7_11_29_w353 : ∀ q ∈ List.range' 353 108,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨29, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[461, 631)` (mirror nodes: 1188). -/
private theorem c3_7_11_29_w461 : ∀ q ∈ List.range' 461 170,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨29, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[631, 640)` (mirror nodes: 27). -/
private theorem c3_7_11_29_w631 : ∀ q ∈ List.range' 631 9,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨29, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

/-- The child `29`, through its window (mirror nodes: 3580). -/
private theorem c3_7_11_29 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨29, 1, false⟩] 2 29 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split c3_7_11_29_w30
      (win_split c3_7_11_29_w353
      (win_split c3_7_11_29_w461
      c3_7_11_29_w631 rfl rfl) rfl rfl) rfl rfl)

set_option maxRecDepth 100000 in
/-- Window `[32, 263)` (mirror nodes: 1194). -/
private theorem c3_7_11_31_w32 : ∀ q ∈ List.range' 32 231,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨31, 2, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[263, 369)` (mirror nodes: 586). -/
private theorem c3_7_11_31_w263 : ∀ q ∈ List.range' 263 106,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨31, 2, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

/-- The child `31`, through its window (mirror nodes: 1781). -/
private theorem c3_7_11_31 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨31, 2, false⟩] 2 31 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split c3_7_11_31_w32
      c3_7_11_31_w263 rfl rfl)

set_option maxRecDepth 100000 in
/-- The child `37` (mirror nodes: 884). -/
private theorem c3_7_11_37 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨37, 1, false⟩] 2 37 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `41` (mirror nodes: 882). -/
private theorem c3_7_11_41 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨41, 1, false⟩] 2 41 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `43` (mirror nodes: 541). -/
private theorem c3_7_11_43 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨43, 2, false⟩] 2 43 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `47` (mirror nodes: 405). -/
private theorem c3_7_11_47 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨47, 2, false⟩] 2 47 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `53` (mirror nodes: 382). -/
private theorem c3_7_11_53 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨53, 1, false⟩] 2 53 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `59` (mirror nodes: 136). -/
private theorem c3_7_11_59 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨59, 2, false⟩] 2 59 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `61` (mirror nodes: 129). -/
private theorem c3_7_11_61 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨61, 1, false⟩] 2 61 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `67` (mirror nodes: 59). -/
private theorem c3_7_11_67 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨67, 2, false⟩] 2 67 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `71` (mirror nodes: 63). -/
private theorem c3_7_11_71 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨71, 2, false⟩] 2 71 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `73` (mirror nodes: 13). -/
private theorem c3_7_11_73 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨11, 2, false⟩, ⟨73, 1, false⟩] 2 73 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `17` (mirror nodes: 356). -/
private theorem c3_7_13_17 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨17, 1, false⟩] 2 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The exact case of the split (mirror nodes: 202). -/
private theorem c3_7_13_19x : solve 29 [⟨3, 2, true⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨19, 2, false⟩] 2 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[20, 349)` (mirror nodes: 1185). -/
private theorem c3_7_13_19yx_w20 : ∀ q ∈ List.range' 20 329,
    isPrimeQ q = true → solve 27 ([⟨3, 4, false⟩, ⟨7, 2, false⟩, ⟨13, 1, true⟩, ⟨19, 2, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[349, 374)` (mirror nodes: 88). -/
private theorem c3_7_13_19yx_w349 : ∀ q ∈ List.range' 349 25,
    isPrimeQ q = true → solve 27 ([⟨3, 4, false⟩, ⟨7, 2, false⟩, ⟨13, 1, true⟩, ⟨19, 2, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

/-- The exact case of the split, through its window (mirror nodes: 1274). -/
private theorem c3_7_13_19yx : solve 28 [⟨3, 4, false⟩, ⟨7, 2, false⟩, ⟨13, 1, true⟩, ⟨19, 2, false⟩] 2 19 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split c3_7_13_19yx_w20
      c3_7_13_19yx_w349 rfl rfl)

set_option maxRecDepth 100000 in
/-- The exact case of the split (mirror nodes: 23). -/
private theorem c3_7_13_19yyx : solve 27 [⟨3, 4, true⟩, ⟨7, 2, false⟩, ⟨13, 2, false⟩, ⟨19, 2, false⟩] 2 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[20, 593)` (mirror nodes: 1189). -/
private theorem c3_7_13_19yyyx_w20 : ∀ q ∈ List.range' 20 573,
    isPrimeQ q = true → solve 25 ([⟨3, 6, false⟩, ⟨7, 2, true⟩, ⟨13, 2, false⟩, ⟨19, 2, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[593, 855)` (mirror nodes: 770). -/
private theorem c3_7_13_19yyyx_w593 : ∀ q ∈ List.range' 593 262,
    isPrimeQ q = true → solve 25 ([⟨3, 6, false⟩, ⟨7, 2, true⟩, ⟨13, 2, false⟩, ⟨19, 2, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

/-- The exact case of the split, through its window (mirror nodes: 1960). -/
private theorem c3_7_13_19yyyx : solve 26 [⟨3, 6, false⟩, ⟨7, 2, true⟩, ⟨13, 2, false⟩, ⟨19, 2, false⟩] 2 19 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split c3_7_13_19yyyx_w20
      c3_7_13_19yyyx_w593 rfl rfl)

set_option maxRecDepth 100000 in
/-- The next exponent of the split (mirror nodes: 190). -/
private theorem c3_7_13_19yyyy : solve 26 [⟨3, 6, false⟩, ⟨7, 4, false⟩, ⟨13, 2, false⟩, ⟨19, 2, false⟩] 2 19 = true := by decide +kernel

/-- The next exponent of the split, through its exponent split (mirror nodes: 2151). -/
private theorem c3_7_13_19yyy : solve 27 [⟨3, 6, false⟩, ⟨7, 2, false⟩, ⟨13, 2, false⟩, ⟨19, 2, false⟩] 2 19 = true :=
  solve_of_split (by decide) (by decide +kernel) (by decide +kernel) rfl rfl c3_7_13_19yyyx c3_7_13_19yyyy

/-- The next exponent of the split, through its exponent split (mirror nodes: 2175). -/
private theorem c3_7_13_19yy : solve 28 [⟨3, 4, false⟩, ⟨7, 2, false⟩, ⟨13, 2, false⟩, ⟨19, 2, false⟩] 2 19 = true :=
  solve_of_split (by decide) (by decide +kernel) (by decide +kernel) rfl rfl c3_7_13_19yyx c3_7_13_19yyy

/-- The next exponent of the split, through its exponent split (mirror nodes: 3450). -/
private theorem c3_7_13_19y : solve 29 [⟨3, 4, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨19, 2, false⟩] 2 19 = true :=
  solve_of_split (by decide) (by decide +kernel) (by decide +kernel) rfl rfl c3_7_13_19yx c3_7_13_19yy

/-- The child `19`, through its exponent split (mirror nodes: 3653). -/
private theorem c3_7_13_19 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨19, 2, false⟩] 2 19 = true :=
  solve_of_split (by decide) (by decide +kernel) (by decide +kernel) rfl rfl c3_7_13_19x c3_7_13_19y

set_option maxRecDepth 100000 in
/-- The child `23` (mirror nodes: 1070). -/
private theorem c3_7_13_23 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨23, 2, false⟩] 2 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `29` (mirror nodes: 617). -/
private theorem c3_7_13_29 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨29, 1, false⟩] 2 29 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `31` (mirror nodes: 438). -/
private theorem c3_7_13_31 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨31, 2, false⟩] 2 31 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `37` (mirror nodes: 346). -/
private theorem c3_7_13_37 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨37, 1, false⟩] 2 37 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `41` (mirror nodes: 275). -/
private theorem c3_7_13_41 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨41, 1, false⟩] 2 41 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `43` (mirror nodes: 99). -/
private theorem c3_7_13_43 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨43, 2, false⟩] 2 43 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `47` (mirror nodes: 43). -/
private theorem c3_7_13_47 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨47, 2, false⟩] 2 47 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `53` (mirror nodes: 1). -/
private theorem c3_7_13_53 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨13, 1, false⟩, ⟨53, 1, false⟩] 2 53 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[18, 23)` (mirror nodes: 929). -/
private theorem c3_7_17_w18 : ∀ q ∈ List.range' 18 5,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨17, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[23, 42)` (mirror nodes: 691). -/
private theorem c3_7_17_w23 : ∀ q ∈ List.range' 23 19,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨17, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

/-- The child `17`, through its window (mirror nodes: 1621). -/
private theorem c3_7_17 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨17, 1, false⟩] 3 17 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split c3_7_17_w18
      c3_7_17_w23 rfl rfl)

set_option maxRecDepth 100000 in
/-- The child `19` (mirror nodes: 376). -/
private theorem c3_7_19 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨19, 2, false⟩] 3 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `23` (mirror nodes: 23). -/
private theorem c3_7_23 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨23, 2, false⟩] 3 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `29` (mirror nodes: 1). -/
private theorem c3_7_29 : solve 30 [⟨3, 2, false⟩, ⟨7, 2, false⟩, ⟨29, 1, false⟩] 3 29 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `11` (mirror nodes: 326). -/
private theorem cno5_11 : solve 30 [⟨3, 2, false⟩, ⟨11, 2, false⟩] 4 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `13` (mirror nodes: 4). -/
private theorem cno5_13 : solve 30 [⟨3, 2, false⟩, ⟨13, 1, false⟩] 4 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `17` (mirror nodes: 1). -/
private theorem cno5_17 : solve 30 [⟨3, 2, false⟩, ⟨17, 1, false⟩] 4 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[38, 43)` (mirror nodes: 705). -/
private theorem c35big_37_w38 : ∀ q ∈ List.range' 38 5,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨37, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[43, 47)` (mirror nodes: 884). -/
private theorem c35big_37_w43 : ∀ q ∈ List.range' 43 4,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨37, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[47, 59)` (mirror nodes: 1112). -/
private theorem c35big_37_w47 : ∀ q ∈ List.range' 47 12,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨37, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[59, 82)` (mirror nodes: 626). -/
private theorem c35big_37_w59 : ∀ q ∈ List.range' 59 23,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨37, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

/-- The child `37`, through its window (mirror nodes: 3328). -/
private theorem c35big_37 : solve 30 [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨37, 1, false⟩] 3 37 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split c35big_37_w38
      (win_split c35big_37_w43
      (win_split c35big_37_w47
      c35big_37_w59 rfl rfl) rfl rfl) rfl rfl)

set_option maxRecDepth 100000 in
/-- Window `[42, 53)` (mirror nodes: 860). -/
private theorem c35big_41_w42 : ∀ q ∈ List.range' 42 11,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨41, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[53, 76)` (mirror nodes: 686). -/
private theorem c35big_41_w53 : ∀ q ∈ List.range' 53 23,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨41, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

/-- The child `41`, through its window (mirror nodes: 1547). -/
private theorem c35big_41 : solve 30 [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨41, 1, false⟩] 3 41 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split c35big_41_w42
      c35big_41_w53 rfl rfl)

set_option maxRecDepth 100000 in
/-- The child `43` (mirror nodes: 862). -/
private theorem c35big_43 : solve 30 [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨43, 2, false⟩] 3 43 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `47` (mirror nodes: 302). -/
private theorem c35big_47 : solve 30 [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨47, 2, false⟩] 3 47 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `53` (mirror nodes: 79). -/
private theorem c35big_53 : solve 30 [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨53, 1, false⟩] 3 53 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `59` (mirror nodes: 2). -/
private theorem c35big_59 : solve 30 [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨59, 2, false⟩] 3 59 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The child `61` (mirror nodes: 1). -/
private theorem c35big_61 : solve 30 [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨61, 1, false⟩] 3 61 = true := by decide +kernel

/-- The prefix `3, 7, 11` (as the three smallest prime factors) is closed for six primes. -/
theorem closed_3_7_11 :
    Closed ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩] ++ [⟨11, kmin 11, false⟩]) (5 - 1 - 1) 11 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩] ++ [⟨11, kmin 11, false⟩])
      (5 - 1 - 1) 11 = [13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73] by
    decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨closed_of_solve 30 c3_7_11_13, closed_of_solve 30 c3_7_11_17,
    closed_of_solve 30 c3_7_11_19, closed_of_solve 30 c3_7_11_23, closed_of_solve 30 c3_7_11_29,
    closed_of_solve 30 c3_7_11_31, closed_of_solve 30 c3_7_11_37, closed_of_solve 30 c3_7_11_41,
    closed_of_solve 30 c3_7_11_43, closed_of_solve 30 c3_7_11_47, closed_of_solve 30 c3_7_11_53,
    closed_of_solve 30 c3_7_11_59, closed_of_solve 30 c3_7_11_61, closed_of_solve 30 c3_7_11_67,
    closed_of_solve 30 c3_7_11_71, closed_of_solve 30 c3_7_11_73⟩

/-- The prefix `3, 7, 13` is closed for six primes. -/
theorem closed_3_7_13 :
    Closed ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩] ++ [⟨13, kmin 13, false⟩]) (5 - 1 - 1) 13 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩] ++ [⟨13, kmin 13, false⟩])
      (5 - 1 - 1) 13 = [17, 19, 23, 29, 31, 37, 41, 43, 47, 53] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨closed_of_solve 30 c3_7_13_17, closed_of_solve 30 c3_7_13_19,
    closed_of_solve 30 c3_7_13_23, closed_of_solve 30 c3_7_13_29, closed_of_solve 30 c3_7_13_31,
    closed_of_solve 30 c3_7_13_37, closed_of_solve 30 c3_7_13_41, closed_of_solve 30 c3_7_13_43,
    closed_of_solve 30 c3_7_13_47, closed_of_solve 30 c3_7_13_53⟩

/-- The prefix `3, 7` is closed for six primes. -/
theorem closed_3_7 : Closed ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩]) (5 - 1) 7 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window ([⟨3, 2, false⟩] ++ [⟨7, kmin 7, false⟩]) (5 - 1) 7 =
      [11, 13, 17, 19, 23, 29] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨closed_3_7_11, closed_3_7_13, closed_of_solve 30 c3_7_17, closed_of_solve 30 c3_7_19,
    closed_of_solve 30 c3_7_23, closed_of_solve 30 c3_7_29⟩

/-- Six prime factors with `3` the smallest and all others above `5` is impossible. -/
theorem closed_no_five : Closed [⟨3, 2, false⟩] 5 5 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window [⟨3, 2, false⟩] 5 5 = [7, 11, 13, 17] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨closed_3_7, closed_of_solve 30 cno5_11, closed_of_solve 30 cno5_13,
    closed_of_solve 30 cno5_17⟩

/-- Six prime factors with `3, 5` the two smallest and all others above `31` is impossible. -/
theorem closed_three_five_big : Closed [⟨3, 2, false⟩, ⟨5, 1, false⟩] 4 31 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window [⟨3, 2, false⟩, ⟨5, 1, false⟩] 4 31 = [37, 41, 43, 47, 53, 59, 61] by
    decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨closed_of_solve 30 c35big_37, closed_of_solve 30 c35big_41, closed_of_solve 30 c35big_43,
    closed_of_solve 30 c35big_47, closed_of_solve 30 c35big_53, closed_of_solve 30 c35big_59,
    closed_of_solve 30 c35big_61⟩

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
