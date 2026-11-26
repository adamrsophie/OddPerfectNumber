import OddPerfect.EulerIndexPairCofactor
import OddPerfect.EulerIndexPairSmallPairs
import OddPerfect.EulerIndexPairSeven

/-!
# Two prime Euler index: one frame for the emitter and the receiver

Restricted result; no published source was checked; novelty not verified.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. The landed theorems on this family each choose their own labeling `(t, u)` of
`{r, s}`, with the emitter row `σ(t ^ e) = q * u ^ v` and the return row `σ(u ^ f) = t ^ j`.

* `PairFrame N q r s t u`: the orientation facts (`{t, u} = {r, s}`, `t ≠ u`, both prime,
  the emitter row, the return row with `j` positive and odd).
* `PairFrame.eq_of_emit`, `PairFrame.unique`: the labeling is determined. A swapped labeling
  gives `q ∣ t ^ j`, so `q = t`, and then `t ∣ σ(t ^ e)`, which is false.
* `exists_pairFrame`: in the family a frame exists.
* `PairFrame.v_eq`, `PairFrame.j_eq`: the exponents `v` and `j` of the rows are determined.
* Transfer theorems `PairFrame.cofactor`, `PairFrame.t_count`, `PairFrame.character`,
  `PairFrame.emitter_ge`, `PairFrame.emitter_ten_all`, `PairFrame.palette`: the conclusions
  of the landed theorems for the labeling of a given frame. Together they contain every
  conjunct of `eulerIndex_pair_rows`, `eulerIndex_pair_rows_all`,
  `eulerIndex_pair_pure_exponent_odd`, `eulerIndex_pair_prime_length`,
  `eulerIndex_pair_short_rows` and `eulerIndex_pair_emitter_ten` as well.

The family is not excluded by this. The odd perfect number conjecture is open, and nothing
here decides it.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The orientation of the two prime Euler index `{r, s}`: `t` is the emitter, with row
`σ(t ^ e) = q * u ^ v`, and `u` the receiver, with return row `σ(u ^ f) = t ^ j`, `j` odd. -/
structure PairFrame (N q r s t u : ℕ) : Prop where
  pair : ({t, u} : Finset ℕ) = {r, s}
  ne : t ≠ u
  t_prime : t.Prime
  u_prime : u.Prime
  emit : ∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v
  ret : ∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j

variable {N q m r s t u : ℕ}

namespace PairFrame

/-- Any labeling of `{r, s}` that carries an emitter row is the labeling of the frame. -/
theorem eq_of_emit (F : PairFrame N q r s t u) (hq : q.Prime) {t' u' v' : ℕ}
    (hp : ({t', u'} : Finset ℕ) = {r, s}) (hne : t' ≠ u')
    (hA : σ 1 (t' ^ N.factorization t') = q * u' ^ v') : t' = t ∧ u' = u := by
  have ht' : t' ∈ ({t, u} : Finset ℕ) := by rw [F.pair, ← hp]; simp
  have hu' : u' ∈ ({t, u} : Finset ℕ) := by rw [F.pair, ← hp]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht' hu'
  rcases ht' with h1 | h1
  · refine ⟨h1, ?_⟩
    rcases hu' with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact h2
  · exfalso
    have h2 : u' = t := by
      rcases hu' with h2 | h2
      · exact h2
      · exact absurd (h1.trans h2.symm) hne
    obtain ⟨v, hv⟩ := F.emit
    obtain ⟨j, -, -, hj⟩ := F.ret
    rw [h1, h2, hj] at hA
    have hqt : q ∣ t := hq.dvd_of_dvd_pow (Dvd.intro _ hA.symm)
    have hqt' := (Nat.prime_dvd_prime_iff_eq hq F.t_prime).mp hqt
    have hdvd : t ∣ σ 1 (t ^ N.factorization t) := by
      rw [hv, hqt']; exact Dvd.intro _ rfl
    exact (Nat.Prime.coprime_iff_not_dvd F.t_prime).mp
      (coprime_sigma_prime_pow F.t_prime _).symm hdvd

/-- Two frames for the same `N q r s` have the same emitter and the same receiver. -/
theorem unique {t' u' : ℕ} (F : PairFrame N q r s t u) (G : PairFrame N q r s t' u')
    (hq : q.Prime) : t' = t ∧ u' = u := by
  obtain ⟨v', hA⟩ := G.emit
  exact F.eq_of_emit hq G.pair G.ne hA

/-- The exponent `v` of the emitter row is determined. -/
theorem v_eq (F : PairFrame N q r s t u) (hq : q.Prime) {v v' : ℕ}
    (hv : σ 1 (t ^ N.factorization t) = q * u ^ v)
    (hv' : σ 1 (t ^ N.factorization t) = q * u ^ v') : v = v' := by
  have h : u ^ v = u ^ v' := Nat.eq_of_mul_eq_mul_left hq.pos (hv.symm.trans hv')
  exact Nat.pow_right_injective F.u_prime.two_le h

/-- The exponent `j` of the return row is determined. -/
theorem j_eq (F : PairFrame N q r s t u) {j j' : ℕ}
    (hj : σ 1 (u ^ N.factorization u) = t ^ j)
    (hj' : σ 1 (u ^ N.factorization u) = t ^ j') : j = j' :=
  Nat.pow_right_injective F.t_prime.two_le (hj.symm.trans hj')

end PairFrame

/-- In the two prime Euler index family a frame exists. -/
theorem exists_pairFrame (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, PairFrame N q r s t u := by
  obtain ⟨t, u, hp, hne, hA, hB, -⟩ := eulerIndex_pair_cofactor h hq hN hqm hr hs hrs hJ
  have hmem : ∀ x ∈ ({t, u} : Finset ℕ), x.Prime := by
    intro x hx
    rw [hp] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hr
    · exact hs
  exact ⟨t, u, hp, hne, hmem t (by simp), hmem u (by simp), hA, hB⟩

namespace PairFrame

/-- Transfer of `eulerIndex_pair_cofactor` (which contains `eulerIndex_pair_rows`,
`eulerIndex_pair_rows_all` and `eulerIndex_pair_pure_exponent_odd`) to the frame. -/
theorem cofactor (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      (eulerIndex q 1 m).factorization t = N.factorization t ∧
      (N.factorization u + 1).Prime ∧ orderOf (u : ZMod t) = N.factorization u + 1 ∧
      t % (2 * (N.factorization u + 1)) = 1 ∧
      ((N.factorization t + 1).Prime ∨ ∃ p, p.Prime ∧ N.factorization t + 1 = p ^ 2) ∧
      (orderOf (q : ZMod t) = 1 ∨ orderOf (q : ZMod t) = N.factorization u + 1) ∧
      (∀ p ∈ N.primeFactors, p ≠ q → p ≠ t → p ≠ u →
        (∃ x y, σ 1 (p ^ N.factorization p) = t ^ x * u ^ y) ∧
        p ^ N.factorization p ∣ q + 1 ∧
        ((N.factorization p + 1).Prime ∨ ∃ P, P.Prime ∧ N.factorization p + 1 = P ^ 2)) ∧
      ∃ d, q + 1 = 2 * u ^ d *
        (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2 := by
  obtain ⟨t', u', hp, hne, ⟨v', hA⟩, rest⟩ := eulerIndex_pair_cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨rfl, rfl⟩ := F.eq_of_emit hq hp hne hA
  exact ⟨⟨v', hA⟩, rest⟩

/-- Transfer of `eulerIndex_pair_t_count` (the ledger of the exponent of `t`) to the frame. -/
theorem t_count (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧ ¬ t ∣ q + 1 ∧
      orderOf (u : ZMod t) = N.factorization u + 1 ∧
      ∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j ∧
      N.factorization t = j + ∑ p ∈ N.primeFactors \ {q, r, s},
        (σ 1 (p ^ N.factorization p)).factorization t ∧
      Odd (∑ p ∈ N.primeFactors \ {q, r, s}, (σ 1 (p ^ N.factorization p)).factorization t) ∧
      (∃ p ∈ N.primeFactors \ {q, r, s}, t ∣ σ 1 (p ^ N.factorization p)) ∧
      t ∣ σ 1 ((∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2) ∧
      ∃ b, σ 1 ((∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2) =
        t ^ (∑ p ∈ N.primeFactors \ {q, r, s}, (σ 1 (p ^ N.factorization p)).factorization t) *
          u ^ b := by
  obtain ⟨t', u', hp, hne, ⟨v', hA⟩, rest⟩ := eulerIndex_pair_t_count h hq hN hqm hr hs hrs hJ
  obtain ⟨rfl, rfl⟩ := F.eq_of_emit hq hp hne hA
  exact ⟨⟨v', hA⟩, rest⟩

/-- Transfer of `eulerIndex_pair_character` to the frame. -/
theorem character (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ¬ t ∣ q + 1 ∧
      (∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧
      ∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v ∧ ((q * u ^ v : ℕ) : ZMod t) = 1 ∧
        IsSquare ((2 * (1 + u ^ v) : ℕ) : ZMod t) ∧
        ((2 * (1 + u ^ v) : ℕ) : ZMod t) ≠ 0 := by
  obtain ⟨t', u', hp, hne, hd, hj, v', hA, rest⟩ :=
    eulerIndex_pair_character h hq hN hqm hr hs hrs hJ
  obtain ⟨rfl, rfl⟩ := F.eq_of_emit hq hp hne hA
  exact ⟨hd, hj, v', hA, rest⟩

/-- Transfer of `eulerIndex_pair_emitter_ge` (lower bound on `t`) to the frame. -/
theorem emitter_ge (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      (N.factorization u + 1).Prime ∧ t % (2 * (N.factorization u + 1)) = 1 ∧
      ((t = 43 ∧ N.factorization u = 6) ∨ 53 ≤ t) := by
  obtain ⟨t', u', hp, hne, ⟨v', hA⟩, rest⟩ := eulerIndex_pair_emitter_ge h hq hN hqm hr hs hrs hJ
  obtain ⟨rfl, rfl⟩ := F.eq_of_emit hq hp hne hA
  exact ⟨⟨v', hA⟩, rest⟩

/-- Transfer of `eulerIndex_pair_emitter_ten_all` (which contains
`eulerIndex_pair_emitter_ten`, `eulerIndex_pair_short_rows` and
`eulerIndex_pair_prime_length`) to the frame: the two branches `v = 0` and `v = 1`. -/
theorem emitter_ten_all (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    t.Prime ∧ t ≠ 2 ∧ ∃ v j,
      σ 1 (t ^ N.factorization t) = q * u ^ v ∧ 0 < j ∧ Odd j ∧
      σ 1 (u ^ N.factorization u) = t ^ j ∧ j < N.factorization t ∧
      (N.factorization t + 1).Prime ∧ 10 ≤ N.factorization t ∧
      ((v = 0 ∧ σ 1 (t ^ N.factorization t) = q ∧ 10 ≤ N.factorization t) ∨
        (v = 1 ∧ u = N.factorization t + 1 ∧ 11 ≤ u ∧ t % u = 1 ∧ q % u = 1 ∧
          q + 1 = 2 * (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2)) := by
  obtain ⟨t', u', hp, hne, ht, ht2, v', j', hA, rest⟩ :=
    eulerIndex_pair_emitter_ten_all h hq hN hqm hr hs hrs hJ
  obtain ⟨rfl, rfl⟩ := F.eq_of_emit hq hp hne hA
  exact ⟨ht, ht2, v', j', hA, rest⟩

/-- Transfer of `eulerIndex_pair_palette` to the frame. -/
theorem palette (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hexp : ∀ p ∈ ({r, s} : Finset ℕ), N.factorization p = 2 ∨ N.factorization p = 4) :
    (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧ ¬ t ∣ q + 1 ∧
      N.factorization u = 4 ∧ ∃ j, 3 ≤ j ∧ Odd j ∧ σ 1 (u ^ 4) = t ^ j := by
  obtain ⟨t', u', hp, hne, ⟨v', hA⟩, rest⟩ :=
    eulerIndex_pair_palette h hq hN hqm hr hs hrs hJ hexp
  obtain ⟨rfl, rfl⟩ := F.eq_of_emit hq hp hne hA
  exact ⟨⟨v', hA⟩, rest⟩

end PairFrame

end OddPerfect

#print axioms OddPerfect.PairFrame.eq_of_emit
#print axioms OddPerfect.PairFrame.unique
#print axioms OddPerfect.PairFrame.v_eq
#print axioms OddPerfect.PairFrame.j_eq
#print axioms OddPerfect.exists_pairFrame
#print axioms OddPerfect.PairFrame.cofactor
#print axioms OddPerfect.PairFrame.t_count
#print axioms OddPerfect.PairFrame.character
#print axioms OddPerfect.PairFrame.emitter_ge
#print axioms OddPerfect.PairFrame.emitter_ten_all
#print axioms OddPerfect.PairFrame.palette
