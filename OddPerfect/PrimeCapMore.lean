import OddPerfect.PrimeCap
import Mathlib.NumberTheory.Multiplicity

/-!
# Capacity of the largest prime for prime senders, indices up to 23

Restricted results; no novelty is claimed, and whether they are in the literature was not
verified.

This module extends `OddPerfect.PrimeCap` from indices `l ≤ 11` to indices `l ≤ 23`.

* `card_le_of_monomial_pairs`: let `w 0, …, w (n - 1)` be distinct primes below the prime `P`
  with `w i ^ d ≡ 1 (mod P ^ j)`, `P ∤ d`. A finite family of pairs of exponent vectors
  `(α, β)` with disjoint supports, `∑ α ≤ a`, `∑ β ≤ b` and `a + b ≤ j` has at most `d`
  members: the reduced fractions `∏ w i ^ α i / ∏ w i ^ β i` are distinct `d`-th roots of
  unity modulo `P` (the injection lemma `card_le_of_reduced_pairs`).
* Explicit families give the layer bounds for `d ≤ 23`: at most two senders at level `3`,
  at most two at level `4` (one when `d ≤ 17`), and at most one at level `5` and above.
* `sum_factorization_geom_sum_le_primeSenderCapMore`: for `3 ≤ l ≤ 23` with `P ∤ l` and a
  finite set `U` of primes below `P`, `∑ u ∈ U, v_P(∑ i < l, u ^ i) ≤ primeSenderCapMore l`,
  with the values `25, 33, 38, 47` at `l = 13, 17, 19, 23` (and `15, 29` at `l = 9, 15`).
* `padicValNat_geom_sum_eq_ite_gcd`: the receiver index identity. For an odd prime `P`,
  `1 < u < P`, `d ≥ 1` and `g = gcd(d, P - 1)`, the valuation `v_P(∑ i < d, u ^ i)` is
  `v_P(∑ i < g, u ^ i) + v_P(d)` when `P` divides `∑ i < g, u ^ i`, and `0` otherwise.
* `sum_padicValNat_geom_sum_le_of_gcd`: for prime senders and `3 ≤ g ≤ 23`, the total is at
  most `primeSenderCapMore g + (g - 1) * v_P(d)`.
-/

open Finset

namespace OddPerfect

/-! ## Monomials in prime senders -/

private theorem factorization_prod_pow {n : ℕ} {w : Fin n → ℕ} (hw : Function.Injective w)
    (hp : ∀ i, (w i).Prime) (α : Fin n → ℕ) (k : Fin n) :
    (∏ i, w i ^ α i).factorization (w k) = α k := by
  rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hp i).ne_zero),
    Finsupp.finsetSum_apply]
  simp only [Nat.factorization_pow, (hp _).factorization, Finsupp.smul_apply,
    Finsupp.single_apply, hw.eq_iff, smul_eq_mul]
  simp

private theorem coprime_prod_pow {n : ℕ} {w : Fin n → ℕ} (hw : Function.Injective w)
    (hp : ∀ i, (w i).Prime) {α β : Fin n → ℕ} (h : ∀ i, α i * β i = 0) :
    Nat.Coprime (∏ i, w i ^ α i) (∏ i, w i ^ β i) := by
  refine Nat.Coprime.prod_left fun i _ => Nat.Coprime.prod_right fun k _ => ?_
  by_cases hik : i = k
  · subst hik
    rcases Nat.mul_eq_zero.mp (h i) with h0 | h0 <;> simp [h0]
  · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hp i) (hp k)).mpr (hw.ne hik))

private theorem prod_pow_le {n m : ℕ} {w : Fin n → ℕ} (hw : ∀ i, w i ≤ m) (α : Fin n → ℕ) :
    ∏ i, w i ^ α i ≤ m ^ ∑ i, α i := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => Nat.pow_le_pow_left (hw i) _

private theorem prod_pow_pow_modEq {n d M : ℕ} {w : Fin n → ℕ}
    (hw : ∀ i, w i ^ d ≡ 1 [MOD M]) (α : Fin n → ℕ) : (∏ i, w i ^ α i) ^ d ≡ 1 [MOD M] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hw i)
  push_cast at h
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

/-- Monomial pairs. Let `P` be prime with `P ∤ d`, `1 ≤ j` and `a + b ≤ j`. Let `w` be an
injective family of `n` primes below `P` with `w i ^ d ≡ 1 (mod P ^ j)`. Let `V` be a finite
set of pairs `(α, β)` of exponent vectors with `∑ i, α i ≤ a`, `∑ i, β i ≤ b` and
`α i * β i = 0` for every `i`. Then `#V ≤ d`. -/
theorem card_le_of_monomial_pairs {P d j a b n : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d)
    (hj : 1 ≤ j) (hab : a + b ≤ j) (w : Fin n → ℕ) (hw : Function.Injective w)
    (hwp : ∀ i, (w i).Prime ∧ w i < P ∧ w i ^ d ≡ 1 [MOD P ^ j])
    (V : Finset ((Fin n → ℕ) × (Fin n → ℕ)))
    (hV : ∀ x ∈ V, ∑ i, x.1 i ≤ a ∧ ∑ i, x.2 i ≤ b ∧ ∀ i, x.1 i * x.2 i = 0) : #V ≤ d := by
  have hp : ∀ i, (w i).Prime := fun i => (hwp i).1
  have hle : ∀ i, w i ≤ P - 1 := fun i => by have := (hwp i).2.1; omega
  refine card_le_of_reduced_pairs hP hPd hj V (fun x => ∏ i, w i ^ x.1 i)
    (fun x => ∏ i, w i ^ x.2 i) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have e1 := factorization_prod_pow hw hp x.1 k
      rw [h1, factorization_prod_pow hw hp] at e1
      exact e1.symm
    · have e2 := factorization_prod_pow hw hp x.2 k
      rw [h2, factorization_prod_pow hw hp] at e2
      exact e2.symm
  · intro x _
    exact Finset.prod_pos fun i _ => pow_pos (hp i).pos _
  · intro x hx
    exact coprime_prod_pow hw hp (hV x hx).2.2
  · intro x _
    exact prod_pow_pow_modEq (fun i => (hwp i).2.2) _
  · intro x _
    exact prod_pow_pow_modEq (fun i => (hwp i).2.2) _
  · intro x hx y hy
    have hP1 : 1 ≤ P - 1 := by have := hP.two_le; omega
    have hx1 := (hV x hx).1
    have hy2 := (hV y hy).2.1
    calc (∏ i, w i ^ x.1 i) * ∏ i, w i ^ y.2 i
        ≤ (P - 1) ^ (∑ i, x.1 i) * (P - 1) ^ (∑ i, y.2 i) :=
          Nat.mul_le_mul (prod_pow_le hle _) (prod_pow_le hle _)
      _ = (P - 1) ^ (∑ i, x.1 i + ∑ i, y.2 i) := (pow_add _ _ _).symm
      _ ≤ (P - 1) ^ j := Nat.pow_le_pow_right hP1 (by omega)
      _ < P ^ j := Nat.pow_lt_pow_left (by omega) (by omega)

/-- Layer bound from a family of monomial pairs. With the hypotheses on `V` of
`card_le_of_monomial_pairs` and `d < #V`, a finite set `s` of primes below `P` with
`u ^ d ≡ 1 (mod P ^ j)` has fewer than `n` elements. -/
theorem card_lt_of_monomial_pairs {P d j a b n : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d)
    (hj : 1 ≤ j) (hab : a + b ≤ j) (V : Finset ((Fin n → ℕ) × (Fin n → ℕ)))
    (hV : ∀ x ∈ V, ∑ i, x.1 i ≤ a ∧ ∑ i, x.2 i ≤ b ∧ ∀ i, x.1 i * x.2 i = 0)
    (hVd : d < #V) (s : Finset ℕ) (hs : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P ^ j]) :
    #s < n := by
  by_contra hc
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show n ≤ #s by omega)
  have := card_le_of_monomial_pairs hP hPd hj hab (t.orderEmbOfFin htc)
    (t.orderEmbOfFin htc).injective (fun i => hs _ (hts (t.orderEmbOfFin_mem htc i))) V hV
  omega

/-! ## Explicit families of monomial pairs -/

/-- Three senders, `a = 1`, `b = 2`: twenty four pairs. -/
private def fam313 : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) :=
  {(![0, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 1]), (![0, 0, 0], ![0, 1, 0]),
   (![0, 0, 0], ![1, 0, 0]), (![0, 0, 1], ![0, 0, 0]), (![0, 1, 0], ![0, 0, 0]),
   (![1, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 2]), (![0, 0, 0], ![0, 1, 1]),
   (![0, 0, 0], ![0, 2, 0]), (![0, 0, 0], ![1, 0, 1]), (![0, 0, 0], ![1, 1, 0]),
   (![0, 0, 0], ![2, 0, 0]), (![0, 0, 1], ![0, 1, 0]), (![0, 0, 1], ![1, 0, 0]),
   (![0, 1, 0], ![0, 0, 1]), (![0, 1, 0], ![1, 0, 0]), (![1, 0, 0], ![0, 0, 1]),
   (![1, 0, 0], ![0, 1, 0]), (![0, 0, 1], ![0, 2, 0]), (![0, 0, 1], ![1, 1, 0]),
   (![0, 0, 1], ![2, 0, 0]), (![0, 1, 0], ![0, 0, 2]), (![0, 1, 0], ![1, 0, 1])}

private theorem fam313_card : #fam313 = 24 := by decide +kernel

private theorem fam313_prop : ∀ x ∈ fam313,
    ∑ i, x.1 i ≤ 1 ∧ ∑ i, x.2 i ≤ 2 ∧ ∀ i, x.1 i * x.2 i = 0 := by decide +kernel

/-- Two senders, `a = 2`, `b = 2`: eighteen pairs. -/
private def fam222 : Finset ((Fin 2 → ℕ) × (Fin 2 → ℕ)) :=
  {(![0, 0], ![0, 0]), (![0, 0], ![0, 1]), (![0, 0], ![1, 0]), (![0, 1], ![0, 0]),
   (![1, 0], ![0, 0]), (![0, 0], ![0, 2]), (![0, 0], ![1, 1]), (![0, 0], ![2, 0]),
   (![0, 1], ![1, 0]), (![0, 2], ![0, 0]), (![1, 0], ![0, 1]), (![1, 1], ![0, 0]),
   (![2, 0], ![0, 0]), (![0, 1], ![2, 0]), (![0, 2], ![1, 0]), (![1, 0], ![0, 2]),
   (![2, 0], ![0, 1]), (![0, 2], ![2, 0])}

private theorem fam222_card : #fam222 = 18 := by decide +kernel

private theorem fam222_prop : ∀ x ∈ fam222,
    ∑ i, x.1 i ≤ 2 ∧ ∑ i, x.2 i ≤ 2 ∧ ∀ i, x.1 i * x.2 i = 0 := by decide +kernel

/-- Three senders, `a = 2`, `b = 2`: twenty four pairs. -/
private def fam322 : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) :=
  {(![0, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 1]), (![0, 0, 0], ![0, 1, 0]),
   (![0, 0, 0], ![1, 0, 0]), (![0, 0, 1], ![0, 0, 0]), (![0, 1, 0], ![0, 0, 0]),
   (![1, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 2]), (![0, 0, 0], ![0, 1, 1]),
   (![0, 0, 0], ![0, 2, 0]), (![0, 0, 0], ![1, 0, 1]), (![0, 0, 0], ![1, 1, 0]),
   (![0, 0, 0], ![2, 0, 0]), (![0, 0, 1], ![0, 1, 0]), (![0, 0, 1], ![1, 0, 0]),
   (![0, 0, 2], ![0, 0, 0]), (![0, 1, 0], ![0, 0, 1]), (![0, 1, 0], ![1, 0, 0]),
   (![0, 1, 1], ![0, 0, 0]), (![0, 2, 0], ![0, 0, 0]), (![1, 0, 0], ![0, 0, 1]),
   (![1, 0, 0], ![0, 1, 0]), (![1, 0, 1], ![0, 0, 0]), (![1, 1, 0], ![0, 0, 0])}

private theorem fam322_card : #fam322 = 24 := by decide +kernel

private theorem fam322_prop : ∀ x ∈ fam322,
    ∑ i, x.1 i ≤ 2 ∧ ∑ i, x.2 i ≤ 2 ∧ ∀ i, x.1 i * x.2 i = 0 := by decide +kernel

/-- Two senders, `a = 2`, `b = 3`: twenty four pairs. -/
private def fam223 : Finset ((Fin 2 → ℕ) × (Fin 2 → ℕ)) :=
  {(![0, 0], ![0, 0]), (![0, 0], ![0, 1]), (![0, 0], ![1, 0]), (![0, 1], ![0, 0]),
   (![1, 0], ![0, 0]), (![0, 0], ![0, 2]), (![0, 0], ![1, 1]), (![0, 0], ![2, 0]),
   (![0, 1], ![1, 0]), (![0, 2], ![0, 0]), (![1, 0], ![0, 1]), (![1, 1], ![0, 0]),
   (![2, 0], ![0, 0]), (![0, 0], ![0, 3]), (![0, 0], ![1, 2]), (![0, 0], ![2, 1]),
   (![0, 0], ![3, 0]), (![0, 1], ![2, 0]), (![0, 2], ![1, 0]), (![1, 0], ![0, 2]),
   (![2, 0], ![0, 1]), (![0, 1], ![3, 0]), (![0, 2], ![2, 0]), (![1, 0], ![0, 3])}

private theorem fam223_card : #fam223 = 24 := by decide +kernel

private theorem fam223_prop : ∀ x ∈ fam223,
    ∑ i, x.1 i ≤ 2 ∧ ∑ i, x.2 i ≤ 3 ∧ ∀ i, x.1 i * x.2 i = 0 := by decide +kernel

/-! ## Layer bounds for indices up to 23 -/

/-- Level three: if `P ∤ d`, `d ≤ 23` and `3 ≤ j`, at most two primes `u < P` have
`u ^ d ≡ 1 (mod P ^ j)` (three senders give twenty four monomial pairs). -/
theorem card_le_two_of_primes_level_three {P d j : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d)
    (hd : d ≤ 23) (hj : 3 ≤ j) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P ^ j]) : #s ≤ 2 := by
  have := card_lt_of_monomial_pairs hP hPd (by omega) (show 1 + 2 ≤ j by omega) fam313
    fam313_prop (by rw [fam313_card]; omega) s hs
  omega

/-- Level four, small index: if `P ∤ d`, `d ≤ 17` and `4 ≤ j`, at most one prime `u < P` has
`u ^ d ≡ 1 (mod P ^ j)` (two senders give eighteen monomial pairs). -/
theorem card_le_one_of_primes_level_four {P d j : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d)
    (hd : d ≤ 17) (hj : 4 ≤ j) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P ^ j]) : #s ≤ 1 := by
  have := card_lt_of_monomial_pairs hP hPd (by omega) (show 2 + 2 ≤ j by omega) fam222
    fam222_prop (by rw [fam222_card]; omega) s hs
  omega

/-- Level four: if `P ∤ d`, `d ≤ 23` and `4 ≤ j`, at most two primes `u < P` have
`u ^ d ≡ 1 (mod P ^ j)` (three senders give twenty four monomial pairs). -/
theorem card_le_two_of_primes_level_four {P d j : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d)
    (hd : d ≤ 23) (hj : 4 ≤ j) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P ^ j]) : #s ≤ 2 := by
  have := card_lt_of_monomial_pairs hP hPd (by omega) (show 2 + 2 ≤ j by omega) fam322
    fam322_prop (by rw [fam322_card]; omega) s hs
  omega

/-- Level five: if `P ∤ d`, `d ≤ 23` and `5 ≤ j`, at most one prime `u < P` has
`u ^ d ≡ 1 (mod P ^ j)` (two senders give twenty four monomial pairs). -/
theorem card_le_one_of_primes_level_five {P d j : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d)
    (hd : d ≤ 23) (hj : 5 ≤ j) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P ^ j]) : #s ≤ 1 := by
  have := card_lt_of_monomial_pairs hP hPd (by omega) (show 2 + 3 ≤ j by omega) fam223
    fam223_prop (by rw [fam223_card]; omega) s hs
  omega

/-! ## The capacity for prime senders, indices up to 23 -/

/-- The bound on the number of prime senders in layer `j` for the index `l ≤ 23`: `l - 1` for
`j = 1`; for `j = 2` the largest `r` with `r ^ 2 + r + 1 ≤ l`; for `j = 3`, `1` when `l ≤ 11`
and `2` otherwise; for `j = 4`, `1` when `l ≤ 17` and `2` otherwise; `1` for `j ≥ 5`. -/
def primeLayerCapMore (l j : ℕ) : ℕ :=
  if j = 1 then l - 1
  else if j = 2 then (if l < 7 then 1 else if l < 13 then 2 else if l < 21 then 3 else 4)
  else if j = 3 then (if l ≤ 11 then 1 else 2)
  else if j = 4 then (if l ≤ 17 then 1 else 2)
  else 1

/-- The capacity for prime senders, indices up to 23:
`∑ j ∈ [1, l - 2], primeLayerCapMore l j`. -/
def primeSenderCapMore (l : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 (l - 2), primeLayerCapMore l j

/-- The value `primeSenderCapMore 9 = 15`. -/
theorem primeSenderCapMore_nine : primeSenderCapMore 9 = 15 := by decide
/-- The value `primeSenderCapMore 13 = 25`. -/
theorem primeSenderCapMore_thirteen : primeSenderCapMore 13 = 25 := by decide
/-- The value `primeSenderCapMore 15 = 29`. -/
theorem primeSenderCapMore_fifteen : primeSenderCapMore 15 = 29 := by decide
/-- The value `primeSenderCapMore 17 = 33`. -/
theorem primeSenderCapMore_seventeen : primeSenderCapMore 17 = 33 := by decide
/-- The value `primeSenderCapMore 19 = 38`. -/
theorem primeSenderCapMore_nineteen : primeSenderCapMore 19 = 38 := by decide
/-- The value `primeSenderCapMore 23 = 47`. -/
theorem primeSenderCapMore_twentythree : primeSenderCapMore 23 = 47 := by decide

private theorem layer_cake_more {f n : ℕ} (h : f ≤ n) :
    f = ∑ j ∈ Finset.Icc 1 n, if j ≤ f then 1 else 0 := by
  rw [← Finset.card_filter]
  have : (Finset.Icc 1 n).filter (fun j => j ≤ f) = Finset.Icc 1 f := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]
  omega

/-- The capacity bound for prime senders, indices up to 23. Let `P` be prime, `3 ≤ l ≤ 23`
with `P ∤ l`, and `U` a finite set of primes below `P`. Then
`∑ u ∈ U, v_P(∑ i < l, u ^ i) ≤ primeSenderCapMore l`. -/
theorem sum_factorization_geom_sum_le_primeSenderCapMore {P l : ℕ} (hP : P.Prime)
    (hPl : ¬ P ∣ l) (hl3 : 3 ≤ l) (hl23 : l ≤ 23) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range l, u ^ i).factorization P ≤ primeSenderCapMore l := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 3 := ⟨l - 3, by omega⟩
  set f : ℕ → ℕ := fun u => (∑ i ∈ Finset.range (m + 3), u ^ i).factorization P with hfdef
  have hne : ∀ u, ∑ i ∈ Finset.range (m + 3), u ^ i ≠ 0 := by
    intro u; rw [Finset.sum_range_succ']; simp
  have hdvd : ∀ {u j : ℕ}, j ≤ f u → P ^ j ∣ ∑ i ∈ Finset.range (m + 3), u ^ i := fun h =>
    (hP.pow_dvd_iff_le_factorization (hne _)).mpr h
  have hfle : ∀ u ∈ U, f u ≤ m + 3 - 2 := by
    intro u hu
    obtain ⟨hup, huP⟩ := hU u hu
    have hu1 := hup.one_lt
    by_contra hc
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (hne u)) (hdvd (show m + 2 ≤ f u by omega))
    have h2 := geom_sum_lt_succ_pow (u := u) (by omega) m
    have h3 : (u + 1) ^ (m + 2) ≤ P ^ (m + 2) := Nat.pow_le_pow_left (by omega) _
    omega
  have hlayer : ∀ j, ∀ u ∈ U.filter (fun u => j ≤ f u),
      u.Prime ∧ u < P ∧ u ^ (m + 3) ≡ 1 [MOD P ^ j] := by
    intro j u hu
    obtain ⟨huU, hju⟩ := Finset.mem_filter.mp hu
    obtain ⟨hup, huP⟩ := hU u huU
    exact ⟨hup, huP, pow_modEq_one_of_dvd_geom_sum hup.one_lt.le (hdvd hju)⟩
  have h7 : ∀ r : ℕ, 2 ≤ r → 7 ≤ r ^ 2 + r + 1 := fun r hr => by nlinarith
  have h13 : ∀ r : ℕ, 3 ≤ r → 13 ≤ r ^ 2 + r + 1 := fun r hr => by nlinarith
  have h21 : ∀ r : ℕ, 4 ≤ r → 21 ≤ r ^ 2 + r + 1 := fun r hr => by nlinarith
  have h31 : ∀ r : ℕ, 5 ≤ r → 31 ≤ r ^ 2 + r + 1 := fun r hr => by nlinarith
  calc ∑ u ∈ U, f u
      = ∑ u ∈ U, ∑ j ∈ Finset.Icc 1 (m + 3 - 2), (if j ≤ f u then 1 else 0) :=
        Finset.sum_congr rfl fun u hu => layer_cake_more (hfle u hu)
    _ = ∑ j ∈ Finset.Icc 1 (m + 3 - 2), #(U.filter (fun u => j ≤ f u)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
    _ ≤ primeSenderCapMore (m + 3) := by
        unfold primeSenderCapMore
        refine Finset.sum_le_sum fun j hj => ?_
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        set c := #(U.filter (fun u => j ≤ f u)) with hcdef
        have hsq : 2 = j → c ^ 2 + c + 1 ≤ m + 3 := fun h2 => by
          subst h2
          exact sq_add_add_one_le_of_primes hP hPl _ (hlayer 2)
        have hcube : ∀ k, 3 ≤ k → k ≤ j → ∀ u ∈ U.filter (fun u => j ≤ f u),
            u.Prime ∧ u < P ∧ u ^ (m + 3) ≡ 1 [MOD P ^ k] := fun k hk hkj u hu => by
          obtain ⟨a, b, c⟩ := hlayer j u hu
          exact ⟨a, b, c.of_dvd (Nat.pow_dvd_pow P hkj)⟩
        unfold primeLayerCapMore
        split_ifs with ha hb hb1 hb2 hb3 hc hc1 hd hd1
        · subst ha
          have := card_add_one_le_of_primes hP hPl _ fun u hu => by
            have h := hlayer 1 u hu
            rwa [pow_one] at h
          omega
        · have := hsq hb.symm
          rcases Nat.lt_or_ge c 2 with h | h
          · omega
          · have := h7 _ h; omega
        · have := hsq hb.symm
          rcases Nat.lt_or_ge c 3 with h | h
          · omega
          · have := h13 _ h; omega
        · have := hsq hb.symm
          rcases Nat.lt_or_ge c 4 with h | h
          · omega
          · have := h21 _ h; omega
        · have := hsq hb.symm
          rcases Nat.lt_or_ge c 5 with h | h
          · omega
          · have := h31 _ h; omega
        · subst hc
          exact card_le_one_of_primes_cube hP hPl hc1 _ fun u hu => hcube 3 le_rfl le_rfl u hu
        · subst hc
          exact card_le_two_of_primes_level_three hP hPl hl23 le_rfl _
            fun u hu => hcube 3 le_rfl le_rfl u hu
        · subst hd
          exact card_le_one_of_primes_level_four hP hPl hd1 le_rfl _ (hlayer 4)
        · subst hd
          exact card_le_two_of_primes_level_four hP hPl hl23 le_rfl _ (hlayer 4)
        · exact card_le_one_of_primes_level_five hP hPl hl23 (by omega) _ (hlayer j)

private theorem not_dvd_of_prime_ne' {P l : ℕ} (hP : P.Prime) (hl : l.Prime) (hlP : l ≠ P) :
    ¬ P ∣ l := fun h => hlP ((Nat.prime_dvd_prime_iff_eq hP hl).mp h).symm

/-- Index `13`: for a prime `P ≠ 13` and a finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(∑ i < 13, u ^ i) ≤ 25`. -/
theorem sum_factorization_geom_sum_thirteen_le_of_primes {P : ℕ} (hP : P.Prime)
    (hP13 : P ≠ 13) (U : Finset ℕ) (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range 13, u ^ i).factorization P ≤ 25 := by
  have := sum_factorization_geom_sum_le_primeSenderCapMore hP
    (not_dvd_of_prime_ne' hP (by decide : Nat.Prime 13) hP13.symm) (by norm_num) (by norm_num)
    U hU
  rwa [primeSenderCapMore_thirteen] at this

/-- Index `17`: for a prime `P ≠ 17` and a finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(∑ i < 17, u ^ i) ≤ 33`. -/
theorem sum_factorization_geom_sum_seventeen_le_of_primes {P : ℕ} (hP : P.Prime)
    (hP17 : P ≠ 17) (U : Finset ℕ) (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range 17, u ^ i).factorization P ≤ 33 := by
  have := sum_factorization_geom_sum_le_primeSenderCapMore hP
    (not_dvd_of_prime_ne' hP (by decide : Nat.Prime 17) hP17.symm) (by norm_num) (by norm_num)
    U hU
  rwa [primeSenderCapMore_seventeen] at this

/-- Index `19`: for a prime `P ≠ 19` and a finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(∑ i < 19, u ^ i) ≤ 38`. -/
theorem sum_factorization_geom_sum_nineteen_le_of_primes {P : ℕ} (hP : P.Prime)
    (hP19 : P ≠ 19) (U : Finset ℕ) (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range 19, u ^ i).factorization P ≤ 38 := by
  have := sum_factorization_geom_sum_le_primeSenderCapMore hP
    (not_dvd_of_prime_ne' hP (by decide : Nat.Prime 19) hP19.symm) (by norm_num) (by norm_num)
    U hU
  rwa [primeSenderCapMore_nineteen] at this

/-- Index `23`: for a prime `P ≠ 23` and a finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(∑ i < 23, u ^ i) ≤ 47`. -/
theorem sum_factorization_geom_sum_twentythree_le_of_primes {P : ℕ} (hP : P.Prime)
    (hP23 : P ≠ 23) (U : Finset ℕ) (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range 23, u ^ i).factorization P ≤ 47 := by
  have := sum_factorization_geom_sum_le_primeSenderCapMore hP
    (not_dvd_of_prime_ne' hP (by decide : Nat.Prime 23) hP23.symm) (by norm_num) (by norm_num)
    U hU
  rwa [primeSenderCapMore_twentythree] at this

/-! ## The receiver index identity -/

private theorem geom_sum_mul_pred {u : ℕ} (hu : 1 ≤ u) (n : ℕ) :
    (∑ i ∈ range n, u ^ i) * (u - 1) = u ^ n - 1 := by
  have h := geom_sum_mul (u : ℤ) n
  have h1 : 1 ≤ u ^ n := Nat.one_le_pow _ _ hu
  zify [hu, h1]
  exact_mod_cast h

/-- The receiver index identity. Let `P` be an odd prime, `1 < u < P`, `1 ≤ d` and
`g = gcd(d, P - 1)`. Then `v_P(∑ i < d, u ^ i)` equals `v_P(∑ i < g, u ^ i) + v_P(d)` when
`P ∣ ∑ i < g, u ^ i`, and `0` otherwise. -/
theorem padicValNat_geom_sum_eq_ite_gcd {P u d : ℕ} (hP : P.Prime) (hP2 : P ≠ 2)
    (hu1 : 1 < u) (huP : u < P) (hd : 1 ≤ d) :
    padicValNat P (∑ i ∈ range d, u ^ i) =
      if P ∣ ∑ i ∈ range (Nat.gcd d (P - 1)), u ^ i then
        padicValNat P (∑ i ∈ range (Nat.gcd d (P - 1)), u ^ i) + padicValNat P d
      else 0 := by
  have : Fact P.Prime := ⟨hP⟩
  set g := Nat.gcd d (P - 1) with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  have hgP : g < P := by
    have := Nat.le_of_dvd (by have := hP.two_le; omega) (Nat.gcd_dvd_right d (P - 1))
    omega
  have hgd : g ∣ d := Nat.gcd_dvd_left d (P - 1)
  have hPu1 : ¬ P ∣ u - 1 := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hPu : ¬ P ∣ u := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hne : ∀ n, 1 ≤ n → ∑ i ∈ range n, u ^ i ≠ 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ']
    simp
  -- valuation and divisibility of the geometric sum through `u ^ n - 1`
  have hval : ∀ n, 1 ≤ n → padicValNat P (∑ i ∈ range n, u ^ i) = padicValNat P (u ^ n - 1) := by
    intro n hn
    rw [← geom_sum_mul_pred hu1.le n, padicValNat.mul (hne n hn) (by omega),
      padicValNat.eq_zero_of_not_dvd hPu1, add_zero]
  have hdiv : ∀ n, P ∣ ∑ i ∈ range n, u ^ i ↔ P ∣ u ^ n - 1 := by
    intro n
    rw [← geom_sum_mul_pred hu1.le n]
    constructor
    · exact fun h => dvd_mul_of_dvd_left h _
    · intro h
      rcases (Nat.Prime.dvd_mul hP).mp h with h | h
      · exact h
      · exact absurd h hPu1
  have hzmod : ∀ n, P ∣ u ^ n - 1 ↔ (u : ZMod P) ^ n = 1 := by
    intro n
    rw [← Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega)), ← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact eq_comm
  have hu0 : (u : ZMod P) ≠ 0 := fun h => hPu ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hiff : P ∣ ∑ i ∈ range d, u ^ i ↔ P ∣ ∑ i ∈ range g, u ^ i := by
    rw [hdiv, hdiv, hzmod, hzmod, hgdef, pow_gcd_eq_one]
    exact ⟨fun h => ⟨h, ZMod.pow_card_sub_one_eq_one hu0⟩, fun h => h.1⟩
  split_ifs with h
  · rw [hval d hd, hval g hg0]
    have hPg : P ∣ u ^ g - 1 := (hdiv g).mp h
    have hug : 1 < u ^ g := Nat.one_lt_pow hg0.ne' hu1
    have hPug : ¬ P ∣ u ^ g := fun h' => hPu (hP.dvd_of_dvd_pow h')
    have hdg0 : d / g ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hgd) hg0).ne'
    have hlte := padicValNat.pow_sub_pow (hP.odd_of_ne_two hP2) hug (by simpa using hPg) hPug
      hdg0
    rw [one_pow, ← pow_mul, Nat.mul_div_cancel' hgd] at hlte
    rw [hlte]
    congr 1
    have hm := padicValNat.mul (p := P) hg0.ne' hdg0
    rw [Nat.mul_div_cancel' hgd, padicValNat.eq_zero_of_not_dvd (n := g) (fun h' => by
      have := Nat.le_of_dvd hg0 h'
      omega), zero_add] at hm
    exact hm.symm
  · exact padicValNat.eq_zero_of_not_dvd fun h' => h (hiff.mp h')

/-- Receiver index `1`. If `P` is an odd prime, `1 < u < P`, `1 ≤ d` and `gcd(d, P - 1) = 1`,
then `P ∤ ∑ i < d, u ^ i`: the valuation is `0`. -/
theorem padicValNat_geom_sum_eq_zero_of_gcd_eq_one {P u d : ℕ} (hP : P.Prime) (hP2 : P ≠ 2)
    (hu1 : 1 < u) (huP : u < P) (hd : 1 ≤ d) (hg : Nat.gcd d (P - 1) = 1) :
    padicValNat P (∑ i ∈ range d, u ^ i) = 0 := by
  rw [padicValNat_geom_sum_eq_ite_gcd hP hP2 hu1 huP hd, hg]
  have : ¬ P ∣ ∑ i ∈ range 1, u ^ i := by
    simp only [Finset.sum_range_one, pow_zero]
    exact hP.not_dvd_one
  rw [if_neg this]

/-- Receiver index capacity for prime senders. Let `P` be an odd prime, `1 ≤ d`, and
`g = gcd(d, P - 1)` with `3 ≤ g ≤ 23`. For a finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(∑ i < d, u ^ i) ≤ primeSenderCapMore g + (g - 1) * v_P(d)`. -/
theorem sum_padicValNat_geom_sum_le_of_gcd {P d : ℕ} (hP : P.Prime) (hP2 : P ≠ 2)
    (hd : 1 ≤ d) (hg3 : 3 ≤ Nat.gcd d (P - 1)) (hg23 : Nat.gcd d (P - 1) ≤ 23)
    (U : Finset ℕ) (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, padicValNat P (∑ i ∈ range d, u ^ i) ≤
      primeSenderCapMore (Nat.gcd d (P - 1)) + (Nat.gcd d (P - 1) - 1) * padicValNat P d := by
  classical
  set g := Nat.gcd d (P - 1) with hgdef
  have hgP : g < P := by
    have := Nat.le_of_dvd (by have := hP.two_le; omega) (Nat.gcd_dvd_right d (P - 1))
    omega
  have hPg : ¬ P ∣ g := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  set V := U.filter (fun u => P ∣ ∑ i ∈ range g, u ^ i) with hVdef
  have hsum : ∑ u ∈ U, padicValNat P (∑ i ∈ range d, u ^ i) =
      ∑ u ∈ V, padicValNat P (∑ i ∈ range g, u ^ i) + #V * padicValNat P d := by
    rw [Finset.sum_congr rfl fun u hu => padicValNat_geom_sum_eq_ite_gcd hP hP2
      (hU u hu).1.one_lt (hU u hu).2 hd, ← Finset.sum_filter, Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul]
  have hcap : ∑ u ∈ V, padicValNat P (∑ i ∈ range g, u ^ i) ≤ primeSenderCapMore g := by
    have h1 := sum_factorization_geom_sum_le_primeSenderCapMore hP hPg hg3 hg23 U hU
    have h2 : ∑ u ∈ V, padicValNat P (∑ i ∈ range g, u ^ i) ≤
        ∑ u ∈ U, padicValNat P (∑ i ∈ range g, u ^ i) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    simp only [Nat.factorization_def _ hP] at h1
    omega
  have hcard : #V + 1 ≤ g := card_add_one_le_of_primes hP hPg V fun u hu => by
    obtain ⟨huU, hdv⟩ := Finset.mem_filter.mp hu
    exact ⟨(hU u huU).1, (hU u huU).2,
      pow_modEq_one_of_dvd_geom_sum (hU u huU).1.one_lt.le hdv⟩
  rw [hsum]
  have := Nat.mul_le_mul_right (padicValNat P d) (show #V ≤ g - 1 by omega)
  omega

end OddPerfect

#print axioms OddPerfect.card_le_of_monomial_pairs
#print axioms OddPerfect.card_lt_of_monomial_pairs
#print axioms OddPerfect.card_le_two_of_primes_level_three
#print axioms OddPerfect.card_le_one_of_primes_level_four
#print axioms OddPerfect.card_le_two_of_primes_level_four
#print axioms OddPerfect.card_le_one_of_primes_level_five
#print axioms OddPerfect.primeSenderCapMore_nine
#print axioms OddPerfect.primeSenderCapMore_thirteen
#print axioms OddPerfect.primeSenderCapMore_fifteen
#print axioms OddPerfect.primeSenderCapMore_seventeen
#print axioms OddPerfect.primeSenderCapMore_nineteen
#print axioms OddPerfect.primeSenderCapMore_twentythree
#print axioms OddPerfect.sum_factorization_geom_sum_le_primeSenderCapMore
#print axioms OddPerfect.sum_factorization_geom_sum_thirteen_le_of_primes
#print axioms OddPerfect.sum_factorization_geom_sum_seventeen_le_of_primes
#print axioms OddPerfect.sum_factorization_geom_sum_nineteen_le_of_primes
#print axioms OddPerfect.sum_factorization_geom_sum_twentythree_le_of_primes
#print axioms OddPerfect.padicValNat_geom_sum_eq_ite_gcd
#print axioms OddPerfect.padicValNat_geom_sum_eq_zero_of_gcd_eq_one
#print axioms OddPerfect.sum_padicValNat_geom_sum_le_of_gcd
