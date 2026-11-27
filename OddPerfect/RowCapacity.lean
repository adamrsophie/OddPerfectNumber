import Mathlib

/-!
# Weighted row capacity

A pure counting lemma; it makes no statement about odd perfect numbers.

Fix a number `q`, a finite set `P` of numbers not containing `q` with at most `r` elements, a
weight `w > 0` and a threshold `T` (in the applications `q` and the elements of `P` are primes;
the proof does not use it). For a finite set `V` of numbers above 1 whose prime factors
all lie in `{q} ∪ P`, write `W n = w * v_q(n) + ∑ p ∈ P, v_p(n)`. Then
`T * V.card ≤ ∑ n ∈ V, W n + capDeficit w T r` (`weighted_row_capacity`).

Proof: `T ≤ W n + (T - W n)` for every `n`, and only the `n` with `W n < T` contribute to the
second sum. Such an `n` has `a = v_q(n) < T` and `j = ∑ p ∈ P, v_p(n) < T`, and `(a, j) ≠ (0, 0)`.
For fixed `(a, j)`, the map `n ↦ n.factorization.erase q` is injective and lands in the
functions supported on `P` with sum `j`, of which there are `(P.card + j - 1).choose j`.

The closed values `capDeficit 5 5 4 = 121`, `capDeficit 5 6 4 = 247` and
`capDeficit 6 6 5 = 456` are evaluated by the kernel.

Restricted result; no published source was checked; novelty not verified.
-/

open Finset

namespace OddPerfect

/-- The deficit of the short exponent vectors: one coordinate of weight `w`, and `r`
coordinates of weight 1, threshold `T`. -/
def capDeficit (w T r : ℕ) : ℕ :=
  ∑ a ∈ Finset.range T, ∑ j ∈ Finset.range T,
    if (a = 0 ∧ j = 0) ∨ T ≤ w * a + j then 0 else (T - (w * a + j)) * (j + r - 1).choose j

namespace RowCapacity

/-- The numbers supported on `{q} ∪ P` with fixed `v_q = a` and fixed sum `j` of the
valuations at `P` are at most `(P.card + j - 1).choose j` in number. -/
private theorem card_fiber_le {q a j : ℕ} {P U : Finset ℕ} (hqP : q ∉ P)
    (hU : ∀ n ∈ U, n ≠ 0 ∧ (∀ p ∈ n.primeFactors, p = q ∨ p ∈ P) ∧ n.factorization q = a ∧
      ∑ p ∈ P, n.factorization p = j) :
    U.card ≤ (P.card + j - 1).choose j := by
  rw [← Finset.card_finsuppAntidiag_nat_eq_choose (s := P) j]
  refine Finset.card_le_card_of_injOn (fun n => (n.factorization).erase q) ?_ ?_
  · intro n hn
    obtain ⟨-, hsupp, -, hsum⟩ := hU n hn
    rw [Finset.mem_coe, Finset.mem_finsuppAntidiag]
    constructor
    · rw [← hsum]
      refine Finset.sum_congr rfl fun p hp => ?_
      exact Finsupp.erase_ne (by rintro rfl; exact hqP hp)
    · intro p hp
      rw [Finsupp.support_erase, Finset.mem_erase, Nat.support_factorization] at hp
      rcases hsupp p hp.2 with h | h
      · exact absurd h hp.1
      · exact h
  · intro n hn n' hn' h
    obtain ⟨h0, -, ha, -⟩ := hU n hn
    obtain ⟨h0', -, ha', -⟩ := hU n' hn'
    have h' : (n.factorization).erase q = (n'.factorization).erase q := h
    apply Nat.factorization_inj h0 h0'
    ext p
    by_cases hp : p = q
    · rw [hp, ha, ha']
    · have := DFunLike.congr_fun h' p
      rwa [Finsupp.erase_ne hp, Finsupp.erase_ne hp] at this

/-- The contribution of one class `(a, j)` to the deficit. -/
private theorem fiber_sum_le {w T r q a j : ℕ} {P U : Finset ℕ} (hqP : q ∉ P)
    (hr : P.card ≤ r)
    (hU : ∀ n ∈ U, 1 < n ∧ (∀ p ∈ n.primeFactors, p = q ∨ p ∈ P) ∧ n.factorization q = a ∧
      ∑ p ∈ P, n.factorization p = j ∧
      w * n.factorization q + ∑ p ∈ P, n.factorization p < T) :
    ∑ n ∈ U, (T - (w * n.factorization q + ∑ p ∈ P, n.factorization p)) ≤
      if (a = 0 ∧ j = 0) ∨ T ≤ w * a + j then 0
      else (T - (w * a + j)) * (j + r - 1).choose j := by
  split_ifs with hc
  · refine le_of_eq (Finset.sum_eq_zero fun n hn => ?_)
    exfalso
    obtain ⟨h1, hsupp, ha, hj, hlt⟩ := hU n hn
    rcases hc with ⟨rfl, rfl⟩ | hc
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      have hpos := hp.factorization_pos_of_dvd (show n ≠ 0 by omega) hpn
      rcases hsupp p (Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩) with rfl | hpP
      · omega
      · have hle : n.factorization p ≤ ∑ x ∈ P, n.factorization x := by
          rw [← Finset.add_sum_erase P _ hpP]
          exact Nat.le_add_right _ _
        omega
    · rw [ha, hj] at hlt
      omega
  · have hcard : U.card ≤ (j + r - 1).choose j := by
      refine (card_fiber_le (a := a) hqP fun n hn => ?_).trans (Nat.choose_le_choose j (by omega))
      obtain ⟨h1, hsupp, ha, hj, -⟩ := hU n hn
      exact ⟨by omega, hsupp, ha, hj⟩
    calc ∑ n ∈ U, (T - (w * n.factorization q + ∑ p ∈ P, n.factorization p))
        = ∑ _n ∈ U, (T - (w * a + j)) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          obtain ⟨-, -, ha, hj, -⟩ := hU n hn
          rw [ha, hj]
      _ = U.card * (T - (w * a + j)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (j + r - 1).choose j * (T - (w * a + j)) := Nat.mul_le_mul_right _ hcard
      _ = (T - (w * a + j)) * (j + r - 1).choose j := mul_comm _ _

/-- The total deficit over `V` is at most `capDeficit w T r`. -/
private theorem sum_sub_le_capDeficit {q w T r : ℕ} {P V : Finset ℕ} (hw : 0 < w)
    (hqP : q ∉ P) (hr : P.card ≤ r)
    (hV : ∀ n ∈ V, 1 < n ∧ ∀ p ∈ n.primeFactors, p = q ∨ p ∈ P) :
    ∑ n ∈ V, (T - (w * n.factorization q + ∑ p ∈ P, n.factorization p)) ≤
      capDeficit w T r := by
  classical
  have hfilt : ∑ n ∈ V.filter
        (fun n => w * n.factorization q + ∑ p ∈ P, n.factorization p < T),
        (T - (w * n.factorization q + ∑ p ∈ P, n.factorization p)) =
      ∑ n ∈ V, (T - (w * n.factorization q + ∑ p ∈ P, n.factorization p)) :=
    Finset.sum_filter_of_ne fun n _ h => Nat.sub_ne_zero_iff_lt.mp h
  rw [← hfilt]
  have hmaps : ∀ n ∈ V.filter (fun n => w * n.factorization q + ∑ p ∈ P, n.factorization p < T),
      (fun n => (n.factorization q, ∑ p ∈ P, n.factorization p)) n ∈ range T ×ˢ range T := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have := Nat.le_mul_of_pos_left (n.factorization q) hw
    simp only [Finset.mem_product, Finset.mem_range]
    constructor <;> omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_product]
  unfold capDeficit
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ => ?_
  refine fiber_sum_le hqP hr fun n hn => ?_
  simp only [Finset.mem_filter, Prod.mk.injEq] at hn
  obtain ⟨⟨hnV, hlt⟩, ha, hj⟩ := hn
  exact ⟨(hV n hnV).1, (hV n hnV).2, ha, hj, hlt⟩

end RowCapacity

/-- Weighted row capacity. Let `P` be a set of at most `r` numbers not containing `q`,
`w > 0` and `T` a threshold. For a finite set `V` of numbers above 1 whose prime factors
lie in `{q} ∪ P`, the weighted valuation sums satisfy
`T * V.card ≤ ∑ n ∈ V, (w * v_q(n) + ∑ p ∈ P, v_p(n)) + capDeficit w T r`.
Pure counting lemma, no statement about odd perfect numbers. Restricted result; no published
source was checked; novelty not verified. -/
theorem weighted_row_capacity {q w T r : ℕ} {P V : Finset ℕ} (hw : 0 < w)
    (hqP : q ∉ P) (hr : P.card ≤ r)
    (hV : ∀ n ∈ V, 1 < n ∧ ∀ p ∈ n.primeFactors, p = q ∨ p ∈ P) :
    T * V.card ≤
      ∑ n ∈ V, (w * n.factorization q + ∑ p ∈ P, n.factorization p) + capDeficit w T r := by
  have hA : T * V.card ≤ ∑ n ∈ V, (w * n.factorization q + ∑ p ∈ P, n.factorization p) +
      ∑ n ∈ V, (T - (w * n.factorization q + ∑ p ∈ P, n.factorization p)) := by
    rw [← Finset.sum_add_distrib]
    calc T * V.card = ∑ _n ∈ V, T := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun n _ => by omega
  have hB := RowCapacity.sum_sub_le_capDeficit (T := T) hw hqP hr hV
  omega

/-- Closed value of `capDeficit 5 5 4`. -/
theorem capDeficit_five_five_four : capDeficit 5 5 4 = 121 := by decide +kernel

/-- Closed value of `capDeficit 5 6 4`. -/
theorem capDeficit_five_six_four : capDeficit 5 6 4 = 247 := by decide +kernel

/-- Closed value of `capDeficit 6 6 5`. -/
theorem capDeficit_six_six_five : capDeficit 6 6 5 = 456 := by decide +kernel

end OddPerfect

#print axioms OddPerfect.weighted_row_capacity
#print axioms OddPerfect.capDeficit_five_five_four
#print axioms OddPerfect.capDeficit_five_six_four
#print axioms OddPerfect.capDeficit_six_six_five
