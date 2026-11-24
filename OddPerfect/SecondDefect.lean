import OddPerfect.ExcessDefect
import OddPerfect.EscapeRowUnique

/-!
# The second defect identity: the count with slope 7/2

Let `N` be an odd perfect number with special prime `q` of exponent `a`, let
`T = ∑ (v_p(N) / 2 - 1)` over the prime factors `p ≠ q` be the total excess, `b = v_3(N)` and
`s = v_3(σ(q ^ a))`. The library proves
`2 * ω(N) + 3 * s ≤ 7 * T + 13 + #(rows through q)`
(`two_mul_card_primeFactors_add_three_mul_le`). This file turns that inequality into an
identity between counts, in the style of `card_primeFactors_add_two_mul_add_defect_eq`. With
`H` the number of escape rows and `A` the number of rows through `q`,

`2 * ω(N) + 3 * s + D = 7 * T + 9 + 2 * H + A`
(`two_mul_card_primeFactors_add_three_mul_add_defect_eq`), where the defect `D` collects

* `squareSurplusTwo`: `∑ (recvWeight p - 2)` over the square primes;
* `highRecvWeight`: the weight that `q` and the primes of exponent at least 4 send to the
  ordinary receivers;
* `receiverSlack`: the ordinary receivers that are not the core of a free row;
* `3 * highThreeWeight`, `5 * highExcessDefect`, `twoModThreeMass`, `highTwoModThree` and
  `threeExcessDefect`, from the primes of exponent at least 4;
* `7` when `3 ∤ N` and `1` when `v_3(N) = 2`.

The proof combines the row split of the square primes, the ledger at the ordinary receivers,
a residue identity prime by prime, and the ledger at 3. Through rows and escape rows each send
weight at least 1 to `q` (`card_throughRows_add_card_escapeRows_le`), so with at most one escape
row (`card_escapeRows_le_one_all`) the identity gives
`2 * ω(N) + 3 * s ≤ 7 * T + 10 + a`, and `2 * ω(N) + 3 * s ≤ 7 * T + 9` when `q ≡ 2 (mod 3)`.
The module `OddPerfect/ExcessSupportEleven.lean`, whose landing is in progress, proves the
inequality with the constant 11.

These are identities and inequalities between counts. Neither the total excess nor the special
exponent is bounded here, and the odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- `∑ (recvWeight p - 2)` over the square primes (natural subtraction). -/
def squareSurplusTwo (N q : ℕ) : ℕ := ∑ p ∈ squarePrimes N q, (recvWeight N q p - 2)

/-- Receivers that are not the core of a free row: `#ordReceivers - #freeRows`. -/
def receiverSlack (N q : ℕ) : ℕ := (ordReceivers N q).card - (freeRows N q).card

/-- The number of ordinary primes of exponent at least 4 that are 2 modulo 3. -/
def highTwoModThree (N q : ℕ) : ℕ := ((highPrimes N q).filter fun p => p % 3 = 2).card

private theorem three_ne_special_sd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : (3 : ℕ) ≠ q := by
  rintro rfl
  have := (special_mod_four h hq hodd).1
  omega

/-- The row split of the square primes:
`2 * #S + squareSurplusTwo = ∑ recvWeight + 2 * H + #throughRows + #freeRows`. -/
theorem two_mul_card_squarePrimes_add_surplus_eq {N q : ℕ} (h : OddPerfect N) :
    2 * (squarePrimes N q).card + squareSurplusTwo N q =
      ∑ p ∈ squarePrimes N q, recvWeight N q p + 2 * (escapeRows N q).card +
        (throughRows N q).card + (freeRows N q).card := by
  have hpt : ∀ p ∈ squarePrimes N q, 2 + (recvWeight N q p - 2) = recvWeight N q p +
      2 * (if ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q then 1 else 0) +
      (if recvWeight N q p = 1 ∧ sigmaWeight N p q ≠ 0 then 1 else 0) +
      (if recvWeight N q p = 1 ∧ sigmaWeight N p q = 0 then 1 else 0) := by
    intro p hp
    by_cases hesc : ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q
    · have h0 := recvWeight_eq_zero_of_mem_escapeRows (Finset.mem_filter.mpr ⟨hp, hesc⟩)
      rw [if_pos hesc]
      split_ifs <;> omega
    · have := one_le_recvWeight h hp hesc
      rw [if_neg hesc]
      split_ifs <;> omega
  have hsum := Finset.sum_congr rfl hpt
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hsum
  have e1 : (throughRows N q).card = ∑ p ∈ squarePrimes N q,
      (if recvWeight N q p = 1 ∧ sigmaWeight N p q ≠ 0 then 1 else 0) := Finset.card_filter _ _
  have e2 : (freeRows N q).card = ∑ p ∈ squarePrimes N q,
      (if recvWeight N q p = 1 ∧ sigmaWeight N p q = 0 then 1 else 0) := Finset.card_filter _ _
  have e3 : (escapeRows N q).card = ∑ p ∈ squarePrimes N q,
      (if ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q then 1 else 0) := Finset.card_filter _ _
  unfold squareSurplusTwo
  omega

/-- The second ledger at the receivers:
`2 * #S + squareSurplusTwo + highRecvWeight + receiverSlack =
2 * H + #throughRows + #ordReceivers + ∑ v_r(N)` over the ordinary receivers. -/
theorem receiver_ledger_two {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    2 * (squarePrimes N q).card + squareSurplusTwo N q + highRecvWeight N q +
        receiverSlack N q =
      2 * (escapeRows N q).card + (throughRows N q).card + (ordReceivers N q).card +
        ∑ r ∈ ordReceivers N q, N.factorization r := by
  have h1 := two_mul_card_squarePrimes_add_surplus_eq (q := q) h
  have h2 := sum_primeFactors_recvWeight_eq (q := q) h
  rw [sum_primeFactors_split h hq hodd (recvWeight N q)] at h2
  have hF := card_freeRows_le (N := N) (q := q) h
  unfold highRecvWeight receiverSlack
  omega

private theorem sum_ite_eq_three_sd (N : ℕ) (g : ℕ → ℕ) (hg : g 0 = 0) :
    ∑ p ∈ N.primeFactors, (if p = 3 then g (N.factorization p) else 0) =
      g (N.factorization 3) := by
  rw [Finset.sum_ite_eq']
  split_ifs with h3
  · rfl
  · rw [Finsupp.notMem_support_iff.mp (by rw [Nat.support_factorization]; exact h3), hg]

/-- The residue identity, prime by prime: with `C` the square primes that are 1 modulo 3, `E`
the ordinary primes of exponent at least 4 and `b = v_3(N)`,
`∑ v_r(N) + #receivers + 2 * #E + 5 * highExcessDefect + twoModThreeMass + highTwoModThree +
((3 * b if b ≥ 4) + threeExcessDefect) = 3 * #C + 7 * T + (7 if b ≥ 4)`. -/
theorem residue_identity_seven {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ∑ r ∈ ordReceivers N q, N.factorization r + (ordReceivers N q).card +
        2 * (highPrimes N q).card + 5 * highExcessDefect N q + twoModThreeMass N q +
        highTwoModThree N q +
        ((if 4 ≤ N.factorization 3 then 3 * N.factorization 3 else 0) + threeExcessDefect N) =
      3 * ((squarePrimes N q).filter fun p => p % 3 = 1).card +
        7 * ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) +
        (if 4 ≤ N.factorization 3 then 7 else 0) := by
  have h3q := three_ne_special_sd h hq hodd
  have hpt : ∀ p ∈ N.primeFactors,
      (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then N.factorization p else 0) +
        (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then 1 else 0) +
        2 * (if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0) +
        5 * (if p ≠ q ∧ 4 ≤ N.factorization p ∧ p ≠ 3 then N.factorization p / 2 - 2
          else 0) +
        (if p ≠ q ∧ 4 ≤ N.factorization p ∧ p % 3 = 2 then N.factorization p else 0) +
        (if p ≠ q ∧ 4 ≤ N.factorization p ∧ p % 3 = 2 then 1 else 0) +
        (if p = 3 then (if 4 ≤ N.factorization p then 3 * N.factorization p else 0) +
          (N.factorization p / 2 - 2) else 0) =
      3 * (if (p ≠ q ∧ N.factorization p = 2) ∧ p % 3 = 1 then 1 else 0) +
        7 * (if p ≠ q then N.factorization p / 2 - 1 else 0) +
        (if p = 3 then (if 4 ≤ N.factorization p then 7 else 0) else 0) := by
    intro p hp
    by_cases hpq : p = q
    · subst hpq
      split_ifs <;> omega
    · obtain ⟨j, hj, hpos⟩ := even_pos_factorization_of_ne h hq hodd hp hpq
      have hp3 : p = 3 ∨ p % 3 ≠ 0 := by
        by_cases h0 : p % 3 = 0
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq Nat.prime_three
            (Nat.prime_of_mem_primeFactors hp)).mp (Nat.dvd_of_mod_eq_zero h0)).symm
        · exact Or.inr h0
      split_ifs <;> omega
  have hsum := Finset.sum_congr rfl hpt
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have e1 : ∑ r ∈ ordReceivers N q, N.factorization r = ∑ p ∈ N.primeFactors,
      (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then N.factorization p else 0) := Finset.sum_filter _ _
  have e2 : (ordReceivers N q).card = ∑ p ∈ N.primeFactors,
      (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then 1 else 0) := Finset.card_filter _ _
  have e3 : (highPrimes N q).card =
      ∑ p ∈ N.primeFactors, (if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0) := by
    rw [highPrimes, ← Finset.filter_ne', Finset.filter_filter, Finset.card_filter]
  have e4 : highExcessDefect N q = ∑ p ∈ N.primeFactors,
      (if p ≠ q ∧ 4 ≤ N.factorization p ∧ p ≠ 3 then N.factorization p / 2 - 2 else 0) := by
    rw [highExcessDefect, highPrimes, ← Finset.filter_ne', Finset.filter_filter,
      Finset.filter_filter, Finset.sum_filter]
  have e5 : twoModThreeMass N q = ∑ p ∈ N.primeFactors,
      (if p ≠ q ∧ 4 ≤ N.factorization p ∧ p % 3 = 2 then N.factorization p else 0) := by
    rw [twoModThreeMass, highPrimes, ← Finset.filter_ne', Finset.filter_filter,
      Finset.filter_filter, Finset.sum_filter]
  have e6 : highTwoModThree N q = ∑ p ∈ N.primeFactors,
      (if p ≠ q ∧ 4 ≤ N.factorization p ∧ p % 3 = 2 then 1 else 0) := by
    rw [highTwoModThree, highPrimes, ← Finset.filter_ne', Finset.filter_filter,
      Finset.filter_filter, Finset.card_filter]
  have e7 : ((squarePrimes N q).filter fun p => p % 3 = 1).card =
      ∑ p ∈ N.primeFactors,
        (if (p ≠ q ∧ N.factorization p = 2) ∧ p % 3 = 1 then 1 else 0) := by
    rw [squarePrimes, Finset.filter_filter, Finset.card_filter]
  have e8 : ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) =
      ∑ p ∈ N.primeFactors, (if p ≠ q then N.factorization p / 2 - 1 else 0) := by
    rw [← Finset.filter_ne', Finset.sum_filter]
  have e9 : ∑ p ∈ N.primeFactors,
      (if p = 3 then (if 4 ≤ N.factorization p then 3 * N.factorization p else 0) +
        (N.factorization p / 2 - 2) else 0) =
      (if 4 ≤ N.factorization 3 then 3 * N.factorization 3 else 0) + threeExcessDefect N :=
    sum_ite_eq_three_sd N (fun e => (if 4 ≤ e then 3 * e else 0) + (e / 2 - 2)) (by simp)
  have e10 : ∑ p ∈ N.primeFactors,
      (if p = 3 then (if 4 ≤ N.factorization p then 7 else 0) else 0) =
      (if 4 ≤ N.factorization 3 then 7 else 0) :=
    sum_ite_eq_three_sd N (fun e => if 4 ≤ e then 7 else 0) (by simp)
  omega

/-- The second defect identity: for every special prime `q` of an odd perfect number `N`, with
`T` the total excess, `H` the number of escape rows and `A` the number of rows through `q`,
`2 * ω(N) + 3 * v_3(σ(q ^ a)) + D = 7 * T + 9 + 2 * H + A` for the defect `D` on the left. The
total excess is not bounded. -/
theorem two_mul_card_primeFactors_add_three_mul_add_defect_eq {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    2 * N.primeFactors.card + 3 * padicValNat 3 (σ 1 (q ^ N.factorization q))
        + squareSurplusTwo N q + highRecvWeight N q + receiverSlack N q
        + 3 * highThreeWeight N q + 5 * highExcessDefect N q + twoModThreeMass N q
        + highTwoModThree N q + threeExcessDefect N
        + (if 3 ∣ N then 0 else 7) + (if N.factorization 3 = 2 then 1 else 0) =
      7 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 9
        + 2 * (escapeRows N q).card + (throughRows N q).card := by
  have h3q := three_ne_special_sd h hq hodd
  have hω := card_primeFactors_eq_split h hq hodd
  have hL := receiver_ledger_two h hq hodd
  have hL3 := three_ledger h hq hodd
  have hR := residue_identity_seven h hq hodd
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd Nat.prime_three h3q
  unfold threeExcessDefect at hR ⊢
  by_cases h3 : 3 ∣ N
  · have := Nat.prime_three.factorization_pos_of_dvd h.ne_zero h3
    rw [if_pos h3]
    split_ifs at hR ⊢ <;> omega
  · have := Nat.factorization_eq_zero_of_not_dvd h3
    rw [if_neg h3]
    split_ifs at hR ⊢ <;> omega

/-- A through row or an escape row sends weight at least 1 to `q`. -/
private theorem one_le_sigmaWeight_special_sd {N q p : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hp : p ∈ throughRows N q ∪ escapeRows N q) : 1 ≤ sigmaWeight N p q := by
  rcases Finset.mem_union.mp hp with hA | hH
  · have := (Finset.mem_filter.mp hA).2.2
    omega
  · obtain ⟨-, j, hj, he⟩ := phi3_escapeRow h hH
    have hd : q ∣ phi3 p := by
      rcases he with e | e <;> rw [e]
      · exact dvd_pow_self q (by omega)
      · exact Dvd.dvd.mul_left (dvd_pow_self q (by omega)) 3
    have hpS := (mem_escapeRows.mp hH).1
    simp only [squarePrimes, Finset.mem_filter] at hpS
    obtain ⟨hpN, -, h2⟩ := hpS
    rw [sigmaWeight, h2, sigma_prime_sq (Nat.prime_of_mem_primeFactors hpN)]
    exact hq.factorization_pos_of_dvd (by unfold phi3; omega) hd

/-- Through rows and escape rows each send weight at least 1 to `q`, and they are disjoint. -/
theorem card_throughRows_add_card_escapeRows_le {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    (throughRows N q).card + (escapeRows N q).card ≤ N.factorization q := by
  have hq2 : q ≠ 2 := by
    have := (special_mod_four h hq hodd).1
    omega
  have hdis : Disjoint (throughRows N q) (escapeRows N q) := by
    rw [Finset.disjoint_left]
    intro p hA hH
    have h0 := recvWeight_eq_zero_of_mem_escapeRows hH
    have h1 := (Finset.mem_filter.mp hA).2.1
    omega
  rw [← Finset.card_union_of_disjoint hdis]
  have hsub : throughRows N q ∪ escapeRows N q ⊆ N.primeFactors := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp <;>
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  calc (throughRows N q ∪ escapeRows N q).card
      = ∑ p ∈ throughRows N q ∪ escapeRows N q, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ p ∈ throughRows N q ∪ escapeRows N q, sigmaWeight N p q :=
        Finset.sum_le_sum fun p hp => one_le_sigmaWeight_special_sd h hq hp
    _ ≤ ∑ p ∈ N.primeFactors, sigmaWeight N p q := Finset.sum_le_sum_of_subset hsub
    _ = N.factorization q := sigmaWeight_sum_eq h.perfect hq hq2

/-- For every special prime `q` of exponent `a` and `T` the total excess,
`2 * ω(N) + 3 * v_3(σ(q ^ a)) ≤ 7 * T + 10 + a`. Neither `T` nor `a` is bounded here. -/
theorem two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_ten_add_exponent
    {N q : ℕ} (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    2 * N.primeFactors.card + 3 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      7 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 10 +
        N.factorization q := by
  have hI := two_mul_card_primeFactors_add_three_mul_add_defect_eq h hq hodd
  have hH := card_escapeRows_le_one_all h hq hodd
  have hA := card_throughRows_add_card_escapeRows_le h hq hodd
  omega

/-- For `q ≡ 2 (mod 3)` there is no escape row and no through row, so
`2 * ω(N) + 3 * v_3(σ(q ^ a)) ≤ 7 * T + 9`. The total excess is not bounded here. -/
theorem two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_nine {N q : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq3 : q % 3 = 2) :
    2 * N.primeFactors.card + 3 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      7 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 9 := by
  have hI := two_mul_card_primeFactors_add_three_mul_add_defect_eq h hq hodd
  have he : throughRows N q ∪ escapeRows N q = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
    have hw := one_le_sigmaWeight_special_sd h hq hp
    have hpS : p ∈ squarePrimes N q := by
      rcases Finset.mem_union.mp hp with hp | hp <;> exact (Finset.mem_filter.mp hp).1
    simp only [squarePrimes, Finset.mem_filter] at hpS
    obtain ⟨hpN, -, h2⟩ := hpS
    rw [sigmaWeight, h2, sigma_prime_sq (Nat.prime_of_mem_primeFactors hpN)] at hw
    have hd : q ∣ phi3 p := Nat.dvd_of_factorization_pos (by omega)
    have := prime_dvd_phi3_mod_three hq (by omega) hd
    omega
  have hc := Finset.card_union_le (throughRows N q) (escapeRows N q)
  have h0 : (throughRows N q).card = 0 ∧ (escapeRows N q).card = 0 := by
    constructor <;> refine Finset.card_eq_zero.mpr (Finset.subset_empty.mp ?_)
    · exact he ▸ Finset.subset_union_left
    · exact he ▸ Finset.subset_union_right
  omega

end OddPerfect

#print axioms OddPerfect.two_mul_card_squarePrimes_add_surplus_eq
#print axioms OddPerfect.receiver_ledger_two
#print axioms OddPerfect.residue_identity_seven
#print axioms OddPerfect.two_mul_card_primeFactors_add_three_mul_add_defect_eq
#print axioms OddPerfect.card_throughRows_add_card_escapeRows_le
#print axioms
  OddPerfect.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_ten_add_exponent
#print axioms OddPerfect.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_nine
