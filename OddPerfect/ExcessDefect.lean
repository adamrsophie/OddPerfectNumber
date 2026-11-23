import OddPerfect.ExcessSupportSharp

/-!
# The defect form of the excess count

Let `N` be an odd perfect number with special prime `q` of exponent `a`, let
`T = ∑ (v_p(N) / 2 - 1)` over the prime factors `p ≠ q` be the total excess, `b = v_3(N)`,
`s = v_3(σ(q ^ a))` and `H` the number of escape rows. The library proves
`ω(N) + 2 * s ≤ 5 * T + 5 + H` (`card_primeFactors_add_two_mul_le_five_excess_add_escape`). This
file keeps the terms that the count drops. With the square primes `S` (ordinary, exponent 2),
the ordinary primes `X` of exponent at least 4 (`highPrimes`) and the ordinary receivers `R`
(`ordReceivers`), the dropped terms are

* `squareSurplus`: the surplus `∑ (recvWeight p - 1)` of the square primes that are not escape
  rows;
* `highRecvWeight`: the weight that `q` and the primes of `X` send to `R`;
* `highThreeWeight`: the weight that the primes of `X` send to 3;
* `twoModThreeMass`: the total exponent of the primes of `X` that are 2 modulo 3;
* `highExcessDefect`: `∑ (v_p(N) / 2 - 2)` over the primes `p ≠ 3` of `X`;
* `threeExcessDefect`: `b / 2 - 2`;

and `supportDefect` is their weighted sum plus 4 when `3 ∤ N`. Two ledgers (at the receivers,
`receiver_ledger`, and at 3, `three_ledger`) give the exact identity
`ω(N) + 2 * s + supportDefect N q = 5 * T + 5 + H`
(`card_primeFactors_add_two_mul_add_defect_eq`). The total excess is not bounded, and the odd
perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The ordinary primes of exponent at least 4: prime factors `p ≠ q` with `4 ≤ v_p(N)`. -/
def highPrimes (N q : ℕ) : Finset ℕ :=
  (N.primeFactors.erase q).filter fun p => 4 ≤ N.factorization p

/-- The surplus of the square rows: `∑ (recvWeight p - 1)` over the square primes that are not
escape rows. Each term is the weight above the one unit the count needs. -/
def squareSurplus (N q : ℕ) : ℕ :=
  ∑ p ∈ squarePrimes N q \ escapeRows N q, (recvWeight N q p - 1)

/-- The weight that the special prime and the ordinary primes of exponent at least 4 send to the
ordinary receivers. -/
def highRecvWeight (N q : ℕ) : ℕ :=
  ∑ p ∈ insert q (highPrimes N q), recvWeight N q p

/-- The weight that the ordinary primes of exponent at least 4 send to 3. -/
def highThreeWeight (N q : ℕ) : ℕ :=
  ∑ p ∈ highPrimes N q, sigmaWeight N p 3

/-- The total exponent of the ordinary primes of exponent at least 4 that are 2 modulo 3. -/
def twoModThreeMass (N q : ℕ) : ℕ :=
  ∑ p ∈ (highPrimes N q).filter (fun p => p % 3 = 2), N.factorization p

/-- `∑ (v_p(N) / 2 - 2)` over the ordinary primes `p ≠ 3` of exponent at least 4. -/
def highExcessDefect (N q : ℕ) : ℕ :=
  ∑ p ∈ (highPrimes N q).filter (fun p => p ≠ 3), (N.factorization p / 2 - 2)

/-- `v_3(N) / 2 - 2` (natural subtraction: 0 when `v_3(N) ≤ 5`). -/
def threeExcessDefect (N : ℕ) : ℕ := N.factorization 3 / 2 - 2

/-- The support defect: the terms that the count `ω(N) + 2 * s ≤ 5 * T + 5 + H` drops. -/
def supportDefect (N q : ℕ) : ℕ :=
  twoModThreeMass N q + 3 * highExcessDefect N q + threeExcessDefect N + squareSurplus N q +
    highRecvWeight N q + 2 * highThreeWeight N q + if 3 ∣ N then 0 else 4

private theorem three_ne_special'' {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : (3 : ℕ) ≠ q := by
  rintro rfl
  have := (special_mod_four h hq hodd).1
  omega

/-- An ordinary prime factor has a positive even exponent. -/
theorem even_pos_factorization_of_ne {N q p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hp : p ∈ N.primeFactors) (hpq : p ≠ q) :
    ∃ j, N.factorization p = j + j ∧ 1 ≤ N.factorization p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hpp hpq
  exact ⟨j, hj, hpp.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)⟩

private theorem special_mem {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : q ∈ N.primeFactors := by
  have : N.factorization q ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
  exact Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos this, h.ne_zero⟩

private theorem special_notMem_high (N q : ℕ) : q ∉ highPrimes N q := by
  simp [highPrimes]

/-- The prime factors split into the square primes, the special prime and the ordinary primes of
exponent at least 4. -/
theorem sum_primeFactors_split {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (f : ℕ → ℕ) :
    ∑ p ∈ N.primeFactors, f p =
      ∑ p ∈ squarePrimes N q, f p + ∑ p ∈ insert q (highPrimes N q), f p := by
  have hdis : Disjoint (squarePrimes N q) (insert q (highPrimes N q)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [squarePrimes, highPrimes, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_erase] at hp hp'
    rcases hp' with rfl | ⟨-, h4⟩
    · exact hp.2.1 rfl
    · omega
  have hset : N.primeFactors = squarePrimes N q ∪ insert q (highPrimes N q) := by
    ext p
    simp only [squarePrimes, highPrimes, Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_erase]
    constructor
    · intro hp
      by_cases hpq : p = q
      · exact Or.inr (Or.inl hpq)
      · obtain ⟨j, hj, hpos⟩ := even_pos_factorization_of_ne h hq hodd hp hpq
        by_cases h2 : N.factorization p = 2
        · exact Or.inl ⟨hp, hpq, h2⟩
        · exact Or.inr (Or.inr ⟨⟨hpq, hp⟩, by omega⟩)
    · rintro (⟨hp, -, -⟩ | rfl | ⟨⟨-, hp⟩, -⟩)
      · exact hp
      · exact special_mem h hq hodd
      · exact hp
  rw [hset, Finset.sum_union hdis]

/-- `ω(N) = 1 + #S + #X`. -/
theorem card_primeFactors_eq_split {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.primeFactors.card = 1 + (squarePrimes N q).card + (highPrimes N q).card := by
  have := sum_primeFactors_split h hq hodd (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
  rw [Finset.card_insert_of_notMem (special_notMem_high N q)] at this
  omega

/-- An escape row sends no weight to the ordinary receivers. -/
theorem recvWeight_eq_zero_of_mem_escapeRows {N q p : ℕ} (hp : p ∈ escapeRows N q) :
    recvWeight N q p = 0 := by
  obtain ⟨hpS, hr⟩ := mem_escapeRows.mp hp
  simp only [squarePrimes, Finset.mem_filter] at hpS
  obtain ⟨hpN, -, he⟩ := hpS
  unfold recvWeight
  refine Finset.sum_eq_zero fun r hrR => ?_
  obtain ⟨hrN, hrq, hr3, -⟩ := Finset.mem_filter.mp hrR
  rw [sigmaWeight, he, sigma_prime_sq (Nat.prime_of_mem_primeFactors hpN)]
  by_contra h0
  rcases hr r (Nat.prime_of_mem_primeFactors hrN) (Nat.dvd_of_factorization_pos h0) with e | e
  · exact hr3 e
  · exact hrq e

/-- Conservation at the ordinary receivers, over all sources. -/
theorem sum_primeFactors_recvWeight_eq {N q : ℕ} (h : OddPerfect N) :
    ∑ p ∈ N.primeFactors, recvWeight N q p = ∑ r ∈ ordReceivers N q, N.factorization r := by
  simp only [recvWeight]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hrN, -, -, hr1⟩ := Finset.mem_filter.mp hr
  exact sigmaWeight_sum_eq h.perfect (Nat.prime_of_mem_primeFactors hrN) (by omega)

/-- The ledger at the receivers: `#S + squareSurplus + highRecvWeight = H + ∑ v_r(N)` over the
ordinary receivers. -/
theorem receiver_ledger {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    (squarePrimes N q).card + squareSurplus N q + highRecvWeight N q =
      (escapeRows N q).card + ∑ r ∈ ordReceivers N q, N.factorization r := by
  rw [← sum_primeFactors_recvWeight_eq h, sum_primeFactors_split h hq hodd (recvWeight N q)]
  have hsub : escapeRows N q ⊆ squarePrimes N q := Finset.filter_subset _ _
  rw [← Finset.sum_sdiff hsub (f := recvWeight N q),
    Finset.sum_eq_zero (fun p hp => recvWeight_eq_zero_of_mem_escapeRows hp), add_zero]
  have hone : ∀ p ∈ squarePrimes N q \ escapeRows N q,
      recvWeight N q p = (recvWeight N q p - 1) + 1 := by
    intro p hp
    obtain ⟨hpS, hpE⟩ := Finset.mem_sdiff.mp hp
    have : 1 ≤ recvWeight N q p :=
      one_le_recvWeight h hpS (fun hall => hpE (Finset.mem_filter.mpr ⟨hpS, hall⟩))
    omega
  rw [Finset.sum_congr rfl hone, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_sdiff_of_subset hsub]
  have := Finset.card_le_card hsub
  unfold squareSurplus highRecvWeight
  omega

/-- The ledger at 3: `v_3(N) = #C + v_3(σ(q ^ a)) + highThreeWeight`, with `C` the square primes
that are 1 modulo 3. -/
theorem three_ledger {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.factorization 3 = ((squarePrimes N q).filter fun p => p % 3 = 1).card +
      padicValNat 3 (σ 1 (q ^ N.factorization q)) + highThreeWeight N q := by
  rw [← sigmaWeight_sum_eq h.perfect Nat.prime_three (by norm_num),
    sum_primeFactors_split h hq hodd (fun p => sigmaWeight N p 3),
    Finset.sum_insert (special_notMem_high N q), sigmaWeight_eq_padicValNat N q Nat.prime_three,
    Finset.card_filter]
  have hS : ∑ p ∈ squarePrimes N q, sigmaWeight N p 3 =
      ∑ p ∈ squarePrimes N q, if p % 3 = 1 then 1 else 0 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [squarePrimes, Finset.mem_filter] at hp
    obtain ⟨hpN, -, he⟩ := hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    rw [sigmaWeight_eq_padicValNat N p Nat.prime_three, he, padicValNat_three_sigma_prime_pow hpp]
    unfold threeWeight
    by_cases h3 : p = 3
    · subst h3; simp
    · by_cases h1 : p % 3 = 1
      · simp [h3, h1]
      · simp [h3, h1]
  rw [hS]
  unfold highThreeWeight
  ring

private theorem card_high_eq_sum (N q : ℕ) :
    (highPrimes N q).card =
      ∑ p ∈ N.primeFactors, if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0 := by
  rw [highPrimes, ← Finset.filter_ne', Finset.filter_filter, Finset.card_filter]

private theorem twoModThreeMass_eq_sum (N q : ℕ) :
    twoModThreeMass N q = ∑ p ∈ N.primeFactors,
      if p ≠ q ∧ 4 ≤ N.factorization p ∧ p % 3 = 2 then N.factorization p else 0 := by
  rw [twoModThreeMass, highPrimes, ← Finset.filter_ne', Finset.filter_filter,
    Finset.filter_filter, Finset.sum_filter]

private theorem highExcessDefect_eq_sum (N q : ℕ) :
    highExcessDefect N q = ∑ p ∈ N.primeFactors,
      if p ≠ q ∧ 4 ≤ N.factorization p ∧ p ≠ 3 then N.factorization p / 2 - 2 else 0 := by
  rw [highExcessDefect, highPrimes, ← Finset.filter_ne', Finset.filter_filter,
    Finset.filter_filter, Finset.sum_filter]

/-- The count by residues, summed over the prime factors. -/
private theorem residue_count {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    (highPrimes N q).card + ∑ r ∈ ordReceivers N q, N.factorization r + twoModThreeMass N q +
        3 * highExcessDefect N q +
        (if 3 ∈ N.primeFactors then
          2 * N.factorization 3 + (N.factorization 3 / 2 - 2) else 0) =
      2 * ((squarePrimes N q).filter fun p => p % 3 = 1).card +
        5 * ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) +
        (if 3 ∈ N.primeFactors then 4 else 0) := by
  have h3q := three_ne_special'' h hq hodd
  have hpt : ∀ p ∈ N.primeFactors,
      (if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0) +
        (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then N.factorization p else 0) +
        (if p ≠ q ∧ 4 ≤ N.factorization p ∧ p % 3 = 2 then N.factorization p else 0) +
        3 * (if p ≠ q ∧ 4 ≤ N.factorization p ∧ p ≠ 3 then N.factorization p / 2 - 2
          else 0) +
        (if p = 3 then 2 * N.factorization p + (N.factorization p / 2 - 2) else 0) =
      2 * (if (p ≠ q ∧ N.factorization p = 2) ∧ p % 3 = 1 then 1 else 0) +
        5 * (if p ≠ q then N.factorization p / 2 - 1 else 0) +
        (if p = 3 then 4 else 0) := by
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
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq'] at hsum
  have e1 : ∑ r ∈ ordReceivers N q, N.factorization r = ∑ p ∈ N.primeFactors,
      (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then N.factorization p else 0) := Finset.sum_filter _ _
  have e4 : ((squarePrimes N q).filter fun p => p % 3 = 1).card =
      ∑ p ∈ N.primeFactors,
        (if (p ≠ q ∧ N.factorization p = 2) ∧ p % 3 = 1 then 1 else 0) := by
    rw [squarePrimes, Finset.filter_filter, Finset.card_filter]
  have e5 : ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) =
      ∑ p ∈ N.primeFactors, (if p ≠ q then N.factorization p / 2 - 1 else 0) := by
    rw [← Finset.filter_ne', Finset.sum_filter]
  rw [card_high_eq_sum, e1, twoModThreeMass_eq_sum, highExcessDefect_eq_sum, e4, e5]
  exact hsum

/-- The defect identity: for every special prime `q` of an odd perfect number `N`, with `T` the
total excess and `H` the number of escape rows,
`ω(N) + 2 * v_3(σ(q ^ a)) + supportDefect N q = 5 * T + 5 + H`. The library inequality
`card_primeFactors_add_two_mul_le_five_excess_add_escape` drops the defect. The total excess is
not bounded. -/
theorem card_primeFactors_add_two_mul_add_defect_eq {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) +
        supportDefect N q =
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 +
        (escapeRows N q).card := by
  have h3q := three_ne_special'' h hq hodd
  have hω := card_primeFactors_eq_split h hq hodd
  have hL1 := receiver_ledger h hq hodd
  have hL3 := three_ledger h hq hodd
  have hR := residue_count h hq hodd
  unfold supportDefect threeExcessDefect
  by_cases h3 : 3 ∣ N
  · have h3P : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
    rw [if_pos h3]
    rw [if_pos h3P, if_pos h3P] at hR
    omega
  · have h3P : 3 ∉ N.primeFactors := fun hm => h3 (Nat.dvd_of_mem_primeFactors hm)
    have hb : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    rw [if_neg h3]
    rw [if_neg h3P, if_neg h3P] at hR
    omega

/-- The inequality form of `card_primeFactors_add_two_mul_add_defect_eq`. -/
theorem card_primeFactors_add_two_mul_add_defect_le {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) +
        supportDefect N q ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 +
        (escapeRows N q).card :=
  (card_primeFactors_add_two_mul_add_defect_eq h hq hodd).le

end OddPerfect

#print axioms OddPerfect.even_pos_factorization_of_ne
#print axioms OddPerfect.sum_primeFactors_split
#print axioms OddPerfect.card_primeFactors_eq_split
#print axioms OddPerfect.recvWeight_eq_zero_of_mem_escapeRows
#print axioms OddPerfect.sum_primeFactors_recvWeight_eq
#print axioms OddPerfect.receiver_ledger
#print axioms OddPerfect.three_ledger
#print axioms OddPerfect.card_primeFactors_add_two_mul_add_defect_eq
#print axioms OddPerfect.card_primeFactors_add_two_mul_add_defect_le
