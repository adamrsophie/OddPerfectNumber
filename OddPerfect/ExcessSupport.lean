import OddPerfect.Phi3
import OddPerfect.Valuation
import OddPerfect.SpecialPrime
import OddPerfect.SpecialIndexWitness
import OddPerfect.Counting

/-!
# Prime factors against total excess when the special prime is 2 modulo 3

Let `N` be an odd perfect number with special prime `q` and total excess
`T = ∑ (v_p(N) / 2 - 1)` over the prime factors `p ≠ q`. If `q ≡ 2 (mod 3)`, then
`ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5` with `a = v_q(N)`
(`card_primeFactors_add_two_mul_le_five_excess_add_five`), hence `ω(N) ≤ 5 * T + 3`
(`card_primeFactors_le_five_excess_add_three`) and
`ω(N) + 2 * v_3(a + 1) ≤ 5 * T + 3` (`card_primeFactors_add_two_mul_index_le`). In Euler's form
`N = q ^ a * m ^ 2` with `q ∤ m` this reads `ω(N) ≤ 5 * (Ω(m) - ω(m)) + 3`
(`cardDistinctFactors_le_five_mul_sub_add_three`). No bound on the special exponent and no cap
on any ordinary exponent is assumed.

The counting lemma holds for every special prime. Call an ordinary prime of exponent exactly 2 a
square prime, and call a square prime `p` an escape row when every prime factor of
`phi3 p = σ(p ^ 2)` is `3` or `q`. Each other square prime sends weight to an ordinary prime
`r ≠ 3` with `r ≡ 1 (mod 3)`, and conservation of weight at `r` (`sigmaWeight_sum_eq`) gives
`#square primes ≤ #escape rows + ∑ v_r(N)` over those receivers (`card_squarePrimes_le`). The
receivers are square primes that are 1 modulo 3 and primes of exponent at least 4, which gives
the form `card_squarePrimes_add_le` in terms of the total excess.

Relation to published results. The count is the one in the proof of Theorem 1 of Ochem and Rao
(Math. Comp. 83, 2014), where the special exponent enters only as capacity of a special prime
that is 1 modulo 3; for a special prime that is 2 modulo 3 that term is absent. The inequality in
this form (no special exponent, in terms of the total excess) is not stated there. Whether it is
stated elsewhere has not been verified. It bounds the number of prime factors for each fixed
total excess in this class of special primes; it does not bound the total excess and does not
show that the class is empty.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The square primes of `N` with respect to `q`: prime factors `p ≠ q` of exponent exactly 2. -/
def squarePrimes (N q : ℕ) : Finset ℕ :=
  N.primeFactors.filter fun p => p ≠ q ∧ N.factorization p = 2

/-- The escape rows: square primes `p` such that every prime factor of `phi3 p` is `3` or `q`.
The quantifier runs over the prime factors of `phi3 p` so that the filter is decidable; see
`mem_escapeRows` for the unbounded form. -/
def escapeRows (N q : ℕ) : Finset ℕ :=
  (squarePrimes N q).filter fun p => ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q

/-- Membership in `escapeRows`, with the quantifier over all primes. -/
theorem mem_escapeRows {N q p : ℕ} : p ∈ escapeRows N q ↔
    p ∈ squarePrimes N q ∧ ∀ r, r.Prime → r ∣ phi3 p → r = 3 ∨ r = q := by
  unfold escapeRows
  rw [Finset.mem_filter]
  have h0 : phi3 p ≠ 0 := by unfold phi3; omega
  constructor
  · rintro ⟨hp, hr⟩
    exact ⟨hp, fun r hr' hd => hr r (Nat.mem_primeFactors.mpr ⟨hr', hd, h0⟩)⟩
  · rintro ⟨hp, hr⟩
    exact ⟨hp, fun r hr' =>
      hr r (Nat.prime_of_mem_primeFactors hr') (Nat.dvd_of_mem_primeFactors hr')⟩

/-- The counting lemma: the number of square primes is at most the number of escape rows plus
the total exponent of the prime factors `r ≠ q`, `r ≠ 3` with `r ≡ 1 (mod 3)`. -/
theorem card_squarePrimes_le {N q : ℕ} (h : OddPerfect N) :
    (squarePrimes N q).card ≤ (escapeRows N q).card +
      ∑ r ∈ N.primeFactors.filter (fun r => r ≠ q ∧ r ≠ 3 ∧ r % 3 = 1), N.factorization r := by
  set R := N.primeFactors.filter (fun r => r ≠ q ∧ r ≠ 3 ∧ r % 3 = 1) with hR
  set O' := (squarePrimes N q).filter fun p => ¬ ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q
    with hO'
  have hsplit := Finset.card_filter_add_card_filter_not (s := squarePrimes N q)
    (fun p => ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q)
  have hrow : ∀ p ∈ O', 1 ≤ ∑ r ∈ R, sigmaWeight N p r := by
    intro p hp
    simp only [O', squarePrimes, Finset.mem_filter] at hp
    obtain ⟨⟨hpN, -, he⟩, hne⟩ := hp
    push Not at hne
    obtain ⟨r, hr, hr3, hrq⟩ := hne
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrd := Nat.dvd_of_mem_primeFactors hr
    have h0 : phi3 p ≠ 0 := by unfold phi3; omega
    have hr1 : r % 3 = 1 := prime_dvd_phi3_mod_three hrp hr3 hrd
    have hw : 1 ≤ sigmaWeight N p r := by
      rw [sigmaWeight, he, sigma_prime_sq hpp]
      exact hrp.factorization_pos_of_dvd h0 hrd
    have hrN : r ∈ N.primeFactors :=
      mem_primeFactors_of_sigmaWeight_ne_zero h.perfect hpN (by omega) (by omega)
    have hrR : r ∈ R := Finset.mem_filter.mpr ⟨hrN, hrq, hr3, hr1⟩
    exact hw.trans (Finset.single_le_sum (f := fun r => sigmaWeight N p r)
      (fun _ _ => Nat.zero_le _) hrR)
  have hcount : O'.card ≤ ∑ r ∈ R, N.factorization r := by
    calc O'.card = ∑ p ∈ O', 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ p ∈ O', ∑ r ∈ R, sigmaWeight N p r := Finset.sum_le_sum hrow
      _ = ∑ r ∈ R, ∑ p ∈ O', sigmaWeight N p r := Finset.sum_comm
      _ ≤ ∑ r ∈ R, ∑ p ∈ N.primeFactors, sigmaWeight N p r := by
          refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum_of_subset ?_
          exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      _ = ∑ r ∈ R, N.factorization r := by
          refine Finset.sum_congr rfl fun r hr => ?_
          obtain ⟨hrN, -, -, hr1⟩ := Finset.mem_filter.mp hr
          exact sigmaWeight_sum_eq h.perfect (Nat.prime_of_mem_primeFactors hrN) (by omega)
  have hesc : (escapeRows N q).card + O'.card = (squarePrimes N q).card := hsplit
  omega

/-- The special prime is not `3`. -/
private theorem three_ne_special {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : (3 : ℕ) ≠ q := by
  rintro rfl
  have := (special_mod_four h hq hodd).1
  omega

/-- The term at `3` as a sum over the prime factors. -/
private theorem ite_three_eq_sum (N : ℕ) :
    (if 4 ≤ N.factorization 3 then N.factorization 3 else 0) =
      ∑ p ∈ N.primeFactors,
        if p = 3 then (if 4 ≤ N.factorization p then N.factorization p else 0) else 0 := by
  rw [Finset.sum_ite_eq']
  by_cases h3 : 3 ∈ N.primeFactors
  · rw [if_pos h3]
  · rw [if_neg h3]
    have : N.factorization 3 = 0 :=
      Finsupp.notMem_support_iff.mp (by rw [Nat.support_factorization]; exact h3)
    simp [this]

/-- The total excess as a sum over the prime factors. -/
private theorem excess_eq_sum (N q : ℕ) :
    ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) =
      ∑ p ∈ N.primeFactors, if p ≠ q then N.factorization p / 2 - 1 else 0 := by
  rw [← Finset.filter_ne', Finset.sum_filter]

/-- The number of primes of exponent at least 4 as a sum over the prime factors. -/
private theorem card_large_eq_sum (N q : ℕ) :
    ((N.primeFactors.erase q).filter fun p => 4 ≤ N.factorization p).card =
      ∑ p ∈ N.primeFactors, if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0 := by
  rw [← Finset.filter_ne', Finset.filter_filter, Finset.card_filter]

/-- The number of square primes as a sum over the prime factors. -/
private theorem card_squarePrimes_eq_sum (N q : ℕ) :
    (squarePrimes N q).card =
      ∑ p ∈ N.primeFactors, if p ≠ q ∧ N.factorization p = 2 then 1 else 0 := by
  rw [squarePrimes, Finset.card_filter]

/-- The number of square primes that are 1 modulo 3 as a sum over the prime factors. -/
private theorem card_squarePrimes_one_eq_sum (N q : ℕ) :
    ((squarePrimes N q).filter fun p => p % 3 = 1).card =
      ∑ p ∈ N.primeFactors,
        if (p ≠ q ∧ N.factorization p = 2) ∧ p % 3 = 1 then 1 else 0 := by
  rw [squarePrimes, Finset.filter_filter, Finset.card_filter]

/-- An ordinary prime factor has a positive even exponent. -/
private theorem ordinary_exp {N q p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hp : p ∈ N.primeFactors) (hpq : p ≠ q) :
    ∃ j, N.factorization p = j + j ∧ 1 ≤ N.factorization p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hpp hpq
  exact ⟨j, hj, hpp.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)⟩

/-- The counting lemma in terms of the total excess `T` and the number `E` of prime factors
`p ≠ q` of exponent at least 4: with `b = v_3(N)` and `C` the square primes that are 1 modulo
3, `#square primes + (b if b ≥ 4, else 0) ≤ #escape rows + 2 * #C + 2 * (T + E)`. -/
theorem card_squarePrimes_add_le {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    (squarePrimes N q).card + (if 4 ≤ N.factorization 3 then N.factorization 3 else 0) ≤
      (escapeRows N q).card + 2 * ((squarePrimes N q).filter fun p => p % 3 = 1).card +
        2 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) +
          ((N.primeFactors.erase q).filter fun p => 4 ≤ N.factorization p).card) := by
  have hgen := card_squarePrimes_le (q := q) h
  have h3q := three_ne_special h hq hodd
  have hpt : ∀ p ∈ N.primeFactors,
      ((if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then N.factorization p else 0) +
        if p = 3 then (if 4 ≤ N.factorization p then N.factorization p else 0) else 0) ≤
      2 * (if (p ≠ q ∧ N.factorization p = 2) ∧ p % 3 = 1 then 1 else 0) +
        2 * (if p ≠ q then N.factorization p / 2 - 1 else 0) +
        2 * (if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0) := by
    intro p hp
    by_cases hpq : p = q
    · split_ifs <;> omega
    · obtain ⟨j, hj, hpos⟩ := ordinary_exp h hq hodd hp hpq
      split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← Finset.sum_filter, ← ite_three_eq_sum, ← card_squarePrimes_one_eq_sum,
    ← excess_eq_sum, ← card_large_eq_sum] at hsum
  omega

/-- `3 E + (b if b ≥ 4, else 0) ≤ 3 T + (4 if b ≥ 4, else 0)`, with `b = v_3(N)`. -/
theorem three_mul_card_large_le {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    3 * ((N.primeFactors.erase q).filter fun p => 4 ≤ N.factorization p).card +
        (if 4 ≤ N.factorization 3 then N.factorization 3 else 0) ≤
      3 * ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) +
        (if 4 ≤ N.factorization 3 then 4 else 0) := by
  have h3q := three_ne_special h hq hodd
  have hpt : ∀ p ∈ N.primeFactors,
      3 * (if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0) +
        (if p = 3 then (if 4 ≤ N.factorization p then N.factorization p else 0) else 0) ≤
      3 * (if p ≠ q then N.factorization p / 2 - 1 else 0) +
        (if p = 3 then (if 4 ≤ N.factorization p then 4 else 0) else 0) := by
    intro p hp
    by_cases hpq : p = q
    · split_ifs <;> omega
    · obtain ⟨j, hj, hpos⟩ := ordinary_exp h hq hodd hp hpq
      split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← ite_three_eq_sum, ← excess_eq_sum, ← card_large_eq_sum] at hsum
  have hF : (∑ p ∈ N.primeFactors,
      if p = 3 then (if 4 ≤ N.factorization p then 4 else 0) else 0) ≤
      (if 4 ≤ N.factorization 3 then 4 else 0) := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> omega
  omega

/-- `ω(N) ≤ 1 + #square primes + E`. -/
theorem card_primeFactors_le_split {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.primeFactors.card ≤ 1 + (squarePrimes N q).card +
      ((N.primeFactors.erase q).filter fun p => 4 ≤ N.factorization p).card := by
  have hpt : ∀ p ∈ N.primeFactors, 1 ≤
      (if p = q then 1 else 0) + (if p ≠ q ∧ N.factorization p = 2 then 1 else 0) +
        (if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0) := by
    intro p hp
    by_cases hpq : p = q
    · split_ifs <;> omega
    · obtain ⟨j, hj, hpos⟩ := ordinary_exp h hq hodd hp hpq
      split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib] at hsum
  rw [← card_squarePrimes_eq_sum, ← card_large_eq_sum, ← Finset.card_eq_sum_ones,
    Finset.sum_ite_eq'] at hsum
  split_ifs at hsum <;> omega

/-- `#C + v_3(σ(q ^ a)) ≤ v_3(N)`, where `C` is the set of square primes that are 1 modulo 3. -/
theorem card_squarePrimes_one_add_le {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ((squarePrimes N q).filter fun p => p % 3 = 1).card +
        padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤ N.factorization 3 := by
  have hb := special_index_budget h hq hodd Nat.prime_three (by decide)
  have hsub : ((squarePrimes N q).filter fun p => p % 3 = 1) ⊆
      N.primeFactors.filter fun p => p ≠ q ∧ p % 3 = 1 ∧ 3 ∣ N.factorization p + 1 := by
    intro p hp
    simp only [squarePrimes, Finset.mem_filter] at hp ⊢
    obtain ⟨⟨hpN, hpq, he⟩, hp1⟩ := hp
    exact ⟨hpN, hpq, hp1, by rw [he]⟩
  have := Finset.card_le_card hsub
  omega

/-- For a special prime `q ≡ 2 (mod 3)` there are no escape rows. -/
private theorem escapeRows_eq_empty {N q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) :
    escapeRows N q = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨hpS, hr⟩ := mem_escapeRows.mp hp
  have hpp : p.Prime := by
    simp only [squarePrimes, Finset.mem_filter] at hpS
    exact Nat.prime_of_mem_primeFactors hpS.1
  have h0 : phi3 p ≠ 0 := by unfold phi3; omega
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ phi3 p → d = 3 := by
    intro d hd hdd
    rcases hr d hd hdd with h3 | rfl
    · exact h3
    · have := prime_dvd_phi3_mod_three hd (by omega) hdd
      omega
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd h0 hall
  set k := (phi3 p).primeFactorsList.length
  have h9 := not_nine_dvd_phi3 p
  have hk : k ≤ 1 := by
    by_contra hk
    exact h9 (by
      rw [hpow]
      exact dvd_trans (by norm_num) (pow_dvd_pow 3 (show 2 ≤ k by omega)))
  have hle : phi3 p ≤ 3 := by
    rw [hpow]
    interval_cases k <;> norm_num
  have h2 := hpp.two_le
  unfold phi3 at hle
  nlinarith

/-- The special component carries `v_3(σ(q ^ a)) = v_3(q + 1) + v_3(a + 1) ≥ 1 + v_3(a + 1)`
when `q ≡ 2 (mod 3)` and `a` is odd. -/
private theorem index_succ_le_sigma {N q : ℕ} (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hq3 : q % 3 = 2) :
    1 + padicValNat 3 (N.factorization q + 1) ≤ padicValNat 3 (σ 1 (q ^ N.factorization q)) := by
  have hs := padicValNat_three_sigma_prime_pow_of_mod_two hq hq3 (N.factorization q)
  rw [if_neg (Nat.not_even_iff_odd.mpr hodd)] at hs
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 1 ≤ padicValNat 3 (q + 1) :=
    one_le_padicValNat_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
  omega

/-- For an odd perfect number `N` with special prime `q ≡ 2 (mod 3)` of exponent `a`,
`ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5`, where `T` is the total excess. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_five {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq3 : q % 3 = 2) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 := by
  have hA := card_squarePrimes_add_le h hq hodd
  rw [escapeRows_eq_empty hq hq3, Finset.card_empty] at hA
  have hB := card_squarePrimes_one_add_le h hq hodd
  have hC := three_mul_card_large_le h hq hodd
  have hD := card_primeFactors_le_split h hq hodd
  have hs := index_succ_le_sigma hq hodd hq3
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd Nat.prime_three
    (three_ne_special h hq hodd)
  split_ifs at hA hC <;> omega

/-- For an odd perfect number with special prime `q ≡ 2 (mod 3)`, `ω(N) ≤ 5 * T + 3`, where `T`
is the total excess. -/
theorem card_primeFactors_le_five_excess_add_three {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq3 : q % 3 = 2) :
    N.primeFactors.card ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 3 := by
  have := card_primeFactors_add_two_mul_le_five_excess_add_five h hq hodd hq3
  have := index_succ_le_sigma hq hodd hq3
  omega

/-- For an odd perfect number with special prime `q ≡ 2 (mod 3)` of exponent `a`,
`ω(N) + 2 * v_3(a + 1) ≤ 5 * T + 3`, where `T` is the total excess. -/
theorem card_primeFactors_add_two_mul_index_le {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq3 : q % 3 = 2) :
    N.primeFactors.card + 2 * padicValNat 3 (N.factorization q + 1) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 3 := by
  have := card_primeFactors_add_two_mul_le_five_excess_add_five h hq hodd hq3
  have := index_succ_le_sigma hq hodd hq3
  omega

/-- In Euler's form `N = q ^ a * m ^ 2` with `q ∤ m`, the special exponent is odd and the total
excess is `Ω(m) - ω(m)`. -/
theorem euler_form_excess {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hqm : ¬ q ∣ m) (hN : N = q ^ a * m ^ 2) :
    Odd (N.factorization q) ∧
      ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) =
        ArithmeticFunction.cardFactors m - ArithmeticFunction.cardDistinctFactors m := by
  have hN0 := h.ne_zero
  have hm0 : m ≠ 0 := by rintro rfl; simp [hN] at hN0
  have hq0 : q ^ a ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hfac : ∀ p, N.factorization p = a * q.factorization p + 2 * m.factorization p := by
    intro p
    rw [hN, Nat.factorization_mul hq0 (pow_ne_zero _ hm0), Finsupp.add_apply,
      Nat.factorization_pow, Nat.factorization_pow]
    rfl
  have hmq : m.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqm
  have hkq : N.factorization q = a := by
    rw [hfac, hq.factorization_self, hmq]
    ring
  have hk : Odd a := by
    by_contra hk
    obtain ⟨j, rfl⟩ := Nat.not_odd_iff_even.mp hk
    exact not_isSquare h ⟨q ^ j * m, by rw [hN]; ring⟩
  have hne : ∀ p, p ≠ q → N.factorization p = 2 * m.factorization p := by
    intro p hpq
    rw [hfac, hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq)]
    ring
  have hset : N.primeFactors.erase q = m.primeFactors := by
    ext p
    rw [Finset.mem_erase, ← Nat.support_factorization, ← Nat.support_factorization,
      Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨hpq, hp⟩
      rw [hne p hpq] at hp
      omega
    · intro hp
      have hpq : p ≠ q := by rintro rfl; exact hp hmq
      exact ⟨hpq, by rw [hne p hpq]; omega⟩
  refine ⟨hkq ▸ hk, ?_⟩
  rw [hset]
  have hsum : ∑ p ∈ m.primeFactors, (N.factorization p / 2 - 1)
      = ∑ p ∈ m.primeFactors, (m.factorization p - 1) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpq : p ≠ q := by rintro rfl; exact (Nat.dvd_of_mem_primeFactors hp |> hqm)
    rw [hne p hpq]
    omega
  have hOm : ArithmeticFunction.cardFactors m =
      ∑ p ∈ m.primeFactors, (m.factorization p - 1) + m.primeFactors.card := by
    rw [cardFactors_eq_sum_primeFactors, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hm0
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  rw [cardDistinctFactors_eq_card_primeFactors, hOm, hsum]
  omega

/-- In Euler's form `N = q ^ a * m ^ 2` with `q ∤ m` of an odd perfect number with
`q ≡ 2 (mod 3)`, `ω(N) ≤ 5 * (Ω(m) - ω(m)) + 3`. -/
theorem cardDistinctFactors_le_five_mul_sub_add_three {N q a m : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hqm : ¬ q ∣ m) (hN : N = q ^ a * m ^ 2) (hq3 : q % 3 = 2) :
    ArithmeticFunction.cardDistinctFactors N ≤
      5 * (ArithmeticFunction.cardFactors m - ArithmeticFunction.cardDistinctFactors m) + 3 := by
  obtain ⟨hodd, hT⟩ := euler_form_excess h hq hqm hN
  rw [cardDistinctFactors_eq_card_primeFactors, ← hT]
  exact card_primeFactors_le_five_excess_add_three h hq hodd hq3

end OddPerfect

#print axioms OddPerfect.mem_escapeRows
#print axioms OddPerfect.card_squarePrimes_le
#print axioms OddPerfect.card_squarePrimes_add_le
#print axioms OddPerfect.three_mul_card_large_le
#print axioms OddPerfect.card_primeFactors_le_split
#print axioms OddPerfect.card_squarePrimes_one_add_le
#print axioms OddPerfect.euler_form_excess
#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five
#print axioms OddPerfect.card_primeFactors_le_five_excess_add_three
#print axioms OddPerfect.card_primeFactors_add_two_mul_index_le
#print axioms OddPerfect.cardDistinctFactors_le_five_mul_sub_add_three
