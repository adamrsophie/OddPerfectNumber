import OddPerfect.ExcessSupport
import OddPerfect.ClassicalInputs
import OddPerfect.Phi3Algebra
import OddPerfect.UpperBound

/-!
# Prime factors against total excess for every special prime, and a conditional bound

Let `N` be an odd perfect number with special prime `q` of exponent `a = v_q(N)`, and let
`T = ∑ (v_p(N) / 2 - 1)` over the prime factors `p ≠ q` be the total excess. For every special
prime, `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5 + #escape rows`
(`card_primeFactors_add_two_mul_le_five_excess_add_escape`), where an escape row is a square
prime `p` such that every prime factor of `phi3 p` is `3` or `q` (`escapeRows`). This part is
unconditional.

The results named `conditional_…` assume `NagellPrimePower` and `LjunggrenThreePrimePower`, two
consequences of classical theorems of Nagell (1921) and Ljunggren (1943) that are not proved in
this library; they are hypotheses of the theorems, not axioms. With them, for each fixed total
excess only finitely many odd perfect numbers can exist. The total excess itself is not
bounded, so this does not prove the conjecture. Relation to published results: the count
follows the proof of Theorem 1 of Ochem and Rao (Math. Comp. 83, 2014), whose inequality carries
the special exponent; whether the form here is stated in the literature has not been verified.

Under the two hypotheses an escape row `p` has `phi3 p ∈ {q, 3 q, 3 q ^ 2}`
(`conditional_phi3_escapeRow`), two escape rows cannot coexist
(`conditional_card_escapeRows_le_one`), hence `ω(N) ≤ 5 * T + 6` and `N < 2 ^ 4 ^ (5 * T + 6)`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The special prime is not `3` (a local copy of a private lemma of `ExcessSupport`). -/
private theorem three_ne_special' {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : (3 : ℕ) ≠ q := by
  rintro rfl
  have := (special_mod_four h hq hodd).1
  omega

/-- For every special prime `q` of an odd perfect number `N`, with `T` the total excess,
`ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5 + #escape rows`. Unconditional. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_escape {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 +
        (escapeRows N q).card := by
  have hA := card_squarePrimes_add_le h hq hodd
  have hB := card_squarePrimes_one_add_le h hq hodd
  have hC := three_mul_card_large_le h hq hodd
  have hD := card_primeFactors_le_split h hq hodd
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd Nat.prime_three
    (three_ne_special' h hq hodd)
  split_ifs at hA hC <;> omega

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (classical theorems of
Nagell and Ljunggren, not proved in this library): an escape row `p` is a prime with
`phi3 p = q`, `phi3 p = 3 * q` or `phi3 p = 3 * q ^ 2`. -/
theorem conditional_phi3_escapeRow (hN : NagellPrimePower) (hL : LjunggrenThreePrimePower)
    {N q p : ℕ} (hq : q.Prime) (hp : p ∈ escapeRows N q) :
    p.Prime ∧ (phi3 p = q ∨ phi3 p = 3 * q ∨ phi3 p = 3 * q ^ 2) := by
  obtain ⟨hpS, hr⟩ := mem_escapeRows.mp hp
  have hpp : p.Prime := by
    simp only [squarePrimes, Finset.mem_filter] at hpS
    exact Nat.prime_of_mem_primeFactors hpS.1
  refine ⟨hpp, ?_⟩
  have h7 : 7 ≤ phi3 p := by
    have := hpp.two_le
    unfold phi3
    nlinarith
  have h9 := not_nine_dvd_phi3 p
  by_cases h3 : 3 ∣ phi3 p
  · obtain ⟨n, hn⟩ := h3
    have h3' : ¬ 3 ∣ n := fun ⟨c, hc⟩ => h9 ⟨c, by rw [hn, hc]; ring⟩
    have hall : ∀ {d : ℕ}, d.Prime → d ∣ n → d = q := by
      intro d hd hdd
      rcases hr d hd (hn ▸ dvd_mul_of_dvd_right hdd 3) with e | e
      · exact absurd (e ▸ hdd) h3'
      · exact e
    obtain ⟨k, hk⟩ : ∃ k, n = q ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) hall⟩
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, pow_zero] at hk; omega
      · exact h0
    have hk2 : k ≤ 2 := hL p q k hpp hq hk1 (by rw [← hk]; exact hn)
    interval_cases k
    · exact Or.inr (Or.inl (by rw [hn, hk, pow_one]))
    · exact Or.inr (Or.inr (by rw [hn, hk]))
  · have hall : ∀ {d : ℕ}, d.Prime → d ∣ phi3 p → d = q := by
      intro d hd hdd
      rcases hr d hd hdd with e | e
      · exact absurd (e ▸ hdd) h3
      · exact e
    obtain ⟨k, hk⟩ : ∃ k, phi3 p = q ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) hall⟩
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, pow_zero] at hk; omega
      · exact h0
    have hk2 : k = 1 := hN p q k hpp hq hk1 hk
    exact Or.inl (by rw [hk, hk2, pow_one])

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (classical theorems of
Nagell and Ljunggren, not proved in this library): there is at most one escape row. The
hypothesis that `N` is an odd perfect number is not needed. -/
theorem conditional_card_escapeRows_le_one (hN : NagellPrimePower)
    (hL : LjunggrenThreePrimePower) {N q : ℕ} (hq : q.Prime) : (escapeRows N q).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  obtain ⟨hxp, hxs⟩ := conditional_phi3_escapeRow hN hL hq hx
  obtain ⟨hyp, hys⟩ := conditional_phi3_escapeRow hN hL hq hy
  have hinj : phi3 x = phi3 y → x = y := fun e => phi3_strictMono.injective e
  have h1q := hq.one_lt
  rcases hxs with h1 | h1 | h1 <;> rcases hys with h2 | h2 | h2
  · exact hinj (h1.trans h2.symm)
  · exact absurd (by rw [h2, h1]) (no_phi3_eq_three_mul_phi3 hyp (h1 ▸ hq))
  · exact (ch_unique_S1_S31 hyp hxp hq h1q (by rw [h2]; ring) h1 le_rfl).elim
  · exact absurd (by rw [h1, h2]) (no_phi3_eq_three_mul_phi3 hxp (h2 ▸ hq))
  · exact hinj (h1.trans h2.symm)
  · exact (ch_unique_S21_S31 hyp hq h1q (by rw [h2]; ring) h1 le_rfl).elim
  · exact (ch_unique_S1_S31 hxp hyp hq h1q (by rw [h1]; ring) h2 le_rfl).elim
  · exact (ch_unique_S21_S31 hxp hq h1q (by rw [h1]; ring) h2 le_rfl).elim
  · exact hinj (h1.trans h2.symm)

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (classical theorems of
Nagell and Ljunggren, not proved in this library): for every special prime `q`,
`ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 6`. -/
theorem conditional_card_primeFactors_add_two_mul_le (hN : NagellPrimePower)
    (hL : LjunggrenThreePrimePower) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 6 := by
  have := card_primeFactors_add_two_mul_le_five_excess_add_escape h hq hodd
  have := conditional_card_escapeRows_le_one hN hL (N := N) hq
  omega

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (classical theorems of
Nagell and Ljunggren, not proved in this library): for every special prime,
`ω(N) ≤ 5 * T + 6`. -/
theorem conditional_card_primeFactors_le_five_excess_add_six (hN : NagellPrimePower)
    (hL : LjunggrenThreePrimePower) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.primeFactors.card ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 6 := by
  have := conditional_card_primeFactors_add_two_mul_le hN hL h hq hodd
  omega

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (classical theorems of
Nagell and Ljunggren, not proved in this library): for every special prime,
`N < 2 ^ 4 ^ (5 * T + 6)`. -/
theorem conditional_lt_two_pow_four_pow_excess (hN : NagellPrimePower)
    (hL : LjunggrenThreePrimePower) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N < 2 ^ 4 ^ (5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 6) :=
  (lt_two_pow_four_pow h).trans_le (Nat.pow_le_pow_right two_pos
    (Nat.pow_le_pow_right (by norm_num)
      (conditional_card_primeFactors_le_five_excess_add_six hN hL h hq hodd)))

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (classical theorems of
Nagell and Ljunggren, not proved in this library): in Euler's form `N = q ^ a * m ^ 2` with
`q ∤ m`, `ω(N) ≤ 5 * (Ω(m) - ω(m)) + 6`. -/
theorem conditional_cardDistinctFactors_le_five_mul_sub_add_six (hN : NagellPrimePower)
    (hL : LjunggrenThreePrimePower) {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hqm : ¬ q ∣ m) (hN' : N = q ^ a * m ^ 2) :
    ArithmeticFunction.cardDistinctFactors N ≤
      5 * (ArithmeticFunction.cardFactors m - ArithmeticFunction.cardDistinctFactors m) + 6 := by
  obtain ⟨hodd, hT⟩ := euler_form_excess h hq hqm hN'
  rw [cardDistinctFactors_eq_card_primeFactors, ← hT]
  exact conditional_card_primeFactors_le_five_excess_add_six hN hL h hq hodd

/-- Conditional on `NagellPrimePower` and `LjunggrenThreePrimePower` (classical theorems of
Nagell and Ljunggren, not proved in this library): for each bound `T` on the total excess, only
finitely many odd perfect numbers exist, for every special prime and with no bound on the
special exponent. The total excess itself is not bounded here. -/
theorem conditional_finite_of_excess_le (hN : NagellPrimePower) (hL : LjunggrenThreePrimePower)
    (T : ℕ) : {N : ℕ | ∃ q, OddPerfect N ∧ q.Prime ∧ Odd (N.factorization q) ∧
      ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) ≤ T}.Finite := by
  refine (Set.finite_lt_nat (2 ^ 4 ^ (5 * T + 6))).subset ?_
  rintro N ⟨q, h, hq, hodd, hT⟩
  exact (conditional_lt_two_pow_four_pow_excess hN hL h hq hodd).trans_le
    (Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_right (by norm_num) (by omega)))

end OddPerfect

#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_escape
#print axioms OddPerfect.conditional_phi3_escapeRow
#print axioms OddPerfect.conditional_card_escapeRows_le_one
#print axioms OddPerfect.conditional_card_primeFactors_add_two_mul_le
#print axioms OddPerfect.conditional_card_primeFactors_le_five_excess_add_six
#print axioms OddPerfect.conditional_lt_two_pow_four_pow_excess
#print axioms OddPerfect.conditional_cardDistinctFactors_le_five_mul_sub_add_six
#print axioms OddPerfect.conditional_finite_of_excess_le
