import OddPerfect.ConditionalSupport
import OddPerfect.EisensteinRows
import OddPerfect.EisensteinLocal

/-!
# At most two escape rows, and unconditional bounds against the total excess

Let `N` be an odd perfect number with special prime `q` and total excess
`T = ∑ (v_p(N) / 2 - 1)` over the prime factors `p ≠ q`. An escape row is a square prime `p`
such that every prime factor of `phi3 p` is `3` or `q`; then `phi3 p = q ^ j` or
`phi3 p = 3 * q ^ j` with `j ≥ 1` (`phi3_escapeRow`).

For a prime `q ≡ 1 (mod 4)` and `c ∈ {1, 3}`, at most one odd `p` has `phi3 p = c * q ^ j`
with `j ≥ 1` (`phi3_eq_mul_prime_pow_unique`), a statement that does not mention odd perfect
numbers. Hence there are at most two escape rows (`card_escapeRows_le_two`). The proof is
elementary: unique factorization in the Eisenstein integers reads each escape row off a power
of one fixed element `ρ ≡ 1 (mod 4)` or of its conjugate (`exists_normalized_root`), and a
2-adic argument on powers of an element `≡ 1 (mod 4)` (`eisenstein_pow_linear_eq_one_unique`,
`eisenstein_pow_linear_star_ne_one`) shows that two rows of the same shape coincide.

Hence, with no classical input, `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 7`, `ω(N) ≤ 5 * T + 7`,
`N < 2 ^ 4 ^ (5 * T + 7)`, and for each bound on the total excess only finitely many odd
perfect numbers exist. The classical theorems of Nagell and Ljunggren would give at most one
escape row and hence `6` in place of `7` (`ConditionalSupport`). The total excess itself is not
bounded here, so this does not prove the conjecture.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- An escape row is an odd prime `p` with `phi3 p = q ^ j` or `phi3 p = 3 * q ^ j`, `j ≥ 1`. -/
theorem phi3_escapeRow {N q p : ℕ} (h : OddPerfect N) (hp : p ∈ escapeRows N q) :
    Odd p ∧ ∃ j, 1 ≤ j ∧ (phi3 p = q ^ j ∨ phi3 p = 3 * q ^ j) := by
  obtain ⟨hpS, hr⟩ := mem_escapeRows.mp hp
  simp only [squarePrimes, Finset.mem_filter] at hpS
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpS.1
  refine ⟨Odd.of_dvd_nat h.odd (Nat.dvd_of_mem_primeFactors hpS.1), ?_⟩
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
    refine ⟨k, ?_, Or.inr (by rw [hn, hk])⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk; omega
    · exact h0
  · have hall : ∀ {d : ℕ}, d.Prime → d ∣ phi3 p → d = q := by
      intro d hd hdd
      rcases hr d hd hdd with e | e
      · exact absurd (e ▸ hdd) h3
      · exact e
    obtain ⟨k, hk⟩ : ∃ k, phi3 p = q ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) hall⟩
    refine ⟨k, ?_, Or.inl hk⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk; omega
    · exact h0

/-- For `z ≡ 1 (mod 4)`, `z ≠ 1` and even `ℓ`: if the linear form `L` has `L (z ^ n) = 1` and
`L (z ^ m) = 1` or `L ((star z) ^ m) = 1`, then `n = m`. -/
private theorem pow_eq_of_eisLin {z : Eis} (hz : z ≠ 1) (hre : (4 : ℤ) ∣ z.re - 1)
    (him : (4 : ℤ) ∣ z.im) {ℓ : ℤ} (hℓ : Even ℓ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h1 : eisLin ℓ (z ^ n) = 1)
    (h2 : eisLin ℓ (z ^ m) = 1 ∨ eisLin ℓ ((star z) ^ m) = 1) : n = m := by
  rcases h2 with h2 | h2
  · exact eisenstein_pow_linear_eq_one_unique hz hre him ℓ hn hm h1 h2
  · exact absurd h2 (eisenstein_pow_linear_star_ne_one hz hre him hℓ hℓ hn hm h1)

/-- Let `q` be a prime that is `1` modulo `4` and `c` be `1` or `3`. At most one odd `p` has
`phi3 p = c * q ^ j` with `j ≥ 1`. Elementary; the classical theorems of Nagell and Ljunggren
say more. -/
theorem phi3_eq_mul_prime_pow_unique {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) {c : ℕ}
    (hc : c = 1 ∨ c = 3) {p p' j j' : ℕ} (hp : Odd p) (hp' : Odd p') (hj : 1 ≤ j) (hj' : 1 ≤ j')
    (h : phi3 p = c * q ^ j) (h' : phi3 p' = c * q ^ j') : p = p' := by
  obtain ⟨ρ, hρ1, hre, him, hrow⟩ := exists_normalized_root hq hq4
  have hs1 : star ρ ≠ 1 := fun e => hρ1 (by simpa using congrArg star e)
  have hsre : (4 : ℤ) ∣ (star ρ).re - 1 := by
    obtain ⟨a, ha⟩ := hre
    obtain ⟨b, hb⟩ := him
    exact ⟨a - b, by rw [QuadraticAlgebra.re_star]; linear_combination ha - hb⟩
  have hsim : (4 : ℤ) ∣ (star ρ).im := by
    obtain ⟨b, hb⟩ := him
    exact ⟨-b, by rw [QuadraticAlgebra.im_star, hb]; ring⟩
  have hjj : ∀ ℓ : ℤ, Even ℓ →
      (eisLin ℓ (ρ ^ j) = 1 ∨ eisLin ℓ ((star ρ) ^ j) = 1) →
      (eisLin ℓ (ρ ^ j') = 1 ∨ eisLin ℓ ((star ρ) ^ j') = 1) → j = j' := by
    intro ℓ hℓ hra hrb
    rcases hra with hra | hra
    · exact pow_eq_of_eisLin hρ1 hre him hℓ hj hj' hra hrb
    · exact pow_eq_of_eisLin hs1 hsre hsim hℓ hj hj' hra (by rw [star_star]; exact hrb.symm)
  have hjk : j = j' := by
    rcases hc with rfl | rfl
    · rw [one_mul] at h h'
      refine hjj 0 ⟨0, by norm_num⟩ ?_ ?_
      · simpa [eisLin_apply] using (hrow p j hp hj).1 (by rw [← h]; rfl)
      · simpa [eisLin_apply] using (hrow p' j' hp' hj').1 (by rw [← h']; rfl)
    · refine hjj (-2) ⟨-1, by norm_num⟩ ?_ ?_
      · rw [eisLin_apply, eisLin_apply]
        exact ((hrow p j hp hj).2 (by rw [← h]; rfl)).imp (fun e => by linarith)
          (fun e => by linarith)
      · rw [eisLin_apply, eisLin_apply]
        exact ((hrow p' j' hp' hj').2 (by rw [← h']; rfl)).imp (fun e => by linarith)
          (fun e => by linarith)
  exact phi3_strictMono.injective (by rw [h, h', hjk])

/-- At most two escape rows, for every special prime. No classical input. -/
theorem card_escapeRows_le_two {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : (escapeRows N q).card ≤ 2 := by
  have hq4 : q % 4 = 1 := (special_mod_four h hq hodd).1
  have hnd : ∀ j, ¬ 3 ∣ q ^ j := fun j h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hinj : Set.InjOn (fun p => decide (3 ∣ phi3 p)) (escapeRows N q : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨hao, j, hj, hsa | hsa⟩ := phi3_escapeRow h ha <;>
      obtain ⟨hbo, k, hk, hsb | hsb⟩ := phi3_escapeRow h hb
    · exact phi3_eq_mul_prime_pow_unique hq hq4 (Or.inl rfl) hao hbo hj hk
        (by rw [hsa, one_mul]) (by rw [hsb, one_mul])
    · simp [hsa, hsb, hnd] at hab
    · simp [hsa, hsb, hnd] at hab
    · exact phi3_eq_mul_prime_pow_unique hq hq4 (Or.inr rfl) hao hbo hj hk hsa hsb
  have := Finset.card_le_card_of_injOn _ (t := (Finset.univ : Finset Bool))
    (fun x _ => Finset.mem_univ _) hinj
  simpa using this

/-- For every special prime `q` of an odd perfect number `N`, with `T` the total excess,
`ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 7`. No classical input. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_seven {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 7 := by
  have := card_primeFactors_add_two_mul_le_five_excess_add_escape h hq hodd
  have := card_escapeRows_le_two h hq hodd
  omega

/-- For every special prime, `ω(N) ≤ 5 * T + 7`, where `T` is the total excess. -/
theorem card_primeFactors_le_five_excess_add_seven {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.primeFactors.card ≤ 5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 7 := by
  have := card_primeFactors_add_two_mul_le_five_excess_add_seven h hq hodd
  omega

/-- For every special prime, `N < 2 ^ 4 ^ (5 * T + 7)`, where `T` is the total excess. -/
theorem lt_two_pow_four_pow_excess {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N < 2 ^ 4 ^ (5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 7) :=
  (lt_two_pow_four_pow h).trans_le (Nat.pow_le_pow_right two_pos
    (Nat.pow_le_pow_right (by norm_num) (card_primeFactors_le_five_excess_add_seven h hq hodd)))

/-- In Euler's form `N = q ^ a * m ^ 2` with `q ∤ m`, `ω(N) ≤ 5 * (Ω(m) - ω(m)) + 7`. -/
theorem cardDistinctFactors_le_five_mul_sub_add_seven {N q a m : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hqm : ¬ q ∣ m) (hN' : N = q ^ a * m ^ 2) :
    ArithmeticFunction.cardDistinctFactors N ≤
      5 * (ArithmeticFunction.cardFactors m - ArithmeticFunction.cardDistinctFactors m) + 7 := by
  obtain ⟨hodd, hT⟩ := euler_form_excess h hq hqm hN'
  rw [cardDistinctFactors_eq_card_primeFactors, ← hT]
  exact card_primeFactors_le_five_excess_add_seven h hq hodd

/-- For each bound `T` on the total excess only finitely many odd perfect numbers exist. -/
theorem finite_of_excess_le (T : ℕ) : {N : ℕ | ∃ q, OddPerfect N ∧ q.Prime ∧
    Odd (N.factorization q) ∧
    ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) ≤ T}.Finite := by
  refine (Set.finite_lt_nat (2 ^ 4 ^ (5 * T + 7))).subset ?_
  rintro N ⟨q, h, hq, hodd, hT⟩
  exact (lt_two_pow_four_pow_excess h hq hodd).trans_le
    (Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_right (by norm_num) (by omega)))

end OddPerfect

#print axioms OddPerfect.phi3_escapeRow
#print axioms OddPerfect.phi3_eq_mul_prime_pow_unique
#print axioms OddPerfect.card_escapeRows_le_two
#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_seven
#print axioms OddPerfect.card_primeFactors_le_five_excess_add_seven
#print axioms OddPerfect.lt_two_pow_four_pow_excess
#print axioms OddPerfect.cardDistinctFactors_le_five_mul_sub_add_seven
#print axioms OddPerfect.finite_of_excess_le
