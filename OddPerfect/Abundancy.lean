import OddPerfect.Basic
import Mathlib

/-!
# The abundancy index

`abundancy n = σ(n)/n` as an exact rational, with its basic multiplicative and
monotonicity properties, terminal contradiction lemmas for perfect numbers, and the
application that an odd perfect number has at least three distinct prime factors.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The abundancy index `σ(n)/n` as an exact rational. -/
def abundancy (n : ℕ) : ℚ := (σ 1 n : ℚ) / n

/-- For `n ≠ 0`, the abundancy is the sum of the reciprocals of the divisors. -/
theorem abundancy_eq_sum_inv {n : ℕ} (hn : n ≠ 0) :
    abundancy n = ∑ e ∈ n.divisors, (e : ℚ)⁻¹ := by
  have h : ∑ d ∈ n.divisors, d = ∑ d ∈ n.divisors, n / d := (Nat.sum_div_divisors n id).symm
  rw [abundancy, sigma_one_apply, h, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' := Nat.dvd_of_mem_divisors he
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [Nat.cast_div he' he0]
  field_simp

/-- Abundancy is multiplicative on coprime arguments. -/
theorem abundancy_mul_of_coprime {a b : ℕ} (h : a.Coprime b) :
    abundancy (a * b) = abundancy a * abundancy b := by
  rw [abundancy, abundancy, abundancy, isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  rw [div_mul_div_comm]

/-- Abundancy of a prime power as a geometric sum in `1/p`. -/
theorem abundancy_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    abundancy (p ^ a) = ∑ i ∈ Finset.range (a + 1), ((p : ℚ)⁻¹) ^ i := by
  rw [abundancy_eq_sum_inv (pow_ne_zero _ hp.ne_zero), Nat.sum_divisors_prime_pow hp]
  push_cast
  simp [inv_pow]

/-- Abundancy of a prime power is strictly below `p/(p-1)`. -/
theorem abundancy_prime_pow_lt {p : ℕ} (hp : p.Prime) (a : ℕ) :
    abundancy (p ^ a) < (p : ℚ) / (p - 1) := by
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : (0 : ℚ) < (p : ℚ)⁻¹ := by positivity
  have hr1 : (p : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hpos : (0 : ℚ) < 1 - (p : ℚ)⁻¹ := by linarith
  have key : (p : ℚ) / (p - 1) = 1 / (1 - (p : ℚ)⁻¹) := by
    field_simp
  rw [abundancy_prime_pow hp, key, lt_div_iff₀ hpos, geom_sum_mul_neg]
  have : 0 < (p : ℚ)⁻¹ ^ (a + 1) := pow_pos hr0 _
  linarith

/-- Abundancy of `p ^ a` is monotone in `a`. -/
theorem abundancy_prime_pow_mono {p : ℕ} (hp : p.Prime) {a b : ℕ} (h : a ≤ b) :
    abundancy (p ^ a) ≤ abundancy (p ^ b) := by
  rw [abundancy_prime_pow hp, abundancy_prime_pow hp]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr (by omega)
  · intro i _ _
    positivity

/-- A positive power of `p` has abundancy at least `1 + 1/p`. -/
theorem one_add_inv_le_abundancy_prime_pow {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 0 < a) :
    1 + (p : ℚ)⁻¹ ≤ abundancy (p ^ a) := by
  have h := abundancy_prime_pow_mono hp ha
  rw [abundancy_prime_pow hp 1] at h
  simpa [Finset.sum_range_succ] using h

/-- Abundancy is monotone along divisibility. -/
theorem abundancy_le_of_dvd {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    abundancy d ≤ abundancy n := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  rw [abundancy_eq_sum_inv hn, abundancy_eq_sum_inv hd0]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hn hd)
  intro i _ _
  positivity

/-- Abundancy is strictly monotone along proper divisibility. -/
theorem abundancy_lt_of_dvd_of_ne {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (hne : d ≠ n) :
    abundancy d < abundancy n := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  rw [abundancy_eq_sum_inv hn, abundancy_eq_sum_inv hd0]
  apply Finset.sum_lt_sum_of_subset (Nat.divisors_subset_of_dvd hn hd)
    (i := n) (Nat.mem_divisors_self n hn)
  · intro hmem
    exact hne (Nat.dvd_antisymm hd (Nat.dvd_of_mem_divisors hmem))
  · have : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  · intro j _ _
    positivity

/-- A positive integer is perfect exactly when its abundancy is two. -/
theorem perfect_iff_abundancy_eq_two {n : ℕ} (hn : 0 < n) :
    n.Perfect ↔ abundancy n = 2 := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn, abundancy, ← sigma_one_apply,
    div_eq_iff hn0]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- Abundancy is the product of the abundancies of the prime power components. -/
theorem abundancy_eq_prod_primeFactors {n : ℕ} (hn : n ≠ 0) :
    abundancy n = ∏ p ∈ n.primeFactors, abundancy (p ^ n.factorization p) := by
  have h1 : abundancy 1 = 1 := by simp [abundancy]
  exact Nat.multiplicative_factorization abundancy (fun _ _ h => abundancy_mul_of_coprime h)
    h1 hn

/-- For `n > 1`, abundancy is strictly below `∏ p/(p-1)` over its prime factors. -/
theorem abundancy_lt_prod {n : ℕ} (hn : 1 < n) :
    abundancy n < ∏ p ∈ n.primeFactors, ((p : ℚ) / (p - 1)) := by
  rw [abundancy_eq_prod_primeFactors (by omega)]
  apply Finset.prod_lt_prod_of_nonempty₀
  · intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    rw [abundancy_eq_sum_inv (pow_ne_zero _ hp'.ne_zero)]
    exact Finset.sum_pos (fun i hi => by
      have : (0 : ℚ) < i := by exact_mod_cast Nat.pos_of_mem_divisors hi
      positivity) (Nat.nonempty_divisors.mpr (pow_ne_zero _ hp'.ne_zero))
  · intro p hp
    exact abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hp) _
  · exact Nat.nonempty_primeFactors.mpr hn

/-- A divisor with abundancy above two excludes perfection. -/
theorem not_perfect_of_dvd_of_two_lt_abundancy {d n : ℕ} (hd : d ∣ n)
    (h : 2 < abundancy d) : ¬ n.Perfect := by
  intro hp
  have := abundancy_le_of_dvd hp.2.ne' hd
  rw [(perfect_iff_abundancy_eq_two hp.2).mp hp] at this
  linarith

/-- A proper divisor with abundancy at least two excludes perfection. -/
theorem not_perfect_of_dvd_of_two_le_abundancy {d n : ℕ} (hd : d ∣ n) (hne : d ≠ n)
    (h : 2 ≤ abundancy d) : ¬ n.Perfect := by
  intro hp
  have := abundancy_lt_of_dvd_of_ne hp.2.ne' hd hne
  rw [(perfect_iff_abundancy_eq_two hp.2).mp hp] at this
  linarith

/-- If the full prime support cannot reach abundancy two, the number is not perfect. -/
theorem not_perfect_of_prod_le_two {n : ℕ} (hn : 1 < n)
    (h : ∏ p ∈ n.primeFactors, ((p : ℚ) / (p - 1)) ≤ 2) : ¬ n.Perfect := by
  intro hp
  have := abundancy_lt_prod hn
  rw [(perfect_iff_abundancy_eq_two hp.2).mp hp] at this
  linarith

/-- The bound `x/(x-1) ≤ m/(m-1)` for natural numbers `2 ≤ m ≤ x`. -/
private theorem div_sub_one_le {m x : ℕ} (hm : 2 ≤ m) (hx : m ≤ x) :
    (x : ℚ) / (x - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hx' : (m : ℚ) ≤ x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

namespace OddPerfect

/-- An odd perfect number has at least three distinct prime factors. -/
theorem three_le_card_primeFactors {N : ℕ} (h : OddPerfect N) : 3 ≤ N.primeFactors.card := by
  have hodd : ∀ p ∈ N.primeFactors, 3 ≤ p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hne : p ≠ 2 := by
      rintro rfl; exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
    have := hp'.two_le
    omega
  have hfive : ∀ p ∈ N.primeFactors, p ≠ 3 → 5 ≤ p := by
    intro p hp h3
    have hp' := Nat.prime_of_mem_primeFactors hp
    have := hodd p hp
    by_contra hlt
    have h4 : p = 4 := by omega
    subst h4
    exact absurd hp' (by norm_num)
  have hf3 : ∀ p ∈ N.primeFactors, (p : ℚ) / (p - 1) ≤ 3 / 2 := by
    intro p hp
    have := div_sub_one_le (m := 3) (by norm_num) (hodd p hp)
    norm_num at this ⊢
    exact this
  have hf5 : ∀ p ∈ N.primeFactors, p ≠ 3 → (p : ℚ) / (p - 1) ≤ 5 / 4 := by
    intro p hp h3
    have := div_sub_one_le (m := 5) (by norm_num) (hfive p hp h3)
    norm_num at this ⊢
    exact this
  have hpos : ∀ p ∈ N.primeFactors, (0 : ℚ) ≤ (p : ℚ) / (p - 1) := by
    intro p hp
    have : (3 : ℚ) ≤ p := by exact_mod_cast hodd p hp
    apply div_nonneg <;> linarith
  by_contra hlt
  rw [not_le] at hlt
  by_cases h1 : N = 1
  · subst h1
    have hp1 := h.perfect
    simp [Nat.Perfect] at hp1
  have hN : 1 < N := by have := h.pos; omega
  apply not_perfect_of_prod_le_two hN _ h.perfect
  interval_cases hc : N.primeFactors.card
  · rw [Finset.card_eq_zero.mp hc]; norm_num
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hmem : p ∈ N.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    rw [hp, Finset.prod_singleton]
    linarith [hf3 p hmem]
  · obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp hc
    have hpm : p ∈ N.primeFactors := by rw [hs]; simp
    have hqm : q ∈ N.primeFactors := by rw [hs]; simp
    rw [hs, Finset.prod_pair hpq]
    by_cases hp3 : p = 3
    · have hq3 : q ≠ 3 := by rintro rfl; exact hpq hp3
      calc (p : ℚ) / (p - 1) * (q / (q - 1)) ≤ 3 / 2 * (5 / 4) :=
            mul_le_mul (hf3 p hpm) (hf5 q hqm hq3) (hpos q hqm) (by norm_num)
        _ ≤ 2 := by norm_num
    · calc (p : ℚ) / (p - 1) * (q / (q - 1)) ≤ 5 / 4 * (3 / 2) :=
            mul_le_mul (hf5 p hpm hp3) (hf3 q hqm) (hpos q hqm) (by norm_num)
        _ ≤ 2 := by norm_num

end OddPerfect

#print axioms abundancy_eq_sum_inv
#print axioms abundancy_mul_of_coprime
#print axioms abundancy_prime_pow
#print axioms abundancy_prime_pow_lt
#print axioms abundancy_prime_pow_mono
#print axioms one_add_inv_le_abundancy_prime_pow
#print axioms abundancy_le_of_dvd
#print axioms abundancy_lt_of_dvd_of_ne
#print axioms perfect_iff_abundancy_eq_two
#print axioms abundancy_eq_prod_primeFactors
#print axioms abundancy_lt_prod
#print axioms not_perfect_of_dvd_of_two_lt_abundancy
#print axioms not_perfect_of_dvd_of_two_le_abundancy
#print axioms not_perfect_of_prod_le_two
#print axioms OddPerfect.three_le_card_primeFactors
