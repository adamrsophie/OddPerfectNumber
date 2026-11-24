import Mathlib

/-!
# Mutual rows for `ℓ = 5` and `ℓ = 7`

For primes `p` and `q` and exponents `α, β ≥ 1`, the pair of equations
`1 + p + ... + p ^ (ℓ - 1) = ℓ q ^ α` and `1 + q + ... + q ^ (ℓ - 1) = ℓ p ^ β` has no
solution for `ℓ = 5` (`no_mutual_rows_five`) and for `ℓ = 7` (`no_mutual_rows_seven`).

Reducing the second equation modulo `p` gives `q ^ ℓ ≡ 1`, and the first gives
`ℓ q ^ α ≡ 1`, so `p ∣ ℓ ^ ℓ - 1`; by symmetry also `q ∣ ℓ ^ ℓ - 1`. Since
`5 ^ 5 - 1 = 2 ^ 2 * 11 * 71` and `7 ^ 7 - 1 = 2 * 3 * 29 * 4733`, a finite check of the
first equation remains: for `α = 1` it is a numeral comparison, and for `α ≥ 2` the square
`q ^ 2` does not divide the left side in any of the cases.

The argument, for `ℓ = 5`, is in the proof of Proposition 6.2 of Hagis, Math. Comp. 35
(1980); no novelty is claimed.
-/

open Finset

namespace OddPerfect

namespace MutualRowsSmall

/-- Mutual rows force `p ∣ ℓ ^ ℓ - 1`. -/
private theorem dvd_pow_self_sub_one {l p q α β : ℕ} (hl : 1 ≤ l)
    (h1 : ∑ i ∈ range l, p ^ i = l * q ^ α) (h2 : ∑ i ∈ range l, q ^ i = l * p ^ β)
    (hβ : 1 ≤ β) : p ∣ l ^ l - 1 := by
  have e1 := congrArg (Nat.cast : ℕ → ZMod p) h1
  have e2 := congrArg (Nat.cast : ℕ → ZMod p) h2
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul, ZMod.natCast_self] at e1 e2
  rw [zero_pow (by omega : β ≠ 0), mul_zero] at e2
  have hql : (q : ZMod p) ^ l = 1 := by
    have := geom_sum_mul (q : ZMod p) l
    rw [e2, zero_mul] at this
    exact sub_eq_zero.mp this.symm
  have hs : ∑ i ∈ range l, (0 : ZMod p) ^ i = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    rw [Finset.sum_range_succ']
    simp
  rw [hs] at e1
  have key : ((l ^ l : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    calc (l : ZMod p) ^ l = (l : ZMod p) ^ l * ((q : ZMod p) ^ l) ^ α := by
          rw [hql, one_pow, mul_one]
      _ = ((l : ZMod p) * (q : ZMod p) ^ α) ^ l := by ring
      _ = 1 := by rw [← e1, one_pow]
  rw [ZMod.natCast_eq_natCast_iff] at key
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp key.symm

/-- The finite check for `ℓ = 5`. -/
private theorem five_check {p q α : ℕ} (hp : p = 2 ∨ p = 11 ∨ p = 71)
    (hq : q = 2 ∨ q = 11 ∨ q = 71) (hα : 1 ≤ α) (h : ∑ i ∈ range 5, p ^ i = 5 * q ^ α) :
    False := by
  rcases Nat.lt_or_ge α 2 with hα1 | hα2
  · obtain rfl : α = 1 := by omega
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      norm_num [Finset.sum_range_succ] at h
  · have hd : q ^ 2 ∣ ∑ i ∈ range 5, p ^ i :=
      h ▸ Dvd.dvd.mul_left (pow_dvd_pow q hα2) 5
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      norm_num [Finset.sum_range_succ] at hd

/-- The finite check for `ℓ = 7`. -/
private theorem seven_check {p q α : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 29 ∨ p = 4733)
    (hq : q = 2 ∨ q = 3 ∨ q = 29 ∨ q = 4733) (hα : 1 ≤ α)
    (h : ∑ i ∈ range 7, p ^ i = 7 * q ^ α) : False := by
  rcases Nat.lt_or_ge α 2 with hα1 | hα2
  · obtain rfl : α = 1 := by omega
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      norm_num [Finset.sum_range_succ] at h
  · have hd : q ^ 2 ∣ ∑ i ∈ range 7, p ^ i :=
      h ▸ Dvd.dvd.mul_left (pow_dvd_pow q hα2) 7
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      norm_num [Finset.sum_range_succ] at hd

/-- The prime divisors of `5 ^ 5 - 1 = 2 ^ 2 * 11 * 71`. -/
private theorem prime_dvd_five {p : ℕ} (hp : p.Prime) (h : p ∣ 5 ^ 5 - 1) :
    p = 2 ∨ p = 11 ∨ p = 71 := by
  have h' : p ∣ 2 ^ 2 * 11 * 71 := by simpa using h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
  · rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h'))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h'))

/-- The prime divisors of `7 ^ 7 - 1 = 2 * 3 * 29 * 4733`. -/
private theorem prime_dvd_seven {p : ℕ} (hp : p.Prime) (h : p ∣ 7 ^ 7 - 1) :
    p = 2 ∨ p = 3 ∨ p = 29 ∨ p = 4733 := by
  have h' : p ∣ 2 * 3 * 29 * 4733 := by simpa using h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
  · rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h'))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h')))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h')))

end MutualRowsSmall

open MutualRowsSmall

/-- **No mutual rows for `ℓ = 5`.** There are no primes `p`, `q` and exponents `α, β ≥ 1`
with `1 + p + p ^ 2 + p ^ 3 + p ^ 4 = 5 q ^ α` and `1 + q + q ^ 2 + q ^ 3 + q ^ 4 = 5 p ^ β`.
The argument is in the proof of Proposition 6.2 of Hagis, Math. Comp. 35 (1980); no
novelty is claimed. -/
theorem no_mutual_rows_five {p q α β : ℕ} (hp : p.Prime) (hq : q.Prime) (hα : 1 ≤ α)
    (hβ : 1 ≤ β) (h1 : ∑ i ∈ range 5, p ^ i = 5 * q ^ α)
    (h2 : ∑ i ∈ range 5, q ^ i = 5 * p ^ β) : False :=
  five_check (prime_dvd_five hp (dvd_pow_self_sub_one (by norm_num) h1 h2 hβ))
    (prime_dvd_five hq (dvd_pow_self_sub_one (by norm_num) h2 h1 hα)) hα h1

/-- **No mutual rows for `ℓ = 7`.** There are no primes `p`, `q` and exponents `α, β ≥ 1`
with `1 + p + ... + p ^ 6 = 7 q ^ α` and `1 + q + ... + q ^ 6 = 7 p ^ β`.
The same argument as for `ℓ = 5`, which is in the proof of Proposition 6.2 of Hagis,
Math. Comp. 35 (1980); no novelty is claimed. -/
theorem no_mutual_rows_seven {p q α β : ℕ} (hp : p.Prime) (hq : q.Prime) (hα : 1 ≤ α)
    (hβ : 1 ≤ β) (h1 : ∑ i ∈ range 7, p ^ i = 7 * q ^ α)
    (h2 : ∑ i ∈ range 7, q ^ i = 7 * p ^ β) : False :=
  seven_check (prime_dvd_seven hp (dvd_pow_self_sub_one (by norm_num) h1 h2 hβ))
    (prime_dvd_seven hq (dvd_pow_self_sub_one (by norm_num) h2 h1 hα)) hα h1

end OddPerfect

#print axioms OddPerfect.no_mutual_rows_five
#print axioms OddPerfect.no_mutual_rows_seven
