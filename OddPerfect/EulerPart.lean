import OddPerfect.SpecialPrime
import OddPerfect.ClosedLoop
import OddPerfect.Valuation

/-!
# The Euler part of an odd perfect number

Identities and congruences for Euler's form `N = q ^ k * m ^ 2` of an odd perfect number,
with `q` the special prime and `q ∤ m`.

* The index `i = σ(m ^ 2) / q ^ k`: `σ(m ^ 2) = q ^ k i`, `σ(q ^ k) i = 2 m ^ 2`,
  `i = gcd(m ^ 2, σ(m ^ 2))`, `i` odd and `i ≥ 3`.
* Hornfeck: `q ^ k = σ(m ^ 2) / gcd(σ(m ^ 2), 2 m ^ 2)`, so `m` determines `N`.
* Deficiency: `2 m ^ 2 - σ(m ^ 2) = i σ(q ^ (k - 1))`, and it divides `m ^ 2` iff `k = 1`.
* Modulo 8: `N ≡ q (mod 8)` and `σ(m ^ 2) ≡ 1 (mod 4)` iff `q ≡ k (mod 8)`.
* Dris and Luca: `v_l(σ(p ^ (l - 1))) ≤ 1` for odd primes `l` (so `25 ∤ σ(p ^ 4)`), and
  their Lemma 2 for odd `p`.
* Small facts: `q ^ k + 8 ≤ m ^ 2`, `m < q → k = 1`, and no two primes divide an odd
  perfect number exactly once.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Basic facts about an Euler form `N = q ^ k * m ^ 2` with `q ∤ m`. -/
private lemma setup {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    m ≠ 0 ∧ Odd k ∧ q % 4 = 1 ∧ k % 4 = 1 ∧ m % 2 = 1 ∧
      σ 1 (q ^ k) * σ 1 (m ^ 2) = 2 * N := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hcop : Nat.Coprime (q ^ k) (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow k 2
  have hfac : N.factorization q = k := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have hk : Odd k := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  have h4 := special_mod_four h hq (hfac ▸ hk)
  rw [hfac] at h4
  have hmo : m % 2 = 1 :=
    Nat.odd_iff.mp (h.odd.of_dvd_nat (hN ▸ (dvd_pow_self m two_ne_zero).mul_left _))
  refine ⟨hm, hk, h4.1, h4.2, hmo, ?_⟩
  rw [← isMultiplicative_sigma.map_mul_of_coprime hcop, ← hN]
  exact h.sigma_eq

/-- `σ(p ^ (j + 1)) = σ(p ^ j) + p ^ (j + 1)`. -/
private lemma sigma_succ_add {p : ℕ} (hp : p.Prime) (j : ℕ) :
    σ 1 (p ^ (j + 1)) = σ 1 (p ^ j) + p ^ (j + 1) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ _ (j + 1)]

/-- `σ(p ^ (j + 1)) = 1 + p σ(p ^ j)`. -/
private lemma sigma_succ_mul {p : ℕ} (hp : p.Prime) (j : ℕ) :
    σ 1 (p ^ (j + 1)) = 1 + p * σ 1 (p ^ j) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-! ## The index -/

/-- The index `σ(m ^ 2) / q ^ k` of an Euler form `q ^ k * m ^ 2`. -/
def eulerIndex (q k m : ℕ) : ℕ := σ 1 (m ^ 2) / q ^ k

variable {N q k m : ℕ}

/-- `σ(m ^ 2) = q ^ k * i`. -/
theorem sigma_sq_eq_mul_eulerIndex (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : σ 1 (m ^ 2) = q ^ k * eulerIndex q k m :=
  (Nat.mul_div_cancel' (pow_dvd_sigma_sq h hq hN hqm)).symm

/-- `σ(q ^ k) * i = 2 * m ^ 2`. -/
theorem sigma_special_mul_eulerIndex (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : σ 1 (q ^ k) * eulerIndex q k m = 2 * m ^ 2 := by
  obtain ⟨-, -, -, -, -, hprod⟩ := setup h hq hN hqm
  have hs := sigma_sq_eq_mul_eulerIndex h hq hN hqm
  rw [hs, hN] at hprod
  have hqk : 0 < q ^ k := pow_pos hq.pos k
  refine Nat.eq_of_mul_eq_mul_left hqk ?_
  calc q ^ k * (σ 1 (q ^ k) * eulerIndex q k m) = σ 1 (q ^ k) * (q ^ k * eulerIndex q k m) := by
        ring
    _ = q ^ k * (2 * m ^ 2) := by rw [hprod]; ring

/-- The index is odd. -/
theorem odd_eulerIndex (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : Odd (eulerIndex q k m) := by
  have ho := odd_sigma_sq h hq hN hqm
  rw [sigma_sq_eq_mul_eulerIndex h hq hN hqm] at ho
  exact (Nat.odd_mul.mp ho).2

/-- The index is at least 3 (Dandapat, Hunsucker, and Pomerance). -/
theorem three_le_eulerIndex (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : 3 ≤ eulerIndex q k m := by
  obtain ⟨-, hk, -, -, -, -⟩ := setup h hq hN hqm
  have ho := odd_eulerIndex h hq hN hqm
  have h1 : eulerIndex q k m ≠ 1 := by
    intro h1
    apply not_sigma_sq_eq_special_pow h hq hN hqm hk
    rw [sigma_sq_eq_mul_eulerIndex h hq hN hqm, h1, mul_one]
  obtain ⟨j, hj⟩ := ho
  omega

/-- The index divides `m ^ 2`. -/
theorem eulerIndex_dvd_sq (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : eulerIndex q k m ∣ m ^ 2 := by
  have hd : eulerIndex q k m ∣ 2 * m ^ 2 :=
    ⟨σ 1 (q ^ k), by rw [← sigma_special_mul_eulerIndex h hq hN hqm, mul_comm]⟩
  exact ((Nat.coprime_two_right.mpr (odd_eulerIndex h hq hN hqm))).dvd_of_dvd_mul_left hd

/-- The index is `gcd(m ^ 2, σ(m ^ 2))`. -/
theorem eulerIndex_eq_gcd (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    eulerIndex q k m = Nat.gcd (m ^ 2) (σ 1 (m ^ 2)) := by
  have hcop : Nat.Coprime (q ^ k) (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow k 2
  rw [sigma_sq_eq_mul_eulerIndex h hq hN hqm, Nat.gcd_comm,
    Nat.Coprime.gcd_mul_left_cancel _ hcop, Nat.gcd_eq_left (eulerIndex_dvd_sq h hq hN hqm)]

/-- `σ(q ^ k) / 2 = m ^ 2 / i`. -/
theorem sigma_special_div_two (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    σ 1 (q ^ k) / 2 = m ^ 2 / eulerIndex q k m := by
  obtain ⟨-, hk, hq4, -, -, -⟩ := setup h hq hN hqm
  obtain ⟨s, hs⟩ : 2 ∣ σ 1 (q ^ k) := by
    have := succ_dvd_sigma_special (N := q ^ k) hq
    rw [Nat.Prime.factorization_pow hq, Finsupp.single_eq_same] at this
    exact (show 2 ∣ q + 1 by omega).trans (this (by simpa using hk))
  have hi := sigma_special_mul_eulerIndex h hq hN hqm
  have hpos : 0 < eulerIndex q k m := by have := three_le_eulerIndex h hq hN hqm; omega
  rw [hs] at hi
  have : m ^ 2 = s * eulerIndex q k m := by linarith
  rw [hs, this, Nat.mul_div_cancel _ hpos, Nat.mul_div_cancel_left _ two_pos]

/-! ## Hornfeck's lemma -/

/-- Hornfeck: `q ^ k = σ(m ^ 2) / gcd(σ(m ^ 2), 2 m ^ 2)`. -/
theorem special_pow_eq_div_gcd (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    q ^ k = σ 1 (m ^ 2) / Nat.gcd (σ 1 (m ^ 2)) (2 * m ^ 2) := by
  have hpos : 0 < eulerIndex q k m := by have := three_le_eulerIndex h hq hN hqm; omega
  have hg : Nat.gcd (σ 1 (m ^ 2)) (2 * m ^ 2) = eulerIndex q k m := by
    rw [sigma_sq_eq_mul_eulerIndex h hq hN hqm, ← sigma_special_mul_eulerIndex h hq hN hqm,
      Nat.gcd_mul_right, (coprime_sigma_prime_pow hq k).pow_right k |>.symm, one_mul]
  rw [hg, sigma_sq_eq_mul_eulerIndex h hq hN hqm, Nat.mul_div_cancel _ hpos]

/-- Hornfeck: two odd perfect numbers with Euler forms sharing the same `m` are equal. -/
theorem eq_of_euler_form_sq_eq {N₁ N₂ q₁ q₂ k₁ k₂ m : ℕ} (h₁ : OddPerfect N₁)
    (h₂ : OddPerfect N₂) (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hN₁ : N₁ = q₁ ^ k₁ * m ^ 2) (hN₂ : N₂ = q₂ ^ k₂ * m ^ 2)
    (hqm₁ : ¬ q₁ ∣ m) (hqm₂ : ¬ q₂ ∣ m) : N₁ = N₂ := by
  rw [hN₁, hN₂, special_pow_eq_div_gcd h₁ hq₁ hN₁ hqm₁, special_pow_eq_div_gcd h₂ hq₂ hN₂ hqm₂]

/-! ## Deficiency of `m ^ 2` -/

/-- `σ(m ^ 2) < 2 m ^ 2`: the square part is deficient. -/
theorem sigma_sq_lt (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : σ 1 (m ^ 2) < 2 * m ^ 2 := by
  obtain ⟨-, hk, -, -, -, -⟩ := setup h hq hN hqm
  have hi := sigma_special_mul_eulerIndex h hq hN hqm
  have hs := sigma_sq_eq_mul_eulerIndex h hq hN hqm
  have hpos : 0 < eulerIndex q k m := by have := three_le_eulerIndex h hq hN hqm; omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk.pos; omega⟩
  rw [sigma_succ_add hq] at hi
  have : 0 < σ 1 (q ^ j) := sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)
  rw [hs, ← hi]
  nlinarith

/-- The deficiency `2 m ^ 2 - σ(m ^ 2)` equals `i * σ(q ^ (k - 1))`. -/
theorem deficiency_sq_eq (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    2 * m ^ 2 - σ 1 (m ^ 2) = eulerIndex q k m * σ 1 (q ^ (k - 1)) := by
  obtain ⟨-, hk, -, -, -, -⟩ := setup h hq hN hqm
  have hi := sigma_special_mul_eulerIndex h hq hN hqm
  have hs := sigma_sq_eq_mul_eulerIndex h hq hN hqm
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk.pos; omega⟩
  rw [sigma_succ_add hq] at hi
  rw [hs, ← hi, add_mul, Nat.add_sub_cancel, Nat.add_sub_cancel, mul_comm]

/-- Dris: the deficiency `2 m ^ 2 - σ(m ^ 2)` divides `m ^ 2` iff `k = 1`. -/
theorem deficiency_sq_dvd_iff (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    2 * m ^ 2 - σ 1 (m ^ 2) ∣ m ^ 2 ↔ k = 1 := by
  rw [deficiency_sq_eq h hq hN hqm]
  constructor
  · intro hd
    obtain ⟨-, hk, -, -, -, -⟩ := setup h hq hN hqm
    have hi := sigma_special_mul_eulerIndex h hq hN hqm
    have hpos : 0 < eulerIndex q k m := by have := three_le_eulerIndex h hq hN hqm; omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk.pos; omega⟩
    rw [Nat.add_sub_cancel] at hd
    have h2 : eulerIndex q (j + 1) m * σ 1 (q ^ j) ∣ eulerIndex q (j + 1) m * σ 1 (q ^ (j + 1)) := by
      rw [mul_comm _ (σ 1 (q ^ (j + 1))), hi]
      exact hd.mul_left 2
    have h3 := Nat.dvd_of_mul_dvd_mul_left hpos h2
    rw [sigma_succ_mul hq] at h3
    have h4 : σ 1 (q ^ j) = 1 := Nat.dvd_one.mp ((Nat.dvd_add_left (dvd_mul_left _ q)).mp h3)
    rcases j with _ | j
    · rfl
    · rw [sigma_succ_mul hq] at h4
      have := sigma_pos 1 (q ^ j) (pow_ne_zero _ hq.ne_zero)
      have := hq.pos
      nlinarith
  · rintro rfl
    simp only [Nat.sub_self, pow_zero, isMultiplicative_sigma.map_one, mul_one]
    exact eulerIndex_dvd_sq h hq hN hqm

/-- Dris: `σ(m ^ 2) / q` divides `m ^ 2` iff `k = 1`. -/
theorem sigma_sq_div_dvd_iff (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    σ 1 (m ^ 2) / q ∣ m ^ 2 ↔ k = 1 := by
  obtain ⟨-, hk, -, -, -, -⟩ := setup h hq hN hqm
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk.pos; omega⟩
  rw [sigma_sq_eq_mul_eulerIndex h hq hN hqm, pow_succ,
    show q ^ j * q * eulerIndex q (j + 1) m = q * (q ^ j * eulerIndex q (j + 1) m) by ring,
    Nat.mul_div_cancel_left _ hq.pos]
  constructor
  · intro hd
    rcases j with _ | j
    · rfl
    · exfalso
      have : q ∣ m ^ 2 := (dvd_pow_self q (Nat.succ_ne_zero j)).mul_right _ |>.trans hd
      exact hqm (hq.dvd_of_dvd_pow this)
  · intro hj
    obtain rfl : j = 0 := by omega
    rw [pow_zero, one_mul]
    exact eulerIndex_dvd_sq h hq hN hqm

/-! ## Congruences modulo 8 -/

/-- An odd perfect number is congruent to its special prime modulo 8. -/
theorem mod_eight_eq_special (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : N % 8 = q % 8 := by
  obtain ⟨-, ⟨j, rfl⟩, hq4, -, hmo, -⟩ := setup h hq hN hqm
  have hm8 : m ^ 2 % 8 = 1 := by
    have : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
    rw [Nat.pow_mod]; rcases this with h | h | h | h <;> simp [h]
  have hq8 : (q ^ 2) ^ j % 8 = 1 := by
    have : q ^ 2 % 8 = 1 := by
      have : q % 8 = 1 ∨ q % 8 = 5 := by omega
      rw [Nat.pow_mod]; rcases this with h | h <;> simp [h]
    simp [Nat.pow_mod, this]
  rw [hN, Nat.mul_mod, hm8, mul_one, pow_succ, pow_mul, Nat.mod_mod, Nat.mul_mod, hq8, one_mul,
    Nat.mod_mod]

/-- `σ(q ^ (2 j + 1)) = (q + 1) * ∑_{i ≤ j} q ^ (2 i)`. -/
private lemma sigma_odd_pow {q : ℕ} (hq : q.Prime) (j : ℕ) :
    σ 1 (q ^ (2 * j + 1)) = (q + 1) * ∑ i ∈ Finset.range (j + 1), (q ^ 2) ^ i := by
  induction j with
  | zero => rw [sigma_one_apply_prime_pow hq]; simp [Finset.sum_range_succ, add_comm]
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring, sigma_succ_add hq, sigma_succ_add hq,
      ih, Finset.sum_range_succ _ (j + 1)]
    ring

/-- For odd `q`, `∑_{i ≤ j} q ^ (2 i) ≡ j + 1 (mod 4)`. -/
private lemma sum_sq_pow_mod {q : ℕ} (hq : q % 2 = 1) (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), (q ^ 2) ^ i) % 4 = (j + 1) % 4 := by
  have h1 : q ^ 2 % 4 = 1 := by
    have : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rw [Nat.pow_mod]; rcases this with h | h <;> simp [h]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have : (q ^ 2) ^ (j + 1) % 4 = 1 := by simp [Nat.pow_mod, h1]
    omega

/-- Chen and Luo; Dris and San Diego: `σ(m ^ 2) ≡ 1 (mod 4)` iff `q ≡ k (mod 8)`. Equivalent to
congruence (2) of Ewell, J. Number Theory 12 (1980), 339 to 342 (p. 340): with `q = 4 π + 1`,
`k = 4 ε + 1` and ordinary components `p_i ^ (2 e_i)`, `p_i = 2 π_i - 1`, he proves
`π + ε + ∑ π_i e_i ≡ 0 (mod 2)`. The two are equivalent because
`σ(m ^ 2) ≡ 1 + 2 ∑ π_i e_i (mod 4)`; this last congruence is not stated in his paper. -/
theorem sigma_sq_mod_four_eq_one_iff (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : σ 1 (m ^ 2) % 4 = 1 ↔ q % 8 = k % 8 := by
  obtain ⟨-, ⟨j, rfl⟩, hq4, hk4, -, hprod⟩ := setup h hq hN hqm
  have hN4 := mod_four h
  have ho := odd_sigma_sq h hq hN hqm
  obtain ⟨a, ha⟩ : ∃ a, q + 1 = 2 * a := ⟨(q + 1) / 2, by omega⟩
  have hT := sum_sq_pow_mod (q := q) (by omega) j
  rw [sigma_odd_pow hq, ha] at hprod
  set T := ∑ i ∈ Finset.range (j + 1), (q ^ 2) ^ i
  have hprod' : a * T * σ 1 (m ^ 2) = N :=
    Nat.eq_of_mul_eq_mul_left two_pos (by rw [← hprod]; ring)
  have hmod : (a * T * σ 1 (m ^ 2)) % 4 = 1 := by rw [hprod', hN4]
  rw [Nat.mul_mod, Nat.mul_mod a] at hmod
  have hs : σ 1 (m ^ 2) % 4 = 1 ∨ σ 1 (m ^ 2) % 4 = 3 := by
    obtain ⟨c, hc⟩ := ho; omega
  have hq8 : q % 8 = 1 ∨ q % 8 = 5 := by omega
  have hk8 : (2 * j + 1) % 8 = 1 ∨ (2 * j + 1) % 8 = 5 := by omega
  have hA : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hB : T % 4 = 1 ∨ T % 4 = 3 := by omega
  rcases hq8 with hq8 | hq8 <;> rcases hk8 with hk8 | hk8 <;> rcases hs with hs | hs <;>
    rcases hA with hA | hA <;> rcases hB with hB | hB <;>
    first
    | (exfalso; omega)
    | (simp [hs, hq8, hk8]; done)
    | (rw [hA, hB, hs] at hmod; norm_num at hmod)

/-! ## Small consequences -/

/-- Dris: `m ^ 2 - q ^ k ≥ 8`, that is, `q ^ k + 8 ≤ m ^ 2`. -/
theorem special_pow_add_eight_le (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : q ^ k + 8 ≤ m ^ 2 := by
  obtain ⟨-, hk, hq4, -, hmo, -⟩ := setup h hq hN hqm
  have hlt := special_pow_lt_sq h hq hN hqm hk
  have hqk4 : q ^ k % 4 = 1 := by simp [Nat.pow_mod, hq4]
  have hm8 : m ^ 2 % 8 = 1 := by
    have : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
    rw [Nat.pow_mod]; rcases this with h | h | h | h <;> rw [h]
  by_contra hc
  have h4 : m ^ 2 = q ^ k + 4 := by omega
  have hm3 : m ≤ 3 := by nlinarith
  have hm : m = 3 := by
    interval_cases m <;> omega
  subst hm
  have hqk : q ^ k = 5 := by omega
  have hd := pow_dvd_sigma_sq h hq hN hqm
  rw [hqk, show (3 : ℕ) ^ 2 = 3 ^ 2 from rfl, sigma_one_apply_prime_pow Nat.prime_three] at hd
  simp [Finset.sum_range_succ] at hd

/-- If `m < q` then `k = 1`. -/
theorem exponent_eq_one_of_lt (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hlt : m < q) : k = 1 := by
  obtain ⟨-, hk, hq4, hk4, -, -⟩ := setup h hq hN hqm
  have h1 := special_pow_lt_sq h hq hN hqm hk
  have h2 : m ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hlt two_ne_zero
  have h3 : q ^ k < q ^ 2 := by omega
  have := (Nat.pow_lt_pow_iff_right hq.one_lt).mp h3
  omega

/-- No two distinct primes divide an odd perfect number exactly once. -/
theorem not_two_primes_exact_once (h : OddPerfect N) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hp1 : N.factorization p = 1) (hr1 : N.factorization r = 1) : False :=
  hpr ((existsUnique_odd_exponent h).unique ⟨hp, by rw [hp1]; exact odd_one⟩
    ⟨hr, by rw [hr1]; exact odd_one⟩)

/-! ## Dris and Luca -/

/-- For an odd prime `l` and any prime `p`, `v_l(σ(p ^ (l - 1))) ≤ 1`. -/
theorem padicValNat_sigma_pow_pred_le {l p : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hp : p.Prime) :
    padicValNat l (σ 1 (p ^ (l - 1))) ≤ 1 := by
  have : Fact l.Prime := ⟨hl⟩
  by_cases hpl : p = l
  · subst hpl; rw [padicValNat_sigma_prime_pow_self hp]; omega
  by_cases h1 : l ∣ p - 1
  · rw [padicValNat_sigma_prime_pow_of_dvd_pred hp hl hl2 h1,
      Nat.sub_add_cancel hl.one_lt.le, padicValNat_self]
  · rw [padicValNat_sigma_prime_pow_of_not_orderOf_dvd hp hl]
    · omega
    rw [Nat.sub_add_cancel hl.one_lt.le]
    intro hd
    have hp0 : (p : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => hpl ((Nat.prime_dvd_prime_iff_eq hl hp).mp h).symm
    have hd' := ZMod.orderOf_dvd_card_sub_one hp0
    have h11 : orderOf (p : ZMod l) ∣ 1 := by
      have := Nat.dvd_sub hd hd'
      rwa [Nat.sub_sub_self hl.one_lt.le] at this
    have hc : (p : ZMod l) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h11)
    apply h1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hp.one_lt.le, hc, Nat.cast_one, sub_self]

/-- For an odd prime `l` and any prime `p`, `l ^ 2 ∤ σ(p ^ (l - 1))`. -/
theorem not_sq_dvd_sigma_pow_pred {l p : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hp : p.Prime) :
    ¬ l ^ 2 ∣ σ 1 (p ^ (l - 1)) := by
  have : Fact l.Prime := ⟨hl⟩
  intro hd
  have := (padicValNat_dvd_iff_le (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne').mp hd
  have := padicValNat_sigma_pow_pred_le hl hl2 hp
  omega

/-- Dris and Luca: `25 ∤ σ(p ^ 4)` for every prime `p`. -/
theorem not_twentyfive_dvd_sigma_pow_four {p : ℕ} (hp : p.Prime) : ¬ 25 ∣ σ 1 (p ^ 4) :=
  not_sq_dvd_sigma_pow_pred (l := 5) Nat.prime_five (by norm_num) hp

/-- Dris and Luca, Lemma 2: for an odd prime `p` and a prime `q`, if
`σ(p ^ λ) = q ^ β` and `p ^ λ ∣ σ(q ^ α)`, then `p ^ (λ - 1) ∣ α + 1`. (False for `p = 2`:
`σ(2 ^ 4) = 31` and `2 ^ 4 ∣ σ(31 ^ 1) = 32`, but `2 ^ 3 ∤ 2`.) -/
theorem pow_pred_dvd_succ_of_sigma_eq_pow {p q l b a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hσ : σ 1 (p ^ l) = q ^ b) (hd : p ^ l ∣ σ 1 (q ^ a)) :
    p ^ (l - 1) ∣ a + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases l with _ | l'
  · simp
  rw [Nat.add_sub_cancel]
  set s := σ 1 (p ^ l')
  have hs0 : s ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'
  have hσ1 : q ^ b = 1 + p * s := by rw [← hσ, sigma_succ_mul hp]
  have hb : b ≠ 0 := by
    rintro rfl
    have := hp.pos
    simp at hσ1
    rcases Nat.mul_eq_zero.mp (by omega : p * s = 0) with h | h <;> omega
  have hqp : q ≠ p := by
    rintro rfl
    have h1 : q ∣ σ 1 (q ^ (l' + 1)) := hσ ▸ dvd_pow_self q hb
    have := coprime_sigma_prime_pow hq (l' + 1)
    exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm this) h1)
  have hσa0 : σ 1 (q ^ a) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  have hle : l' + 1 ≤ padicValNat p (σ 1 (q ^ a)) := (padicValNat_dvd_iff_le hσa0).mp hd
  have hpd : p ∣ σ 1 (q ^ a) := (dvd_pow_self p (Nat.succ_ne_zero l')).trans hd
  have ha0 : a + 1 ≠ 0 := Nat.succ_ne_zero a
  apply (padicValNat_dvd_iff_le ha0).mpr
  by_cases h1 : orderOf (q : ZMod p) = 1
  · have hc : (q : ZMod p) = 1 := orderOf_eq_one_iff.mp h1
    have hdp : p ∣ q - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq.one_lt.le, hc, Nat.cast_one, sub_self]
    rw [padicValNat_sigma_prime_pow_of_dvd_pred hq hp hp2 hdp] at hle
    omega
  · have hdiv := (dvd_sigma_prime_pow_iff hq hp hqp).mp hpd
    rw [if_neg h1] at hdiv
    have hdb : orderOf (q : ZMod p) ∣ b := by
      apply orderOf_dvd_of_pow_eq_one
      have : ((q ^ b : ℕ) : ZMod p) = 1 := by
        rw [hσ1]; push_cast; rw [ZMod.natCast_self, zero_mul, add_zero]
      exact_mod_cast this
    have hd0 : orderOf (q : ZMod p) ≠ 0 := fun h0 => hb (Nat.eq_zero_of_zero_dvd (h0 ▸ hdb))
    rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hq hp hp2 hqp (by omega) hdiv] at hle
    set d := orderOf (q : ZMod p)
    -- `v_p(q ^ d - 1) ≤ v_p(q ^ b - 1) = 1`
    have hqb1 : q ^ b - 1 = p * s := by omega
    have hvb : padicValNat p (q ^ b - 1) = 1 := by
      rw [hqb1, padicValNat.mul hp.ne_zero hs0, padicValNat_self,
        padicValNat_sigma_prime_pow_self hp]
    have hqd : 1 < q ^ d := Nat.one_lt_pow hd0 hq.one_lt
    have hdvd : q ^ d - 1 ∣ q ^ b - 1 := by
      obtain ⟨c, hc⟩ := hdb
      rw [hc, pow_mul]
      exact Nat.sub_one_dvd_pow_sub_one _ _
    have hv1 : padicValNat p (q ^ d - 1) ≤ 1 := by
      have := (padicValNat_dvd_iff_le (by rw [hqb1]; exact mul_ne_zero hp.ne_zero hs0)).mp
        ((pow_padicValNat_dvd (p := p) (n := q ^ d - 1)).trans hdvd)
      omega
    have hv2 : padicValNat p ((a + 1) / d) ≤ padicValNat p (a + 1) := by
      apply (padicValNat_dvd_iff_le ha0).mp
      exact (pow_padicValNat_dvd (p := p) (n := (a + 1) / d)).trans (Nat.div_dvd_of_dvd hdiv)
    omega

end OddPerfect

#print axioms OddPerfect.sigma_sq_eq_mul_eulerIndex
#print axioms OddPerfect.sigma_special_mul_eulerIndex
#print axioms OddPerfect.odd_eulerIndex
#print axioms OddPerfect.three_le_eulerIndex
#print axioms OddPerfect.eulerIndex_dvd_sq
#print axioms OddPerfect.eulerIndex_eq_gcd
#print axioms OddPerfect.sigma_special_div_two
#print axioms OddPerfect.special_pow_eq_div_gcd
#print axioms OddPerfect.eq_of_euler_form_sq_eq
#print axioms OddPerfect.sigma_sq_lt
#print axioms OddPerfect.deficiency_sq_eq
#print axioms OddPerfect.deficiency_sq_dvd_iff
#print axioms OddPerfect.sigma_sq_div_dvd_iff
#print axioms OddPerfect.mod_eight_eq_special
#print axioms OddPerfect.sigma_sq_mod_four_eq_one_iff
#print axioms OddPerfect.special_pow_add_eight_le
#print axioms OddPerfect.exponent_eq_one_of_lt
#print axioms OddPerfect.not_two_primes_exact_once
#print axioms OddPerfect.padicValNat_sigma_pow_pred_le
#print axioms OddPerfect.not_sq_dvd_sigma_pow_pred
#print axioms OddPerfect.not_twentyfive_dvd_sigma_pow_four
#print axioms OddPerfect.pow_pred_dvd_succ_of_sigma_eq_pow
