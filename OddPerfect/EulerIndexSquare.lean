import OddPerfect.EulerPart
import OddPerfect.SquareRow
import OddPerfect.SpecialPrime

/-!
# The index of an odd perfect number is not a square

Let `N = q ^ k * m ^ 2` be an odd perfect number in Euler's form, with `q` the special prime
and `q ∤ m`, and let `d = σ(m ^ 2) / q ^ k` be its index (`eulerIndex`). Then `k ≡ 1 (mod 4)`;
put `ℓ = (k + 1) / 2`, `R = σ(q ^ (ℓ - 1))` and `S = (q ^ ℓ + 1) / 2`. Then
`σ(q ^ k) = 2 R S` with `R` and `S` odd and coprime, so `m ^ 2 = d R S`.

* If `d = d₁ ^ 2 * d₂` with `d₂ ∣ S`, then `R` is a square, and the square rows theorem
  (`isSquare_sigma_prime_pow_iff`) forces `k = 1`.
* Hence for `k ≠ 1` the index is not a square.
* If `d = d₁ ^ 2 * d₂` with `d₂` coprime to `S`, then `S` is a square and `q ≡ 1 (mod 8)`.
* So for `k ≠ 1` either `d₂` shares a prime factor with `S` without dividing it, or
  `q ≡ 1 (mod 8)`.

This is known mathematics: L. H. Gallardo, Integers 22 (2022), A58, Propositions 2, 3 and the
first claim of Proposition 4; Proposition 2 is also due to Broughan, Delbourgo and Zhou (see
Remark 2 of that paper). These results give no bound on the index. The odd perfect number
conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexSquare

/-- If coprime `a` and `b` have a square product, then `a` is a square. -/
private lemma isSquare_of_coprime_mul_eq_sq {a b c : ℕ} (hab : Nat.Coprime a b)
    (h : a * b = c ^ 2) : IsSquare a := by
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hab) h
  exact ⟨d, by rw [hd, sq]⟩

/-- `σ(q ^ (2 i + 1)) = σ(q ^ i) * (q ^ (i + 1) + 1)`. -/
private lemma sigma_odd_pow_eq {q : ℕ} (hq : q.Prime) (i : ℕ) :
    σ 1 (q ^ (i + i + 1)) = σ 1 (q ^ i) * (q ^ (i + 1) + 1) := by
  rw [sigma_one_apply_prime_pow hq, sigma_one_apply_prime_pow hq,
    show i + i + 1 + 1 = (i + 1) + (i + 1) by ring, Finset.sum_range_add]
  have : ∑ x ∈ Finset.range (i + 1), q ^ (i + 1 + x) =
      q ^ (i + 1) * ∑ x ∈ Finset.range (i + 1), q ^ x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => pow_add q (i + 1) x
  rw [this]; ring

/-- `σ(q ^ i) + q ^ (i + 1) = 1 + q σ(q ^ i)`. -/
private lemma sigma_shift {q : ℕ} (hq : q.Prime) (i : ℕ) :
    σ 1 (q ^ i) + q ^ (i + 1) = 1 + q * σ 1 (q ^ i) := by
  rw [sigma_one_apply_prime_pow hq, ← Finset.sum_range_succ, Finset.sum_range_succ',
    Finset.mul_sum]
  simp only [pow_succ', pow_zero]
  ring

/-- The common setup: `k = 4 j + 1`, `q ≡ 1 (mod 4)`, `q ^ (2 j + 1) + 1 = 2 S`,
`m ^ 2 = d R S` with `R = σ(q ^ (2 j))` coprime to the odd number `S`. -/
private lemma core {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    ∃ j : ℕ, k = 4 * j + 1 ∧ q % 4 = 1 ∧ m ≠ 0 ∧
      q ^ (2 * j + 1) + 1 = 2 * ((q ^ (2 * j + 1) + 1) / 2) ∧
      m ^ 2 = eulerIndex q k m * (σ 1 (q ^ (2 * j)) * ((q ^ (2 * j + 1) + 1) / 2)) ∧
      Nat.Coprime (σ 1 (q ^ (2 * j))) ((q ^ (2 * j + 1) + 1) / 2) ∧
      Odd ((q ^ (2 * j + 1) + 1) / 2) := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
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
  obtain ⟨hq4, hk4⟩ := h4
  obtain ⟨j, rfl⟩ : ∃ j, k = 4 * j + 1 := ⟨k / 4, by omega⟩
  have hmo : Odd m := h.odd.of_dvd_nat (hN ▸ (dvd_pow_self m two_ne_zero).mul_left _)
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have h2S : q ^ (2 * j + 1) + 1 = 2 * ((q ^ (2 * j + 1) + 1) / 2) := by
    obtain ⟨t, ht⟩ := hqo.pow (n := 2 * j + 1)
    generalize q ^ (2 * j + 1) = A at *
    omega
  have hsig : σ 1 (q ^ (4 * j + 1)) =
      σ 1 (q ^ (2 * j)) * (2 * ((q ^ (2 * j + 1) + 1) / 2)) := by
    rw [show 4 * j + 1 = 2 * j + 2 * j + 1 by ring, sigma_odd_pow_eq hq, ← h2S]
  have hprod := sigma_special_mul_eulerIndex h hq hN hqm
  rw [hsig] at hprod
  have hmS : m ^ 2 = eulerIndex q (4 * j + 1) m *
      (σ 1 (q ^ (2 * j)) * ((q ^ (2 * j + 1) + 1) / 2)) := by
    apply Nat.eq_of_mul_eq_mul_left two_pos
    rw [← hprod]; ring
  have hSodd : Odd ((q ^ (2 * j + 1) + 1) / 2) :=
    (hmo.pow (n := 2)).of_dvd_nat ⟨eulerIndex q (4 * j + 1) m * σ 1 (q ^ (2 * j)), by
      rw [hmS]; ring⟩
  have hsh := sigma_shift hq (2 * j)
  have hg2 : Nat.gcd (σ 1 (q ^ (2 * j))) ((q ^ (2 * j + 1) + 1) / 2) ∣ 2 := by
    have h1 : Nat.gcd (σ 1 (q ^ (2 * j))) ((q ^ (2 * j + 1) + 1) / 2) ∣
        q * σ 1 (q ^ (2 * j)) + 2 := by
      have : q * σ 1 (q ^ (2 * j)) + 2 =
          2 * ((q ^ (2 * j + 1) + 1) / 2) + σ 1 (q ^ (2 * j)) := by linarith
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 2) (Nat.gcd_dvd_left _ _)
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) q)).mp h1
  have hgo : Odd (Nat.gcd (σ 1 (q ^ (2 * j))) ((q ^ (2 * j + 1) + 1) / 2)) :=
    hSodd.of_dvd_nat (Nat.gcd_dvd_right _ _)
  have hcop : Nat.Coprime (σ 1 (q ^ (2 * j))) ((q ^ (2 * j + 1) + 1) / 2) := by
    have := Nat.le_of_dvd two_pos hg2
    obtain ⟨t, ht⟩ := hgo
    show Nat.gcd _ _ = 1
    omega
  exact ⟨j, rfl, hq4, hm, h2S, hmS, hcop, hSodd⟩

end EulerIndexSquare

open EulerIndexSquare

variable {N q k m d₁ d₂ : ℕ}

/-- **Gallardo, Proposition 3.** For an odd perfect
number `q ^ k * m ^ 2` with special prime `q`, if the index is `d₁ ^ 2 * d₂` with
`d₂ ∣ (q ^ ℓ + 1) / 2`, where `ℓ = (k + 1) / 2`, then `k = 1`. -/
theorem exponent_eq_one_of_eulerIndex_eq_sq_mul (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m)
    (hd : eulerIndex q k m = d₁ ^ 2 * d₂) (hS : d₂ ∣ (q ^ ((k + 1) / 2) + 1) / 2) : k = 1 := by
  obtain ⟨j, rfl, hq4, hm, -, hmS, hcop, -⟩ := core h hq hN hqm
  rw [show (4 * j + 1 + 1) / 2 = 2 * j + 1 by omega] at hS
  obtain ⟨T, hT⟩ := hS
  have hTS : T ∣ (q ^ (2 * j + 1) + 1) / 2 := Dvd.intro_left d₂ hT.symm
  rw [hd, hT] at hmS
  have he : m ^ 2 = (d₁ * d₂) ^ 2 * (σ 1 (q ^ (2 * j)) * T) := by rw [hmS]; ring
  obtain ⟨u, rfl⟩ : d₁ * d₂ ∣ m := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨_, he⟩
  have hne : (d₁ * d₂) ^ 2 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at he
    exact hm ((pow_eq_zero_iff two_ne_zero).mp he)
  have hu : u ^ 2 = σ 1 (q ^ (2 * j)) * T := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
    rw [← he]; ring
  have hRsq := isSquare_of_coprime_mul_eq_sq (Nat.Coprime.coprime_dvd_right hTS hcop) hu.symm
  by_contra hk1
  have := (isSquare_sigma_prime_pow_iff hq (by omega) (even_two_mul j) (by omega)).mp hRsq
  omega

/-- **Gallardo, Proposition 2** (also Broughan, Delbourgo and Zhou). For an odd perfect number
`q ^ k * m ^ 2` with special prime `q` and `k ≠ 1`, the index `σ(m ^ 2) / q ^ k` is not a square. -/
theorem not_isSquare_eulerIndex (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k ≠ 1) : ¬ IsSquare (eulerIndex q k m) := by
  rintro ⟨r, hr⟩
  exact hk (exponent_eq_one_of_eulerIndex_eq_sq_mul (d₁ := r) (d₂ := 1) h hq hN hqm
    (by rw [hr, sq, mul_one]) (one_dvd _))

/-- **Gallardo, Proposition 4, first claim.** For an odd perfect number `q ^ k * m ^ 2` with
special prime `q`, if the index is `d₁ ^ 2 * d₂` with `d₂` coprime to `(q ^ ℓ + 1) / 2`, where
`ℓ = (k + 1) / 2`, then `(q ^ ℓ + 1) / 2` is a square and `q ≡ 1 (mod 8)`. No hypothesis on
`k` is needed. -/
theorem special_mod_eight_of_eulerIndex_coprime (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m)
    (hd : eulerIndex q k m = d₁ ^ 2 * d₂)
    (hS : Nat.Coprime d₂ ((q ^ ((k + 1) / 2) + 1) / 2)) :
    IsSquare ((q ^ ((k + 1) / 2) + 1) / 2) ∧ q % 8 = 1 := by
  obtain ⟨j, rfl, hq4, hm, h2S, hmS, hcop, hSodd⟩ := core h hq hN hqm
  rw [show (4 * j + 1 + 1) / 2 = 2 * j + 1 by omega] at hS ⊢
  rw [hd] at hmS
  have he : m ^ 2 = d₁ ^ 2 *
      ((q ^ (2 * j + 1) + 1) / 2 * (d₂ * σ 1 (q ^ (2 * j)))) := by rw [hmS]; ring
  obtain ⟨u, rfl⟩ : d₁ ∣ m := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨_, he⟩
  have hne : d₁ ^ 2 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at he
    exact hm ((pow_eq_zero_iff two_ne_zero).mp he)
  have hu : u ^ 2 = (q ^ (2 * j + 1) + 1) / 2 * (d₂ * σ 1 (q ^ (2 * j))) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
    rw [← he]; ring
  have hc : Nat.Coprime ((q ^ (2 * j + 1) + 1) / 2) (d₂ * σ 1 (q ^ (2 * j))) :=
    Nat.Coprime.mul_right hS.symm hcop.symm
  obtain ⟨t, ht⟩ := isSquare_of_coprime_mul_eq_sq hc hu.symm
  refine ⟨⟨t, ht⟩, ?_⟩
  have hto : t % 2 = 1 := by
    rw [ht] at hSodd
    exact Nat.odd_iff.mp (Nat.odd_mul.mp hSodd).1
  have ht8 : t * t % 8 = 1 := by
    have : t % 8 = 1 ∨ t % 8 = 3 ∨ t % 8 = 5 ∨ t % 8 = 7 := by omega
    rcases this with h8 | h8 | h8 | h8 <;> simp [Nat.mul_mod, h8]
  have hq2 : q ^ 2 % 8 = 1 := by
    have : q % 8 = 1 ∨ q % 8 = 5 := by omega
    rw [Nat.pow_mod]
    rcases this with h8 | h8 <;> simp [h8]
  have hpow : q ^ (2 * j + 1) % 8 = q % 8 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, hq2]
    simp
  rw [ht] at h2S
  generalize q ^ (2 * j + 1) = A at *
  generalize t * t = s at *
  omega

/-- **Dichotomy.** For an odd perfect number `q ^ k * m ^ 2` with special prime `q` and
`k ≠ 1`, write the index as `d₁ ^ 2 * d₂` and put `S = (q ^ ℓ + 1) / 2` with
`ℓ = (k + 1) / 2`. Then either `d₂` does not divide `S` but shares a prime factor with it,
or `q ≡ 1 (mod 8)`. -/
theorem exists_prime_dvd_or_mod_eight_of_eulerIndex (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k ≠ 1)
    (hd : eulerIndex q k m = d₁ ^ 2 * d₂) :
    (¬ d₂ ∣ (q ^ ((k + 1) / 2) + 1) / 2 ∧
      ∃ p, p.Prime ∧ p ∣ d₂ ∧ p ∣ (q ^ ((k + 1) / 2) + 1) / 2) ∨ q % 8 = 1 := by
  by_cases hc : Nat.Coprime d₂ ((q ^ ((k + 1) / 2) + 1) / 2)
  · exact Or.inr (special_mod_eight_of_eulerIndex_coprime h hq hN hqm hd hc).2
  · exact Or.inl ⟨fun hS => hk (exponent_eq_one_of_eulerIndex_eq_sq_mul h hq hN hqm hd hS),
      Nat.Prime.not_coprime_iff_dvd.mp hc⟩

end OddPerfect

#print axioms OddPerfect.exponent_eq_one_of_eulerIndex_eq_sq_mul
#print axioms OddPerfect.not_isSquare_eulerIndex
#print axioms OddPerfect.special_mod_eight_of_eulerIndex_coprime
#print axioms OddPerfect.exists_prime_dvd_or_mod_eight_of_eulerIndex
