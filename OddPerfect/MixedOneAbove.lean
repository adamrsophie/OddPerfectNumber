import OddPerfect.MixedLargestPrime
import OddPerfect.RankTwoPaletteFree

/-!
# One prime above the special prime in the palette of exponents 2 and 4 without 3 and 5

Restricted family results; the family is not excluded, and whether the results are in the
literature was not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`, let
every other prime factor have exponent `2` or `4`, let `3 ∤ N` and `5 ∤ N`, and let exactly one
prime factor `P` exceed `q`. The landed
`special_exponent_eq_one_or_thirteen_of_not_three_five_dvd` gives `a = 1`, or `a = 13` with
`q ≡ 1 (mod 60)`. Here `a = 13` is excluded
(`mixed_special_exponent_ne_thirteen_of_not_three_five_dvd`), and then `v_P(N) = 2`,
`P ≡ 11 (mod 15)` and `P < q ^ 2` (`mixed_one_above`). The case `q < P < q ^ 2` remains. By the
Main Theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81 (2012)) the least prime factor
exceeds `10 ^ 8` when every prime factor other than the special prime has exponent `2` or `4`,
so `3 ∤ N` and `5 ∤ N` hold in this family; that theorem is not formalized here, and the two
conditions are explicit hypotheses.

Proof outline for `a = 13`. Write `σ(q ^ 13) = A (q ^ 7 + 1)` with `A = 1 + q + ... + q ^ 6`;
a common prime factor of `A` and `q ^ 7 + 1` divides `2`, so a power of `P` dividing `σ(q ^ 13)`
divides `T = q ^ 7 - 1` or `T = q ^ 7 + 1`. The rows below `q` carry at most `7` at `q`, so
`q ^ 6 ∣ σ(P ^ d)` with `d = v_P(N)`.

* `d = 4`: `P ^ 3 ∣ σ(q ^ 13)` (`mixed_largest_cube_dvd_sigma_special`), so `T = P ^ 3 X` with
  `X ≤ q ^ 4` and `P ^ 2 < q ^ 5`. As `P ^ 5 ≡ 1 (mod q ^ 6)`, `X ≡ ∓ P ^ 2 (mod q ^ 6)`: either
  `q ^ 6 ∣ X + P ^ 2`, too small, or `X = P ^ 2`, against parity.
* `d = 2`: `q ^ 3 ≤ P`. Square rows do not reach `P`, a row `σ(p ^ 4)` with `p < q` is below
  `P ^ 2`, and two such rows cannot both reach `P` (their residues are fifth roots of unity, so
  one is a power of the other, and every case is too small to be a congruence). So `P ∣ T`,
  `P < q ^ 4`, `T = P X` with `X ≤ q ^ 4` and `X ≡ ± (P + 1) (mod q ^ 6)`; this leaves only
  `q ^ 7 - 1 = P (P + 1)`, against `P ^ 2 ∣ T` or against `P ≡ 1 (mod 5)`.

For `a = 1` and `q ^ 2 ≤ P`, the same receipt count gives `v_P(σ(N)) ≤ 1 < 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem moa_geom_mul_add (q c : ℕ) :
    (∑ i ∈ Finset.range c, q ^ i) * q + 1 = (∑ i ∈ Finset.range c, q ^ i) + q ^ c := by
  induction c with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ, add_mul]
    omega

private theorem moa_geom_double (q c : ℕ) :
    ∑ i ∈ Finset.range (2 * c), q ^ i =
      (∑ i ∈ Finset.range c, q ^ i) * (q ^ c + 1) := by
  rw [two_mul, Finset.sum_range_add]
  have h : ∑ x ∈ Finset.range c, q ^ (c + x) = q ^ c * ∑ x ∈ Finset.range c, q ^ x := by
    rw [Finset.mul_sum]
    simp only [pow_add]
  rw [h]
  ring

/-- A power of an odd prime dividing `σ(q ^ 13)` divides `q ^ 7 - 1` or `q ^ 7 + 1`. -/
private theorem moa_split {q P r : ℕ} (hq : 1 ≤ q) (hP : P.Prime) (hP2 : P ≠ 2)
    (hd : P ^ r ∣ ∑ i ∈ Finset.range 14, q ^ i) :
    ∃ T, P ^ r ∣ T ∧ (T + 1 = q ^ 7 ∨ T = q ^ 7 + 1) := by
  have hgm := moa_geom_mul_add q 7
  rw [show (14 : ℕ) = 2 * 7 by norm_num, moa_geom_double] at hd
  generalize ∑ i ∈ Finset.range 7, q ^ i = A at hgm hd
  have hPd : ¬ (P ∣ A ∧ P ∣ q ^ 7 + 1) := by
    rintro ⟨h1, h2⟩
    have h3 : P ∣ A + (q ^ 7 + 1) := dvd_add h1 h2
    rw [show A + (q ^ 7 + 1) = A * q + 2 by omega] at h3
    have h4 : P ∣ 2 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h1 q)).mp h3
    exact hP2 ((Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).mp h4)
  by_cases hPA : P ∣ A
  · have hcop : Nat.Coprime (P ^ r) (q ^ 7 + 1) :=
      Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd hP).mpr fun h2 => hPd ⟨hPA, h2⟩)
    refine ⟨A * (q - 1), (hcop.dvd_of_dvd_mul_right hd).mul_right _, Or.inl ?_⟩
    have h1 : A * (q - 1) = A * q - A := Nat.mul_sub_one A q
    have h2 : A ≤ A * q := Nat.le_mul_of_pos_right A hq
    omega
  · have hcop : Nat.Coprime (P ^ r) A :=
      Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd hP).mpr hPA)
    exact ⟨q ^ 7 + 1, hcop.dvd_of_dvd_mul_left hd, Or.inr rfl⟩

private theorem moa_pow_seven_zero (q : ℕ) : (q : ZMod (q ^ 6)) ^ 7 = 0 := by
  have := (ZMod.natCast_eq_zero_iff (q ^ 7) (q ^ 6)).mpr (pow_dvd_pow q (by norm_num))
  exact_mod_cast this

/-- The case `v_P(N) = 4` at `a = 13`: `q ^ 6 ∣ σ(P ^ 4)` and `P ^ 3 ∣ q ^ 7 ∓ 1` are
incompatible for odd `q < P`. -/
private theorem moa_core_four {q P T : ℕ} (hq : 3 ≤ q) (hqo : q % 2 = 1) (hPo : P % 2 = 1)
    (hqP : q < P) (hσ : q ^ 6 ∣ ∑ i ∈ Finset.range 5, P ^ i) (hT : P ^ 3 ∣ T)
    (hTq : T + 1 = q ^ 7 ∨ T = q ^ 7 + 1) : False := by
  obtain ⟨X, rfl⟩ := hT
  have hq3 : q ^ 3 < P ^ 3 := Nat.pow_lt_pow_left hqP (by norm_num)
  have h27 : 27 ≤ q ^ 3 := by
    have := Nat.pow_le_pow_left hq 3
    simpa using this
  have hTle : P ^ 3 * X ≤ q ^ 7 + 1 := by rcases hTq with e | e <;> omega
  have hX : X ≤ q ^ 4 := by
    by_contra hc
    have h1 : q ^ 3 * (q ^ 4 + 1) ≤ P ^ 3 * X := Nat.mul_le_mul hq3.le (by omega)
    have h2 : q ^ 3 * (q ^ 4 + 1) = q ^ 7 + q ^ 3 := by ring
    omega
  have hX0 : 0 < X := by
    rcases Nat.eq_zero_or_pos X with h0 | h0
    · subst h0
      have : 1 < q ^ 7 := Nat.one_lt_pow (by norm_num) (by omega)
      rcases hTq with e | e <;> omega
    · exact h0
  have hP3le : P ^ 3 ≤ q ^ 7 + 1 := le_trans (Nat.le_mul_of_pos_right _ hX0) hTle
  have hP2 : P ^ 2 < q ^ 5 := by
    have h1 : (P ^ 2) ^ 3 = (P ^ 3) ^ 2 := by ring
    have h2 : (P ^ 3) ^ 2 ≤ (q ^ 7 + 1) ^ 2 := Nat.pow_le_pow_left hP3le 2
    have h3 : (q ^ 7 + 1) ^ 2 < (q ^ 5) ^ 3 := by
      have e1 : (q ^ 5) ^ 3 = q ^ 7 * q ^ 7 * q := by ring
      have e2 : (q ^ 7 + 1) ^ 2 = q ^ 7 * q ^ 7 + 2 * q ^ 7 + 1 := by ring
      have e3 : q ^ 7 * q ^ 7 * 3 ≤ q ^ 7 * q ^ 7 * q := Nat.mul_le_mul_left _ hq
      have e4 : q ^ 7 ≤ q ^ 7 * q ^ 7 := Nat.le_mul_of_pos_right _ (by positivity)
      have e5 : 3 ≤ q ^ 7 := le_trans hq (Nat.le_self_pow (by norm_num) q)
      have e6 : q ^ 7 * 3 ≤ q ^ 7 * q ^ 7 := Nat.mul_le_mul_left _ e5
      omega
    exact (Nat.pow_lt_pow_iff_left (by norm_num : 3 ≠ 0)).mp (by omega)
  have hq54 : q ^ 4 * 3 ≤ q ^ 5 := by
    rw [pow_succ]
    exact Nat.mul_le_mul_left _ hq
  have hq65 : q ^ 5 * 3 ≤ q ^ 6 := by
    rw [pow_succ q 5]
    exact Nat.mul_le_mul_left _ hq
  have h7 := moa_pow_seven_zero q
  have h5 : (P : ZMod (q ^ 6)) ^ 5 = 1 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr hσ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    push_cast at h
    linear_combination ((P : ZMod (q ^ 6)) - 1) * h
  rcases hTq with h1 | h1
  · have hc := congrArg (Nat.cast : ℕ → ZMod (q ^ 6)) h1
    push_cast at hc
    have hz : ((X + P ^ 2 : ℕ) : ZMod (q ^ 6)) = 0 := by
      push_cast
      linear_combination (P : ZMod (q ^ 6)) ^ 2 * hc - (X : ZMod (q ^ 6)) * h5 +
        (P : ZMod (q ^ 6)) ^ 2 * h7
    have hle := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    omega
  · have hc := congrArg (Nat.cast : ℕ → ZMod (q ^ 6)) h1
    push_cast at hc
    have hz : ((X : ℕ) : ZMod (q ^ 6)) = ((P ^ 2 : ℕ) : ZMod (q ^ 6)) := by
      push_cast
      linear_combination (P : ZMod (q ^ 6)) ^ 2 * hc - (X : ZMod (q ^ 6)) * h5 +
        (P : ZMod (q ^ 6)) ^ 2 * h7
    have hm := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
    subst hm
    have e1 : Odd (P ^ 3 * P ^ 2) :=
      (Nat.odd_iff.mpr hPo).pow.mul (Nat.odd_iff.mpr hPo).pow
    have e2 : Odd (q ^ 7) := (Nat.odd_iff.mpr hqo).pow
    rw [h1] at e1
    rw [Nat.odd_iff] at e1 e2
    omega

/-- From `q ^ 6 ∣ σ(P ^ 2)`: `q ^ 3 ≤ P`. -/
private theorem moa_cube_le {q P : ℕ} (hq : 2 ≤ q) (hσ : q ^ 6 ∣ ∑ i ∈ Finset.range 3, P ^ i) :
    q ^ 3 ≤ P := by
  have hs : ∑ i ∈ Finset.range 3, P ^ i = P ^ 2 + P + 1 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hs] at hσ
  have h1 := Nat.le_of_dvd (by positivity) hσ
  have h64 : 64 ≤ q ^ 6 := by
    have := Nat.pow_le_pow_left hq 6
    simpa using this
  have hP0 : 0 < P := by
    rcases Nat.eq_zero_or_pos P with h0 | h0
    · subst h0
      norm_num at h1
      omega
    · exact h0
  by_contra hc
  have h2 : (P + 1) ^ 2 ≤ (q ^ 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e1 : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have e2 : (P + 1) ^ 2 = P ^ 2 + P + 1 + P := by ring
  omega

/-- The case `v_P(N) = 2` at `a = 13`: if `q ^ 6 ∣ σ(P ^ 2)`, `P < q ^ 4` and `P ∣ q ^ 7 ∓ 1`,
then `q ^ 7 - 1 = P (P + 1)`. -/
private theorem moa_core_two {q P T : ℕ} (hq : 3 ≤ q)
    (hσ : q ^ 6 ∣ ∑ i ∈ Finset.range 3, P ^ i) (hP3 : q ^ 3 ≤ P) (hPlt : P < q ^ 4)
    (hT : P ∣ T) (hTq : T + 1 = q ^ 7 ∨ T = q ^ 7 + 1) :
    T = P * (P + 1) ∧ T + 1 = q ^ 7 := by
  have hs : ∑ i ∈ Finset.range 3, P ^ i = P ^ 2 + P + 1 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hs] at hσ
  have h27 : 27 ≤ q ^ 3 := by
    have := Nat.pow_le_pow_left hq 3
    simpa using this
  obtain ⟨X, rfl⟩ := hT
  have hX : X ≤ q ^ 4 := by
    by_contra hc
    have h1 : q ^ 3 * (q ^ 4 + 1) ≤ P * X := Nat.mul_le_mul hP3 (by omega)
    have h2 : q ^ 3 * (q ^ 4 + 1) = q ^ 7 + q ^ 3 := by ring
    omega
  have hq46 : q ^ 4 * 3 ≤ q ^ 6 := by
    have e : q ^ 6 = q ^ 4 * (q * q) := by ring
    rw [e]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have h7 := moa_pow_seven_zero q
  have h3 : (P : ZMod (q ^ 6)) ^ 2 + P + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hσ
    exact_mod_cast this
  rcases hTq with h1 | h1
  · have hc := congrArg (Nat.cast : ℕ → ZMod (q ^ 6)) h1
    push_cast at hc
    have hz : ((X : ℕ) : ZMod (q ^ 6)) = ((P + 1 : ℕ) : ZMod (q ^ 6)) := by
      push_cast
      linear_combination (X : ZMod (q ^ 6)) * h3 - ((P : ZMod (q ^ 6)) + 1) * hc -
        ((P : ZMod (q ^ 6)) + 1) * h7
    have hm := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
    subst hm
    exact ⟨rfl, h1⟩
  · have hc := congrArg (Nat.cast : ℕ → ZMod (q ^ 6)) h1
    push_cast at hc
    have hz : ((X + P + 1 : ℕ) : ZMod (q ^ 6)) = 0 := by
      push_cast
      linear_combination (X : ZMod (q ^ 6)) * h3 - ((P : ZMod (q ^ 6)) + 1) * hc -
        ((P : ZMod (q ^ 6)) + 1) * h7
    have hle := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    omega

/-- Two quartic senders: distinct primes `u, v` with `u v < P`, `u ^ 2 < P` and `v ^ 2 < P`
cannot both have `σ(u ^ 4)` and `σ(v ^ 4)` divisible by a prime `P ≠ 5`. -/
private theorem moa_two_quartic {P u v : ℕ} (hP : P.Prime) (hP5 : P ≠ 5) (hu : u.Prime)
    (hv : v.Prime) (huv : u ≠ v) (h1 : u * v < P) (h2 : u ^ 2 < P) (h3 : v ^ 2 < P)
    (hdu : P ∣ ∑ i ∈ Finset.range 5, u ^ i) (hdv : P ∣ ∑ i ∈ Finset.range 5, v ^ i) :
    False := by
  have : Fact P.Prime := ⟨hP⟩
  have hu2 := hu.two_le
  have hv2 := hv.two_le
  have huP : u < P := lt_of_le_of_lt (Nat.le_self_pow (by norm_num) u) h2
  have hvP : v < P := lt_of_le_of_lt (Nat.le_self_pow (by norm_num) v) h3
  have ha := (ZMod.natCast_eq_zero_iff _ _).mpr hdu
  have hb := (ZMod.natCast_eq_zero_iff _ _).mpr hdv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at ha hb
  push_cast at ha hb
  have ha1 : (u : ZMod P) ≠ 1 := by
    intro h
    rw [h] at ha
    have h5 : ((5 : ℕ) : ZMod P) = 0 := by
      push_cast
      linear_combination ha
    exact hP5 ((Nat.prime_dvd_prime_iff_eq hP Nat.prime_five).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp h5))
  have h5 : (u : ZMod P) ^ 5 = 1 := by linear_combination ((u : ZMod P) - 1) * ha
  have key : ((v : ZMod P) - u) * ((v : ZMod P) - (u : ZMod P) ^ 2) *
      ((v : ZMod P) - (u : ZMod P) ^ 3) * ((v : ZMod P) - (u : ZMod P) ^ 4) = 0 := by
    linear_combination hb + ((u : ZMod P) ^ 6 - (u : ZMod P) ^ 5 * v - (u : ZMod P) ^ 5 +
      (u : ZMod P) ^ 3 * v ^ 2 + (u : ZMod P) * v ^ 2 + (u : ZMod P) * v + (u : ZMod P) -
      (v : ZMod P) ^ 3 - (v : ZMod P) ^ 2 - v - 1) * ha
  have hcast : ∀ {x y : ℕ}, x < P → y < P → (x : ZMod P) = (y : ZMod P) → x = y := by
    intro x y hx hy hxy
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  have hsq : ∀ {x y : ℕ}, x.Prime → 2 ≤ y → x = y ^ 2 → False := by
    intro x y hx hy hxy
    rcases hx.eq_one_or_self_of_dvd y ⟨y, by rw [hxy]; ring⟩ with h | h
    · omega
    · rw [hxy] at h
      nlinarith
  simp only [mul_eq_zero] at key
  rcases key with ((h | h) | h) | h
  · exact huv (hcast huP hvP (sub_eq_zero.mp h).symm)
  · exact hsq hv hu2 (hcast hvP h2 (by push_cast; exact sub_eq_zero.mp h))
  · refine hsq hu hv2 (hcast huP h3 ?_)
    push_cast
    linear_combination (-((v : ZMod P) + (u : ZMod P) ^ 3)) * h - (u : ZMod P) * h5
  · have := hcast h1 hP.one_lt (by push_cast; linear_combination (u : ZMod P) * h + h5)
    nlinarith

/-- The rows other than the special row carry at most one unit at `P` when `v_P(N) = 2` and
`q ^ 2 ≤ P`; if they carry one, then `P ≡ 1 (mod 5)` and `P < q ^ 4`. -/
private theorem moa_rest_le_one {N q P : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N)
    (hP : P ∈ N.primeFactors) (hPq : P ≠ q) (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hP2 : N.factorization P = 2) (hqP : q ^ 2 ≤ P) :
    ∑ p ∈ N.primeFactors.erase q, sigmaWeight N p P ≤ 1 ∧
      (∑ p ∈ N.primeFactors.erase q, sigmaWeight N p P ≠ 0 → P % 5 = 1 ∧ P < q ^ 4) := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hP5 : P ≠ 5 := fun h' => h5 (h' ▸ Nat.dvd_of_mem_primeFactors hP)
  have hterm : ∀ p ∈ N.primeFactors.erase q, sigmaWeight N p P ≤ 1 ∧
      (sigmaWeight N p P ≠ 0 → p.Prime ∧ p < q ∧ P ∣ ∑ i ∈ Finset.range 5, p ^ i ∧
        P < q ^ 4) := by
    intro p hp
    obtain ⟨hpq, hp'⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hp'
    have hw : sigmaWeight N p P = (σ 1 (p ^ N.factorization p)).factorization P := rfl
    by_cases hpP : p = P
    · rw [hpP, sigmaWeight_self hPp]
      exact ⟨by omega, fun h0 => absurd rfl h0⟩
    have hlt : p < q := lt_of_le_of_ne (hsecond p hp' hpP) hpq
    have hσ0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
    rcases hexp p hp' hpq with hf | hf
    · have hz : sigmaWeight N p P = 0 := by
        rw [hw]
        refine Nat.factorization_eq_zero_of_not_dvd fun hd => ?_
        rw [hf] at hd
        have := mixed_square_row_target_exponent_four h hexp h3 hp' hf hPp hd hPq
        omega
      rw [hz]
      exact ⟨by omega, fun h0 => absurd rfl h0⟩
    · have hq4 : σ 1 (p ^ N.factorization p) < q ^ 4 := by
        have h1 := sigma_prime_pow_lt_succ_pow hpp (k := N.factorization p) (by omega)
        rw [hf] at h1 ⊢
        have h2 : (p + 1) ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left (by omega) 4
        omega
      have hq4P : q ^ 4 ≤ P ^ 2 := by
        have e : q ^ 4 = (q ^ 2) ^ 2 := by ring
        rw [e]
        exact Nat.pow_le_pow_left hqP 2
      refine ⟨?_, fun h0 => ?_⟩
      · by_contra hc
        have hd : P ^ 2 ∣ σ 1 (p ^ N.factorization p) :=
          (hPp.pow_dvd_iff_le_factorization hσ0).mpr (by omega)
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hσ0) hd
        omega
      · have hd : P ∣ σ 1 (p ^ N.factorization p) :=
          Nat.dvd_of_factorization_pos (by rw [← hw]; exact h0)
        have hPle := Nat.le_of_dvd (Nat.pos_of_ne_zero hσ0) hd
        rw [hf, sigma_one_apply_prime_pow hpp] at hd
        exact ⟨hpp, hlt, hd, by omega⟩
  have hcard : ((N.primeFactors.erase q).filter (fun p => sigmaWeight N p P ≠ 0)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    obtain ⟨hxp, hxq, hxd, -⟩ := (hterm x hx1).2 hx2
    obtain ⟨hyp, hyq, hyd, -⟩ := (hterm y hy1).2 hy2
    by_contra hxy
    have e1 : x * y < q ^ 2 := by
      rw [pow_two]
      exact Nat.mul_lt_mul'' hxq hyq
    have e2 : x ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hxq (by norm_num)
    have e3 : y ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hyq (by norm_num)
    exact moa_two_quartic hPp hP5 hxp hyp hxy (by omega) (by omega) (by omega) hxd hyd
  refine ⟨?_, fun hs => ?_⟩
  · rw [← Finset.sum_filter_ne_zero]
    have := Finset.sum_le_card_nsmul
      ((N.primeFactors.erase q).filter (fun p => sigmaWeight N p P ≠ 0))
      (fun p => sigmaWeight N p P) 1
      (fun p hp => (hterm p (Finset.mem_filter.mp hp).1).1)
    simp only [smul_eq_mul, mul_one] at this
    omega
  · obtain ⟨p, hp, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    obtain ⟨-, -, hd, hlt⟩ := (hterm p hp).2 hw
    refine ⟨?_, hlt⟩
    by_contra hc
    have := hPp.two_le
    exact not_dvd_geom_sum_of_not_dvd_sub_one hPp Nat.prime_five hP5 (by omega) p hd

private theorem moa_mod_five {P : ℕ} (h : P % 5 = 1) : (P * (P + 1) + 1) % 5 = 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, P = 5 * k + 1 := ⟨P / 5, by omega⟩
  ring_nf
  omega

/-- Special exponent `13` is impossible. Let `N` be an odd perfect number with special prime `q`,
let every other prime factor have exponent `2` or `4`, and let `q` be the second largest prime
factor (some prime factor `P > q`, every prime factor other than `P` at most `q`). Under the
explicit hypotheses `3 ∤ N` and `5 ∤ N`, `v_q(N) ≠ 13`. Restricted family result: the family is
not excluded. The Main Theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81 (2012)) gives
`3 ∤ N` and `5 ∤ N` in this family; it is not formalized here. Novelty not verified. -/
theorem mixed_special_exponent_ne_thirteen_of_not_three_five_dvd {N q P : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) :
    N.factorization q ≠ 13 := by
  classical
  intro h13
  have hq60 : q % 60 = 1 := by
    rcases special_exponent_eq_one_or_thirteen_of_not_three_five_dvd h hq hodd hP hqP hsecond
      hexp h3 h5 with h1 | h1
    · omega
    · exact h1.2
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hPq : P ≠ q := by omega
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by omega)
  have hP2 : P ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hP)
  have hq2 : q ≠ 2 := by omega
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  have hmax : ∀ p ∈ N.primeFactors, p ≤ P := by
    intro p hp
    by_cases hpP : p = P
    · omega
    · have := hsecond p hp hpP
      omega
  -- the ledger at `q`
  have hrest : N.primeFactors.filter (fun p => ¬ p < q) = {q, P} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hpq⟩
      by_cases hpP : p = P
      · exact Or.inr hpP
      · have := hsecond p hp hpP
        exact Or.inl (by omega)
    · rintro (rfl | rfl)
      · exact ⟨hqmem, lt_irrefl _⟩
      · exact ⟨hP, by omega⟩
  have hledq := sigmaWeight_sum_eq h.2 hq hq2
  rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q), hrest,
    Finset.sum_pair hPq.symm, sigmaWeight_self hq] at hledq
  have hlow := mixed_sum_sigmaWeight_below_special_le_mod_of_not_three_dvd h hq hexp h3
  have hlow7 : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ 7 := by
    split_ifs at hlow <;> omega
  have hw6 : 6 ≤ sigmaWeight N P q := by omega
  have hqd : q ^ 6 ∣ σ 1 (P ^ N.factorization P) :=
    (pow_dvd_pow q hw6).trans (Nat.ordProj_dvd _ _)
  have hσq : σ 1 (q ^ N.factorization q) = ∑ i ∈ Finset.range 14, q ^ i := by
    rw [sigma_one_apply_prime_pow hq, h13]
  have hPodd : P % 2 = 1 := Nat.odd_iff.mp (hPp.eq_two_or_odd'.resolve_left hP2)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.eq_two_or_odd'.resolve_left hq2)
  rcases hexp P hP hPq with hd2 | hd4
  · -- `v_P(N) = 2`
    rw [hd2, sigma_one_apply_prime_pow hPp] at hqd
    have hP3 := moa_cube_le hq.two_le hqd
    have hq2P : q ^ 2 ≤ P := le_trans (Nat.pow_le_pow_right hq.pos (by norm_num)) hP3
    obtain ⟨-, hr2⟩ := moa_rest_le_one h hexp h3 h5 hP hPq hsecond hd2 hq2P
    have hledP := sigmaWeight_sum_eq h.2 hPp hP2
    rw [← Finset.add_sum_erase _ _ hqmem, hd2] at hledP
    have hwP : P ^ sigmaWeight N q P ∣ σ 1 (q ^ N.factorization q) := Nat.ordProj_dvd _ _
    rw [hσq] at hwP
    obtain ⟨T, hT, hTq⟩ := moa_split hq.one_le hPp hP2 hwP
    have hrle := (moa_rest_le_one h hexp h3 h5 hP hPq hsecond hd2 hq2P).1
    have hw1 : sigmaWeight N q P ≠ 0 := by omega
    have hPT : P ∣ T := (dvd_pow_self P hw1).trans hT
    have hT0 : 0 < T := by
      have : 1 < q ^ 7 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
    by_cases hs : ∑ p ∈ N.primeFactors.erase q, sigmaWeight N p P = 0
    · have hw2 : sigmaWeight N q P = 2 := by omega
      rw [hw2] at hT
      have hle := Nat.le_of_dvd hT0 hT
      have hPlt : P < q ^ 4 := by
        by_contra hc
        have e1 : (q ^ 4) ^ 2 ≤ P ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have e2 : (q ^ 4) ^ 2 = q ^ 7 * q := by ring
        have e3 : q ^ 7 * 3 ≤ q ^ 7 * q := Nat.mul_le_mul_left _ hq3
        have e4 : 1 ≤ q ^ 7 := Nat.one_le_pow _ _ hq.pos
        omega
      obtain ⟨hTe, -⟩ := moa_core_two hq3 hqd hP3 hPlt hPT hTq
      rw [hTe, pow_two] at hT
      have h1 : P ∣ P + 1 := (Nat.mul_dvd_mul_iff_left hPp.pos).mp hT
      have h2 : P ∣ 1 := (Nat.dvd_add_right (dvd_refl P)).mp h1
      exact hPp.one_lt.ne' (Nat.dvd_one.mp h2)
    · obtain ⟨hP51, hPlt⟩ := hr2 hs
      obtain ⟨hTe, hT1⟩ := moa_core_two hq3 hqd hP3 hPlt hPT hTq
      rw [hTe] at hT1
      have e1 : q ^ 7 % 5 = 1 := by
        rw [Nat.pow_mod, show q % 5 = 1 by omega]
      have e2 := moa_mod_five hP51
      omega
  · -- `v_P(N) = 4`
    rw [hd4, sigma_one_apply_prime_pow hPp] at hqd
    have hcube := mixed_largest_cube_dvd_sigma_special h hexp h3 h5 hP hmax hPq hd4
    rw [hσq] at hcube
    obtain ⟨T, hT, hTq⟩ := moa_split hq.one_le hPp hP2 hcube
    exact moa_core_four hq3 hqodd hPodd hqP hqd hT hTq

/-- One prime above the special prime. Let `N` be an odd perfect number with special prime `q`,
let every other prime factor have exponent `2` or `4`, and let `q` be the second largest prime
factor (some prime factor `P > q`, every prime factor other than `P` at most `q`). Under the
explicit hypotheses `3 ∤ N` and `5 ∤ N`: `v_q(N) = 1`, `v_P(N) = 2`, `P ≡ 11 (mod 15)` and
`P < q ^ 2`. Restricted family result: the family is not excluded (the case `q < P < q ^ 2`
remains). The Main Theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81 (2012)) gives `3 ∤ N`
and `5 ∤ N` in this family; it is not formalized here. Novelty not verified. -/
theorem mixed_one_above {N q P : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) :
    N.factorization q = 1 ∧ N.factorization P = 2 ∧ P % 15 = 11 ∧ P < q ^ 2 := by
  classical
  have ha : N.factorization q = 1 := by
    rcases special_exponent_eq_one_or_thirteen_of_not_three_five_dvd h hq hodd hP hqP hsecond
      hexp h3 h5 with h1 | h1
    · exact h1
    · exact absurd h1.1 (mixed_special_exponent_ne_thirteen_of_not_three_five_dvd h hq hodd hP
        hqP hsecond hexp h3 h5)
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hPq : P ≠ q := by omega
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by omega)
  have hP2 : P ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hP)
  have hq2 : q ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hqmem)
  have hmax : ∀ p ∈ N.primeFactors, p ≤ P := by
    intro p hp
    by_cases hpP : p = P
    · omega
    · have := hsecond p hp hpP
      omega
  obtain ⟨hd2, h15⟩ :=
    mixed_largest_exponent_two_of_special_exponent_one h hexp h3 h5 hP hmax hPq ha
  refine ⟨ha, hd2, h15, ?_⟩
  by_contra hc
  have hq2P : q ^ 2 ≤ P := not_lt.mp hc
  obtain ⟨hr1, -⟩ := moa_rest_le_one h hexp h3 h5 hP hPq hsecond hd2 hq2P
  have hledP := sigmaWeight_sum_eq h.2 hPp hP2
  rw [← Finset.add_sum_erase _ _ hqmem, hd2] at hledP
  have hs : σ 1 (q ^ N.factorization q) = q + 1 := by
    rw [ha, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ, add_comm]
  have hnd : ¬ P ∣ q + 1 := by
    rintro ⟨k, hk⟩
    have ho1 := hq.eq_two_or_odd.resolve_left hq2
    have ho2 := hPp.eq_two_or_odd.resolve_left hP2
    rcases k with _ | _ | k
    · omega
    · omega
    · nlinarith
  have hq0 : sigmaWeight N q P = 0 := by
    unfold sigmaWeight
    rw [hs]
    exact Nat.factorization_eq_zero_of_not_dvd hnd
  omega

end OddPerfect

#print axioms OddPerfect.mixed_special_exponent_ne_thirteen_of_not_three_five_dvd
#print axioms OddPerfect.mixed_one_above
