import Mathlib

/-!
# A power series certificate bounds the prime in `2 t ^ 2 = 1 + σ(p ^ (2 h))`

In the open shape of the inequality `q < m` (see `special_lt_or_shape` in
`OddPerfect/SpecialBelow.lean`) an odd perfect number would have a prime `p` with even exponent
`e = 2 h`, `σ(p ^ e) = q` and `q + 1 = 2 t ^ 2`. This module uses only the equation
`2 t ^ 2 = 1 + σ(p ^ (2 h))` and shows that `p` is bounded in terms of `h`.

The argument: take natural numbers `D > 0` and `c_0 = D, c_1, ..., c_h` with
`2 ∑_{i + j = k} c_i c_j = D ^ 2` for `1 ≤ k ≤ h` and `2 c_i ≤ D` for `i ≥ 1` (they are `D` times
the first coefficients of the power series of `√((1 - X / 2) / (1 - X))`). With
`A = ∑ c_i p ^ i` and `U = D t`, the polynomial identity
`2 A(X) ^ 2 ≡ D ^ 2 (2 + X + ... + X ^ h) (mod X ^ (h + 1))` gives
`p ^ (h + 1) ∣ (U - A) (U + A)`. If `p > 2 D` then `p` divides at most one factor (since
`A ≡ D (mod p)`), so `p ^ (h + 1)` divides one of them; but `0 < U - A < U + A < p ^ (h + 1)`
by size. Hence `p ≤ max 7 (2 D)`.

This does not exclude the shape: it only bounds `p` for each exponent. Novelty was not
verified.
-/

open Finset Polynomial

namespace OddPerfect

/-- The certificate congruence: if `c_0 = D` and `2 ∑_{i + j = k} c_i c_j = D ^ 2` for
`1 ≤ k ≤ h`, then `x ^ (h + 1)` divides `2 A ^ 2 - D ^ 2 (1 + ∑_{i ≤ h} x ^ i)` for every integer
`x`, where `A = ∑_{i ≤ h} c_i x ^ i`. -/
theorem pow_succ_dvd_cert_sq_sub (c : ℕ → ℕ) {h D : ℕ} (hc0 : c 0 = D)
    (hck : ∀ k, 1 ≤ k → k ≤ h → 2 * ∑ ij ∈ antidiagonal k, c ij.1 * c ij.2 = D ^ 2) (x : ℤ) :
    x ^ (h + 1) ∣ 2 * (∑ i ∈ range (h + 1), (c i : ℤ) * x ^ i) ^ 2 -
      (D : ℤ) ^ 2 * (1 + ∑ i ∈ range (h + 1), x ^ i) := by
  set Q : ℤ[X] := ∑ i ∈ range (h + 1), C (c i : ℤ) * X ^ i with hQ
  have hQc : ∀ a, a ≤ h → Q.coeff a = c a := by
    intro a ha
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Nat.lt_succ_of_le ha]
  have hdvd : (X : ℤ[X]) ^ (h + 1) ∣
      C 2 * Q ^ 2 - C ((D : ℤ) ^ 2) * (1 + ∑ i ∈ range (h + 1), X ^ i) := by
    rw [X_pow_dvd_iff]
    intro d hd
    have hs : ∑ ab ∈ antidiagonal d, Q.coeff ab.1 * Q.coeff ab.2 =
        ((∑ ab ∈ antidiagonal d, c ab.1 * c ab.2 : ℕ) : ℤ) := by
      push_cast
      refine Finset.sum_congr rfl fun ab hab => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      rw [hQc _ (by omega), hQc _ (by omega)]
    rw [coeff_sub, coeff_C_mul, coeff_C_mul, pow_two, coeff_mul, hs, coeff_add, coeff_one,
      finsetSum_coeff]
    simp only [coeff_X_pow]
    rw [Finset.sum_ite_eq]
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp [hc0]
      ring
    · have h1 := hck d hd0 (by omega)
      have h2 : (2 : ℤ) * ((∑ ab ∈ antidiagonal d, c ab.1 * c ab.2 : ℕ) : ℤ) = (D : ℤ) ^ 2 := by
        exact_mod_cast h1
      have hmem : d ∈ range (h + 1) := mem_range.mpr hd
      simp only [hd0.ne', if_false, hmem, if_true]
      linear_combination h2
  have := eval_dvd (x := x) hdvd
  simpa [hQ, eval_finsetSum] using this

/-- Bound on the prime base: if `p` is a prime with
`2 t ^ 2 = 1 + ∑_{i ≤ 2 h} p ^ i = 1 + σ(p ^ (2 h))` and `h ≥ 1`, then `p ≤ max 7 (2 D)` for
every certificate `D, c` of degree `h` (see the module docstring); `p = 2` needs no separate
hypothesis since `p > 7` is assumed in the proof by contradiction. Only this equation is used;
the shape of the inequality `q < m` is not excluded. -/
theorem prime_le_of_two_sq_eq_succ_sigma {h D p t : ℕ} (c : ℕ → ℕ) (hD : 0 < D) (hc0 : c 0 = D)
    (hck : ∀ k, 1 ≤ k → k ≤ h → 2 * ∑ ij ∈ antidiagonal k, c ij.1 * c ij.2 = D ^ 2)
    (hsmall : ∀ i, 1 ≤ i → i ≤ h → 2 * c i ≤ D) (hh : 1 ≤ h) (hp : p.Prime)
    (ht : 2 * t ^ 2 = 1 + ∑ i ∈ Finset.range (2 * h + 1), p ^ i) : p ≤ max 7 (2 * D) := by
  by_contra hlt
  push Not at hlt
  have hp8 : 8 ≤ p := by have := le_max_left 7 (2 * D); omega
  have hpD : 2 * D < p := lt_of_le_of_lt (le_max_right _ _) hlt
  set x : ℤ := (p : ℤ) with hx
  set A : ℤ := ∑ i ∈ range (h + 1), (c i : ℤ) * x ^ i with hA
  set s : ℤ := ∑ i ∈ range (h + 1), x ^ i with hs
  set s2 : ℤ := ∑ i ∈ range (2 * h + 1), x ^ i with hs2
  set P : ℤ := x ^ h with hP
  set T : ℤ := (t : ℤ) with hT
  set E : ℤ := (D : ℤ) with hE
  have hx8 : (8 : ℤ) ≤ x := by rw [hx]; exact_mod_cast hp8
  have hxD : 2 * E + 1 ≤ x := by rw [hx, hE]; exact_mod_cast hpD
  have hE0 : (0 : ℤ) < E := by rw [hE]; exact_mod_cast hD
  have hT0 : (0 : ℤ) ≤ T := by rw [hT]; positivity
  have hxP : x ≤ P := by rw [hP]; exact le_self_pow₀ (by linarith) (by omega)
  have ht2 : 2 * T ^ 2 = 1 + s2 := by
    rw [hT, hs2, hx]; exact_mod_cast ht
  -- geometric sums
  have hgs : s * (x - 1) = x * P - 1 := by
    rw [hs, geom_sum_mul, hP, pow_succ, mul_comm]
  have hgs2 : s2 * (x - 1) = x * P ^ 2 - 1 := by
    rw [hs2, geom_sum_mul, hP, pow_succ, ← pow_mul, mul_comm h 2, mul_comm]
  have hsplit : s2 = s + x ^ (h + 1) * ∑ i ∈ range h, x ^ i := by
    rw [hs2, hs, show 2 * h + 1 = (h + 1) + h by ring, Finset.sum_range_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  -- `A ≥ 0`, `x ∣ A - D`, `2 A ≤ D (1 + s)`
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hAD : x ∣ A - E := by
    rw [hA, Finset.sum_range_succ', pow_zero, mul_one, hc0, ← hE, add_sub_cancel_right]
    exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (dvd_pow_self x (by omega)) _
  have hAle : 2 * A ≤ E * (1 + s) := by
    rw [hA, hs, Finset.sum_range_succ', Finset.sum_range_succ', pow_zero, mul_one, hc0, ← hE]
    have : ∑ i ∈ range h, 2 * ((c (i + 1) : ℤ) * x ^ (i + 1)) ≤
        ∑ i ∈ range h, E * x ^ (i + 1) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' := mem_range.mp hi
      have h0 := hsmall (i + 1) (by omega) (by omega)
      have h1 : (2 * c (i + 1) : ℤ) ≤ E := by rw [hE]; exact_mod_cast h0
      have h2 : (0 : ℤ) ≤ x ^ (i + 1) := by positivity
      nlinarith
    rw [← Finset.mul_sum, ← Finset.mul_sum] at this
    linarith
  -- size estimates
  have hx1 : (0 : ℤ) < x - 1 := by linarith
  have h3s : 3 * (1 + s) < 4 * P := by
    have h1 : (x - 4) * x ≤ (x - 4) * P := mul_le_mul_of_nonneg_left hxP (by linarith)
    have h2 : 3 * (1 + s) * (x - 1) < 4 * P * (x - 1) := by nlinarith
    exact lt_of_mul_lt_mul_right h2 hx1.le
  have hP1 : 8 ≤ P := le_trans hx8 hxP
  have hTP : T < P := by
    by_contra hc
    push Not at hc
    have h1 : P ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by linarith) hc 2
    have h2 : 2 * T ^ 2 * (x - 1) = x - 2 + x * P ^ 2 := by
      rw [ht2]; linear_combination hgs2
    nlinarith
  have hPT : P ^ 2 < 2 * T ^ 2 := by
    have h2 : 2 * T ^ 2 * (x - 1) = x - 2 + x * P ^ 2 := by
      rw [ht2]; linear_combination hgs2
    have h3 : P ^ 2 * (x - 1) < 2 * T ^ 2 * (x - 1) := by nlinarith
    exact lt_of_mul_lt_mul_right h3 hx1.le
  have h2P : 2 * P < 3 * T := by
    by_contra hc
    push Not at hc
    have : (3 * T) ^ 2 ≤ (2 * P) ^ 2 := pow_le_pow_left₀ (by linarith) hc 2
    nlinarith
  have e1 : E * (3 * (1 + s)) < E * (4 * P) := mul_lt_mul_of_pos_left h3s hE0
  have e2 : E * (2 * P) < E * (3 * T) := mul_lt_mul_of_pos_left h2P hE0
  have hAU : A < E * T := by linarith
  have hUA : E * T + A < x ^ (h + 1) := by
    have : x ^ (h + 1) = x * P := by rw [hP, pow_succ, mul_comm]
    rw [this]
    have e3 : E * T < E * P := mul_lt_mul_of_pos_left hTP hE0
    have e4 : (2 * E + 1) * P ≤ x * P := mul_le_mul_of_nonneg_right hxD (by linarith)
    linarith
  -- divisibility
  have hkey := pow_succ_dvd_cert_sq_sub c hc0 hck x
  rw [← hA, ← hs, ← hE] at hkey
  have h2dvd : x ^ (h + 1) ∣ 2 * ((E * T - A) * (E * T + A)) := by
    have : 2 * ((E * T - A) * (E * T + A)) =
        x ^ (h + 1) * (E ^ 2 * ∑ i ∈ range h, x ^ i) -
          (2 * A ^ 2 - E ^ 2 * (1 + s)) := by
      have : 2 * T ^ 2 = 1 + s + x ^ (h + 1) * ∑ i ∈ range h, x ^ i := by rw [ht2, hsplit]; ring
      linear_combination E ^ 2 * this
    rw [this]
    exact dvd_sub (dvd_mul_right _ _) hkey
  have hxprime : Prime x := by rw [hx]; exact Nat.prime_iff_prime_int.mp hp
  have hx2 : ¬ x ∣ 2 := by
    intro hd
    have : p ∣ 2 := by rw [hx] at hd; exact_mod_cast hd
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hprod : x ^ (h + 1) ∣ (E * T - A) * (E * T + A) :=
    hxprime.pow_dvd_of_dvd_mul_left _ hx2 h2dvd
  have hpos : 0 < x ^ (h + 1) := by positivity
  by_cases hm : x ∣ E * T - A
  · have hn : ¬ x ∣ E * T + A := by
      intro hn
      have h1 : x ∣ 2 * E := by
        have : 2 * E = (E * T + A) - (E * T - A) - 2 * (A - E) := by ring
        rw [this]
        exact dvd_sub (dvd_sub hn hm) (Dvd.dvd.mul_left hAD 2)
      have h2 : p ∣ 2 * D := by rw [hx, hE] at h1; exact_mod_cast h1
      have := Nat.le_of_dvd (by omega) h2
      omega
    have := Int.le_of_dvd (by linarith) (hxprime.pow_dvd_of_dvd_mul_right _ hn hprod)
    linarith
  · have := Int.le_of_dvd (by linarith) (hxprime.pow_dvd_of_dvd_mul_left _ hm hprod)
    linarith

end OddPerfect

#print axioms OddPerfect.pow_succ_dvd_cert_sq_sub
#print axioms OddPerfect.prime_le_of_two_sq_eq_succ_sigma
