import OddPerfect.Seed.Collision
import Mathlib

/-!
# Common prime powers in square ratios of the third cyclotomic polynomial

Work on Question 10 of Ochem and Zelinsky, arXiv:2607.19746, in the even gap case.

For `x^2 + x + 1 = K^2 * (y^2 + y + 1)` with `K ≥ 2` we write `V = 2*y + 1` and
`2*x + 1 = K*V + t`. The main structural fact is that `t^2 + 3 = K*m` and
`2*V*t + m = 3*K` for a natural number `m` (an odd number).

If a prime power `p^b` (with `b ≥ 1`) divides both `K` and `y^2+y+1`, then
`t ≡ ±V` and hence `m ≡ ±6` modulo `p^b`. Since `m` is odd this gives `p^b ≤ m + 6`, and the
exact identity `(3K - m)^2 = 4 V^2 (K m - 3)` then forces `K > p^b (y^2+y+1)` when `y ≥ 3`
(`common_prime_power_forces_large_scale`). For Question 10 with even gap `a - b = 2k`
this gives `p^(2b) r < p^k`, so `k > 2b` and `a > 5b` (`even_gap_exponent_bound`).
The previously known bound was `k > b`, that is `a > 3b`. Full impossibility of the even
gap case is not proved here.
-/

namespace OddPerfect

/-- Parametrization of a square ratio. If `x^2+x+1 = K^2 (y^2+y+1)` with `K ≥ 2`, then
there are natural numbers `t > 0` (even) and `m` (odd) with `2x+1 = K(2y+1) + t`,
`t^2 + 3 = K m` and `2(2y+1) t + m = 3K`. No primality is assumed. -/
theorem phi3_square_ratio_param {x y K : ℕ} (hK : 2 ≤ K)
    (h : x ^ 2 + x + 1 = K ^ 2 * (y ^ 2 + y + 1)) :
    ∃ t m : ℕ, 0 < t ∧ t % 2 = 0 ∧ m % 2 = 1 ∧ 2 * x + 1 = K * (2 * y + 1) + t ∧
      t ^ 2 + 3 = K * m ∧ 2 * (2 * y + 1) * t + m = 3 * K := by
  set V := 2 * y + 1 with hV
  have hs : (2 * x + 1) ^ 2 + 3 = (K * V) ^ 2 + 3 * K ^ 2 := by
    rw [hV]; nlinarith only [h]
  have hlt : K * V < 2 * x + 1 := by
    by_contra! hle
    have := Nat.pow_le_pow_left hle 2
    have hsq : 4 ≤ K ^ 2 := by nlinarith
    omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hlt.le
  have htpos : 0 < t := by omega
  have hbal : K * (2 * V * t) + t ^ 2 + 3 = K * (3 * K) := by
    rw [ht] at hs; nlinarith only [hs]
  -- `K` is odd because `x^2+x+1` is odd.
  have hFodd : (x ^ 2 + x + 1) % 2 = 1 := by
    have : Even (x * (x + 1)) := Nat.even_mul_succ_self x
    obtain ⟨c, hc⟩ := this
    have : x ^ 2 + x + 1 = 2 * c + 1 := by rw [sq]; linarith [hc]
    omega
  have hKodd : K % 2 = 1 := by
    rcases Nat.even_or_odd K with ⟨c, hc⟩ | ⟨c, hc⟩
    · exfalso
      rw [h, hc] at hFodd
      have : (c + c) ^ 2 * (y ^ 2 + y + 1) = 2 * (2 * c ^ 2 * (y ^ 2 + y + 1)) := by ring
      omega
    · omega
  have hVodd : V % 2 = 1 := by omega
  have hteven : t % 2 = 0 := by
    have h1 : (K * V) % 2 = 1 := by rw [Nat.mul_mod, hKodd, hVodd]
    omega
  have hdvd : K ∣ t ^ 2 + 3 := by
    have h1 : K ∣ K * (3 * K) := dvd_mul_right _ _
    rw [← hbal, Nat.add_assoc] at h1
    exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h1
  obtain ⟨m, hm⟩ := hdvd
  have hKpos : 0 < K := by omega
  have hlin : 2 * V * t + m = 3 * K := by
    apply Nat.eq_of_mul_eq_mul_left hKpos
    rw [Nat.mul_add, ← hm]; omega
  have hmodd : m % 2 = 1 := by
    have h1 : (t ^ 2 + 3) % 2 = 1 := by
      obtain ⟨c, hc⟩ : 2 ∣ t := Nat.dvd_of_mod_eq_zero hteven
      subst hc; ring_nf; omega
    rw [hm, Nat.mul_mod, hKodd] at h1
    omega
  exact ⟨t, m, htpos, hteven, hmodd, ht, hm, hlin⟩

/-- The size part of `common_prime_power_forces_large_scale`, isolated as a lemma about
natural numbers. -/
private theorem size_contradiction {y V F K t m p q : ℕ} (hy : 3 ≤ y) (hV : V = 2 * y + 1)
    (hF : F = y ^ 2 + y + 1) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≤ q) (hqF : q ≤ F)
    (hqm : q ≤ m + 6) (hpK : p ∣ K) (hpcong : (p : ℤ) ∣ (m : ℤ) - 6 ∨ (p : ℤ) ∣ (m : ℤ) + 6)
    (hmodd : m % 2 = 1) (hm : t ^ 2 + 3 = K * m) (hlin : 2 * V * t + m = 3 * K)
    (hylt : y < K) (hcon : K ≤ q * F) : False := by
  have hpm : p ≤ m + 6 := le_trans hpq hqm
  have hVF : V ^ 2 + 3 = 4 * F := by rw [hV, hF]; ring
  have hV7 : 7 ≤ V := by omega
  have hq5 : 5 ≤ q := le_trans hp5 hpq
  have h2Vt : 2 * V * t < 3 * K := by omega
  have hsq : (2 * V * t) ^ 2 < (3 * K) ^ 2 := Nat.pow_lt_pow_left h2Vt (by norm_num)
  have hkey1 : 4 * V ^ 2 * (K * m) < 9 * K ^ 2 + 12 * V ^ 2 := by
    rw [← hm]
    have e1 : 4 * V ^ 2 * (t ^ 2 + 3) = (2 * V * t) ^ 2 + 12 * V ^ 2 := by ring
    have e2 : (3 * K) ^ 2 = 9 * K ^ 2 := by ring
    omega
  have hVK : 12 * V * V < 12 * V * (2 * K) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hkey2 : K * (4 * V ^ 2 * m) < K * (9 * K + 24 * V) := by
    have e3 : K * (4 * V ^ 2 * m) = 4 * V ^ 2 * (K * m) := by ring
    have e4 : K * (9 * K + 24 * V) = 9 * K ^ 2 + 12 * V * (2 * K) := by ring
    have e5 : 12 * V * V = 12 * V ^ 2 := by ring
    omega
  have hkey3 : 4 * V ^ 2 * m < 9 * K + 24 * V := Nat.lt_of_mul_lt_mul_left hkey2
  have hkey : 4 * V ^ 2 * m < 9 * (q * F) + 24 * V := by omega
  have hid : 2 * V * t * m + m ^ 2 = 3 * t ^ 2 + 9 := by
    have e1 : 2 * V * t * m + m ^ 2 = (2 * V * t + m) * m := by ring
    rw [e1, hlin, show 3 * K * m = 3 * (K * m) by ring, ← hm]
    ring
  rcases Nat.lt_or_ge q 17 with hq17 | hq17
  · -- Small `p^b`: the cofactor `m` is at most `10`.
    have hqF16 : q * F ≤ 16 * F := Nat.mul_le_mul_right F (by omega)
    have hy3 : 3 * y ≤ y * y := Nat.mul_le_mul_right y hy
    have hm10 : m ≤ 10 := by
      by_contra! hm11
      have h11 : 4 * V ^ 2 * 11 ≤ 4 * V ^ 2 * m := Nat.mul_le_mul_left _ hm11
      nlinarith [hkey, hqF16, hVF, hy3]
    interval_cases m <;> try omega
    · -- m = 1
      have h8 : t ∣ 8 := by
        have h1 : t ∣ 3 * t ^ 2 + 8 := ⟨2 * V, by linarith [hid]⟩
        exact (Nat.dvd_add_right ⟨3 * t, by ring⟩).mp h1
      have ht8 := Nat.le_of_dvd (by norm_num) h8
      interval_cases t <;> norm_num at hm hid <;> try omega
      obtain rfl : K = 19 := by omega
      interval_cases p <;> omega
    · -- m = 3
      interval_cases p <;> first | omega | norm_num at hp
    · -- m = 5
      have h16 : t ∣ 16 := by
        have h1 : t ∣ 10 * V * t + 16 := by
          rw [show 10 * V * t + 16 = 3 * t ^ 2 by linarith [hid]]; exact ⟨3 * t, by ring⟩
        exact (Nat.dvd_add_right ⟨10 * V, by ring⟩).mp h1
      have ht16 := Nat.le_of_dvd (by norm_num) h16
      interval_cases t <;> norm_num at hm hid <;> omega
    · -- m = 7
      have h40 : t ∣ 40 := by
        have h1 : t ∣ 14 * V * t + 40 := by
          rw [show 14 * V * t + 40 = 3 * t ^ 2 by linarith [hid]]; exact ⟨3 * t, by ring⟩
        exact (Nat.dvd_add_right ⟨14 * V, by ring⟩).mp h1
      have ht40 := Nat.le_of_dvd (by norm_num) h40
      interval_cases t <;> norm_num at hm hid <;> omega
    · -- m = 9
      have h3t2 : 3 ∣ t ^ 2 := by
        have : 3 ∣ t ^ 2 + 3 := ⟨3 * K, by linarith [hm]⟩
        exact (Nat.dvd_add_left (dvd_refl 3)).mp this
      obtain ⟨s, hs⟩ := Nat.prime_three.dvd_of_dvd_pow h3t2
      rw [hs] at hm
      have h9 : 9 * s ^ 2 + 3 = 9 * K := by nlinarith [hm]
      omega
  · -- Large `p^b`: use `p^b ≤ m + 6`.
    have h1 : 4 * V ^ 2 * q ≤ 4 * V ^ 2 * (m + 6) := Nat.mul_le_mul_left _ hqm
    have hFq : 17 * F ≤ q * F := Nat.mul_le_mul_right F hq17
    have hy4 : 4 ≤ y := by
      by_contra! hy4
      have : y = 3 := by omega
      have : F = 13 := by rw [hF, this]; norm_num
      omega
    have hy4' : 4 * y ≤ y * y := Nat.mul_le_mul_right y hy4
    have hqV : q * V ^ 2 + 3 * q = 4 * (q * F) := by
      rw [show 4 * (q * F) = q * (4 * F) by ring, ← hVF]; ring
    linarith [hkey, h1, hFq, hqF, hVF, hy4', hqV, hF, hV]

/-- A common prime power forces a large scale. Suppose `x^2+x+1 = K^2 (y^2+y+1)` with
`y ≥ 3`, and suppose a prime power `p^b` with `b ≥ 1` divides both `K` and `y^2+y+1`.
Then `p^b (y^2+y+1) < K`. No hypothesis on `x` or on the other factors of `K` is needed.
The bound `y ≥ 3` cannot be dropped: `18^2+18+1 = 7^2 (2^2+2+1)`. -/
theorem common_prime_power_forces_large_scale {x y K p b : ℕ} (hy : 3 ≤ y) (hp : p.Prime)
    (hb : 0 < b) (hqK : p ^ b ∣ K) (hqF : p ^ b ∣ y ^ 2 + y + 1)
    (h : x ^ 2 + x + 1 = K ^ 2 * (y ^ 2 + y + 1)) :
    p ^ b * (y ^ 2 + y + 1) < K := by
  have hFpos : 0 < y ^ 2 + y + 1 := by positivity
  have hpq : p ∣ p ^ b := dvd_pow_self p hb.ne'
  have hpleq : p ≤ p ^ b := Nat.le_of_dvd (pow_pos hp.pos b) hpq
  have hqleF : p ^ b ≤ y ^ 2 + y + 1 := Nat.le_of_dvd hFpos hqF
  have hKpos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hqleK : p ^ b ≤ K := Nat.le_of_dvd hKpos hqK
  have hK2 : 2 ≤ K := by have := hp.two_le; omega
  obtain ⟨t, m, htpos, hteven, hmodd, -, hm, hlin⟩ := phi3_square_ratio_param hK2 h
  have hFodd : (y ^ 2 + y + 1) % 2 = 1 := by
    obtain ⟨c, hc⟩ : Even (y * (y + 1)) := Nat.even_mul_succ_self y
    have : y ^ 2 + y + 1 = 2 * c + 1 := by rw [sq]; linarith [hc]
    omega
  have hp_ne2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ y ^ 2 + y + 1 := hpq.trans hqF
    omega
  have hp_ne3 : p ≠ 3 := by
    rintro rfl
    have h3K : 3 ∣ K := hpq.trans hqK
    have h3t2 : 3 ∣ t ^ 2 := by
      have : 3 ∣ t ^ 2 + 3 := hm ▸ dvd_mul_of_dvd_left h3K m
      exact (Nat.dvd_add_left (dvd_refl 3)).mp this
    obtain ⟨s, hs⟩ := Nat.prime_three.dvd_of_dvd_pow h3t2
    obtain ⟨K', hK'⟩ := h3K
    obtain ⟨m', hm'⟩ : 3 ∣ m := by
      have e : 2 * (2 * y + 1) * t = 3 * (2 * (2 * y + 1) * s) := by rw [hs]; ring
      omega
    rw [hs, hK', hm'] at hm
    have h9 : 9 * s ^ 2 + 3 = 9 * (K' * m') := by nlinarith [hm]
    omega
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    by_contra hlt
    interval_cases p <;> first | omega | norm_num at hp
  -- Divisibilities in the integers.
  have hqV : ((p ^ b : ℕ) : ℤ) ∣ ((2 * y + 1 : ℕ) : ℤ) ^ 2 + 3 := by
    have e : ((2 * y + 1 : ℕ) : ℤ) ^ 2 + 3 = 4 * ((y ^ 2 + y + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [e]
    exact dvd_mul_of_dvd_right (by exact_mod_cast hqF) 4
  have hqt : ((p ^ b : ℕ) : ℤ) ∣ (t : ℤ) ^ 2 + 3 := by
    have : p ^ b ∣ t ^ 2 + 3 := hm ▸ dvd_mul_of_dvd_left hqK m
    exact_mod_cast this
  have hprod : ((p ^ b : ℕ) : ℤ) ∣
      (((2 * y + 1 : ℕ) : ℤ) - t) * (((2 * y + 1 : ℕ) : ℤ) + t) := by
    have := dvd_sub hqV hqt
    have e : ((2 * y + 1 : ℕ) : ℤ) ^ 2 + 3 - ((t : ℤ) ^ 2 + 3) =
        (((2 * y + 1 : ℕ) : ℤ) - t) * (((2 * y + 1 : ℕ) : ℤ) + t) := by ring
    rwa [e] at this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcastq : ((p ^ b : ℕ) : ℤ) = (p : ℤ) ^ b := by push_cast; rfl
  have hpV : ¬ (p : ℤ) ∣ ((2 * y + 1 : ℕ) : ℤ) := by
    intro hd
    have h1 : (p : ℤ) ∣ ((2 * y + 1 : ℕ) : ℤ) ^ 2 := dvd_pow hd two_ne_zero
    have h2 : (p : ℤ) ∣ ((2 * y + 1 : ℕ) : ℤ) ^ 2 + 3 :=
      (show (p : ℤ) ∣ ((p ^ b : ℕ) : ℤ) by exact_mod_cast hpq).trans hqV
    have h3 : (p : ℤ) ∣ 3 := (dvd_add_right h1).mp h2
    have h4 : p ∣ 3 := by exact_mod_cast h3
    exact hp_ne3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h4)
  have hside : ((p ^ b : ℕ) : ℤ) ∣ ((2 * y + 1 : ℕ) : ℤ) - t ∨
      ((p ^ b : ℕ) : ℤ) ∣ ((2 * y + 1 : ℕ) : ℤ) + t := by
    rw [hcastq] at hprod ⊢
    by_cases hminus : (p : ℤ) ∣ ((2 * y + 1 : ℕ) : ℤ) - t
    · left
      have hplus : ¬ (p : ℤ) ∣ ((2 * y + 1 : ℕ) : ℤ) + t := by
        intro hplus
        have h2 : (p : ℤ) ∣ 2 * ((2 * y + 1 : ℕ) : ℤ) := by
          have := dvd_add hminus hplus
          rwa [show ((2 * y + 1 : ℕ) : ℤ) - t + (((2 * y + 1 : ℕ) : ℤ) + t) =
            2 * ((2 * y + 1 : ℕ) : ℤ) by ring] at this
        rcases hpZ.dvd_or_dvd h2 with h2' | h2'
        · have : p ∣ 2 := by exact_mod_cast h2'
          exact hp_ne2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
        · exact hpV h2'
      exact hpZ.pow_dvd_of_dvd_mul_right b hplus hprod
    · right
      exact hpZ.pow_dvd_of_dvd_mul_left b hminus hprod
  -- The cofactor `m` is congruent to `6` or `-6` modulo `p^b`.
  have hmZ : (m : ℤ) = 3 * K - 2 * ((2 * y + 1 : ℕ) : ℤ) * t := by
    have := congrArg (Nat.cast : ℕ → ℤ) hlin
    push_cast at this ⊢
    linarith
  have hqKZ : ((p ^ b : ℕ) : ℤ) ∣ (K : ℤ) := by exact_mod_cast hqK
  have hcong : ((p ^ b : ℕ) : ℤ) ∣ (m : ℤ) - 6 ∨ ((p ^ b : ℕ) : ℤ) ∣ (m : ℤ) + 6 := by
    rcases hside with h1 | h1
    · left
      have e : (m : ℤ) - 6 = 3 * K - 2 * t * (((2 * y + 1 : ℕ) : ℤ) - t) -
          2 * ((t : ℤ) ^ 2 + 3) := by rw [hmZ]; ring
      rw [e]
      exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right hqKZ 3) (dvd_mul_of_dvd_right h1 _))
        (dvd_mul_of_dvd_right hqt 2)
    · right
      have e : (m : ℤ) + 6 = 3 * K - 2 * t * (((2 * y + 1 : ℕ) : ℤ) + t) +
          2 * ((t : ℤ) ^ 2 + 3) := by rw [hmZ]; ring
      rw [e]
      exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hqKZ 3) (dvd_mul_of_dvd_right h1 _))
        (dvd_mul_of_dvd_right hqt 2)
  have hqm : p ^ b ≤ m + 6 := by
    have hm6 : m ≠ 6 := by omega
    rcases hcong with h1 | h1
    · by_cases h6 : 6 < m
      · have := Int.le_of_dvd (by omega) h1; omega
      · have h2 : ((p ^ b : ℕ) : ℤ) ∣ 6 - (m : ℤ) := by
          have := dvd_neg.mpr h1; rwa [neg_sub] at this
        have := Int.le_of_dvd (by omega) h2; omega
    · have := Int.le_of_dvd (by omega) h1; omega
  have hpcong : (p : ℤ) ∣ (m : ℤ) - 6 ∨ (p : ℤ) ∣ (m : ℤ) + 6 := by
    have hpqZ : (p : ℤ) ∣ ((p ^ b : ℕ) : ℤ) := by exact_mod_cast hpq
    rcases hcong with h1 | h1
    · exact Or.inl (hpqZ.trans h1)
    · exact Or.inr (hpqZ.trans h1)
  -- Size estimates.
  have hpK : p ∣ K := hpq.trans hqK
  by_contra! hcon
  have hylt : y < K := OPNCollision.smaller_input_lt_scale (by omega)
    (by unfold OPNCollision.phi3; exact h)
  exact size_contradiction hy rfl rfl hp hp5 hpleq hqleF hqm hpK hpcong hmodd hm hlin hylt hcon

/-- Even gaps in Question 10 of Ochem and Zelinsky. Suppose `p` is prime, `b, k ≥ 1`,
`y ≥ 3`, `x^2+x+1 = p^(b+2k) r` and `y^2+y+1 = p^b r`. Then `p^(2b) r < p^k`.
Neither `x`, `y` nor `r` needs to be prime, and `r` is any natural number. -/
theorem even_gap_scale_bound {x y p r b k : ℕ} (hy : 3 ≤ y) (hp : p.Prime) (hb : 0 < b)
    (hk : 0 < k) (hx : x ^ 2 + x + 1 = p ^ (b + 2 * k) * r)
    (hyv : y ^ 2 + y + 1 = p ^ b * r) : p ^ (2 * b) * r < p ^ k := by
  have hratio : x ^ 2 + x + 1 = (p ^ k) ^ 2 * (y ^ 2 + y + 1) := by
    rw [hx, hyv]; ring
  have hFpos : 0 < y ^ 2 + y + 1 := by positivity
  by_cases hkb : k ≤ b
  · exfalso
    have hd : p ^ k ∣ y ^ 2 + y + 1 := hyv ▸ dvd_mul_of_dvd_left (pow_dvd_pow p hkb) r
    have := common_prime_power_forces_large_scale hy hp hk (dvd_refl _) hd hratio
    have := Nat.le_mul_of_pos_right (p ^ k) hFpos
    omega
  · have hd : p ^ b ∣ y ^ 2 + y + 1 := hyv ▸ dvd_mul_right _ _
    have := common_prime_power_forces_large_scale hy hp hb (pow_dvd_pow p (by omega)) hd hratio
    rw [hyv] at this
    calc p ^ (2 * b) * r = p ^ b * (p ^ b * r) := by ring
      _ < p ^ k := this

/-- Exponent form of `even_gap_scale_bound`: under the same hypotheses `2b < k`, so the
larger exponent `a = b + 2k` satisfies `5b < a`. This improves `a > 3b` from
`OPNGap.no_even_gap_of_le` (which is the case `k ≤ b`). -/
theorem even_gap_exponent_bound {x y p r b k : ℕ} (hy : 3 ≤ y) (hp : p.Prime) (hb : 0 < b)
    (hk : 0 < k) (hx : x ^ 2 + x + 1 = p ^ (b + 2 * k) * r)
    (hyv : y ^ 2 + y + 1 = p ^ b * r) : 2 * b < k ∧ 5 * b < b + 2 * k := by
  have h := even_gap_scale_bound hy hp hb hk hx hyv
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0] at hyv; simp at hyv
    · exact h0
  have h1 : p ^ (2 * b) < p ^ k := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hr) h
  have h2 : 2 * b < k := (pow_lt_pow_iff_right₀ hp.one_lt).mp h1
  omega

end OddPerfect

#print axioms OddPerfect.phi3_square_ratio_param
#print axioms OddPerfect.common_prime_power_forces_large_scale
#print axioms OddPerfect.even_gap_scale_bound
#print axioms OddPerfect.even_gap_exponent_bound
