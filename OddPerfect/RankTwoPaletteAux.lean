import OddPerfect.PaletteGlue
import OddPerfect.LargestPrimeCapacity

/-!
# Arithmetic lemmas for the rank two palette

Helper results for `OddPerfect.RankTwoPalette`. No novelty is claimed.

* `pow_dvd_cyclotomic_orderOf_of_pow_dvd_sigma` (one cyclotomic factor): for primes `q < P`
  with `q + 1 < P` and `a + 1 < P`, if `P ^ k ∣ σ(q ^ a)` with `k ≥ 1`, then the order `t` of `q`
  modulo `P` satisfies `3 ≤ t`, `t ∣ a + 1`, and `P ^ k ∣ Φ_t(q)`. Indeed
  `q ^ (a + 1) - 1 = ∏_{d ∣ a + 1} Φ_d(q)`, and `P ∣ Φ_d(q)` with `P ∤ d` forces `d = t`.
* `pow_lt_succ_pow_totient_of_pow_dvd_sigma`: hence `P ^ k < (q + 1) ^ φ(a + 1)`.
* `two_mul_succ_pow_lt_pow`, `rankTwo_seventeen_false`, `rankTwo_chain_fourteen_false`,
  `rankTwo_chain_eq_one`: size comparisons, all with denominators cleared.
* `geom_eleven_eq_zero_of_pow_thirteen_mul`: in a field with `11 ≠ 0`, if
  `1 + x + ⋯ + x ^ 10 = 0` and `x ^ 13 y = 1`, then `1 + y + ⋯ + y ^ 10 = 0`.
* `eq_of_dvd_geom_five_of_mul_lt`: two primes `u, v` with `u ^ 2, u v, v ^ 2 < P` and
  `P ∣ 1 + u + ⋯ + u ^ 4`, `P ∣ 1 + v + ⋯ + v ^ 4` (for a prime `P ≠ 5`) are equal: otherwise
  `1, u, v, u ^ 2, u v, v ^ 2` would be six distinct fifth roots of unity modulo `P`.
* `rankTwo_twentyone_signed`, `rankTwo_twentyone_le_thirteen`,
  `rankTwo_twentyone_thirteen_false`: the case `σ(q ^ 21)` divisible by `P ^ 3`.
-/

open ArithmeticFunction Polynomial
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- `σ(p ^ k) (p - 1) = p ^ (k + 1) - 1` over the integers, for a prime `p`. -/
theorem rankTwo_sigma_mul_sub_one {p k : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ k) : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul _ _

/-- `σ(p ^ k) < 2 p ^ k` for a prime `p`. -/
theorem rankTwo_sigma_lt_two_mul {p k : ℕ} (hp : p.Prime) : σ 1 (p ^ k) < 2 * p ^ k := by
  have hg := rankTwo_sigma_mul_sub_one (k := k) hp
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hpk : (0 : ℤ) < (p : ℤ) ^ k := by positivity
  zify
  rw [pow_succ] at hg
  nlinarith

/-! ## One cyclotomic factor -/

/-- One cyclotomic factor. Let `q < P` be primes with `q + 1 < P` and `a + 1 < P`, and let
`P ^ k ∣ σ(q ^ a)` with `k ≥ 1`. Then `t = ord_P(q)` satisfies `3 ≤ t`, `t ∣ a + 1`, and
`P ^ k ∣ Φ_t(q)`. -/
theorem pow_dvd_cyclotomic_orderOf_of_pow_dvd_sigma {q P a k : ℕ} (hq : q.Prime) (hP : P.Prime)
    (hqP : q + 1 < P) (haP : a + 1 < P) (hk : 1 ≤ k) (hd : P ^ k ∣ σ 1 (q ^ a)) :
    3 ≤ orderOf (q : ZMod P) ∧ orderOf (q : ZMod P) ∣ a + 1 ∧
      (P : ℤ) ^ k ∣ (cyclotomic (orderOf (q : ZMod P)) ℤ).eval (q : ℤ) := by
  have : Fact P.Prime := ⟨hP⟩
  have hz : (P : ℤ) ^ k ∣ (q : ℤ) ^ (a + 1) - 1 := by
    rw [← rankTwo_sigma_mul_sub_one hq]
    exact Dvd.dvd.mul_right (by exact_mod_cast hd) _
  have hz1 : (P : ℤ) ∣ (q : ℤ) ^ (a + 1) - 1 :=
    (dvd_pow_self (P : ℤ) (by omega)).trans hz
  have hpow : (q : ZMod P) ^ (a + 1) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).mpr hz1
    push_cast at this
    exact sub_eq_zero.mp this
  have htd : orderOf (q : ZMod P) ∣ a + 1 := orderOf_dvd_of_pow_eq_one hpow
  have hinj : ∀ m n : ℕ, m < P → n < P → (m : ZMod P) = n → m = n := by
    intro m n hm hn hmn
    rw [ZMod.natCast_eq_natCast_iff'] at hmn
    rwa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at hmn
  have hq2 := hq.two_le
  have ht3 : 3 ≤ orderOf (q : ZMod P) := by
    have ht0 : 0 < orderOf (q : ZMod P) := Nat.pos_of_dvd_of_pos htd (by omega)
    have h2 := pow_orderOf_eq_one (q : ZMod P)
    by_contra hlt
    have hcases : (q : ZMod P) = 1 ∨ (q : ZMod P) + 1 = 0 := by
      rcases (show orderOf (q : ZMod P) = 1 ∨ orderOf (q : ZMod P) = 2 by omega) with h1 | h1
      · rw [h1, pow_one] at h2
        exact Or.inl h2
      · rw [h1] at h2
        have : ((q : ZMod P) - 1) * ((q : ZMod P) + 1) = 0 := by
          linear_combination h2
        rcases mul_eq_zero.mp this with h | h
        · exact Or.inl (sub_eq_zero.mp h)
        · exact Or.inr h
    rcases hcases with h1 | h1
    · have := hinj q 1 (by omega) (by omega) (by simpa using h1)
      omega
    · have h1' : ((q + 1 : ℕ) : ZMod P) = 0 := by push_cast; exact h1
      rw [ZMod.natCast_eq_zero_iff] at h1'
      have := Nat.le_of_dvd (by omega) h1'
      omega
  refine ⟨ht3, htd, ?_⟩
  have hmem : orderOf (q : ZMod P) ∈ (a + 1).divisors := Nat.mem_divisors.mpr ⟨htd, by omega⟩
  have hprod : (q : ℤ) ^ (a + 1) - 1 = (cyclotomic (orderOf (q : ZMod P)) ℤ).eval (q : ℤ) *
      ∏ d ∈ (a + 1).divisors.erase (orderOf (q : ZMod P)), (cyclotomic d ℤ).eval (q : ℤ) := by
    have h := congrArg (eval (q : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one (Nat.succ_pos a) ℤ)
    rw [eval_prod, ← Finset.mul_prod_erase _ (fun d => (cyclotomic d ℤ).eval (q : ℤ)) hmem] at h
    simpa using h.symm
  have hPz : Prime (P : ℤ) := Nat.prime_iff_prime_int.mp hP
  have hQ : ¬ (P : ℤ) ∣
      ∏ d ∈ (a + 1).divisors.erase (orderOf (q : ZMod P)), (cyclotomic d ℤ).eval (q : ℤ) := by
    rw [hPz.dvd_finsetProd_iff]
    rintro ⟨d, hd, hdu⟩
    obtain ⟨hdt, hdmem⟩ := Finset.mem_erase.mp hd
    have hdle := Nat.divisor_le hdmem
    have := (orderOf_eq_of_dvd_cyclotomic_eval hP hdu fun hh => by
      have := Nat.le_of_dvd (Nat.pos_of_mem_divisors hdmem) hh; omega).1
    exact hdt this.symm
  rw [hprod] at hz
  exact (((hPz.coprime_iff_not_dvd).mpr hQ).pow_left).dvd_of_dvd_mul_right hz

/-- Size form of one cyclotomic factor: in the setting of
`pow_dvd_cyclotomic_orderOf_of_pow_dvd_sigma`, `P ^ k < (q + 1) ^ φ(a + 1)`. -/
theorem pow_lt_succ_pow_totient_of_pow_dvd_sigma {q P a k : ℕ} (hq : q.Prime) (hP : P.Prime)
    (hqP : q + 1 < P) (haP : a + 1 < P) (hk : 1 ≤ k) (hd : P ^ k ∣ σ 1 (q ^ a)) :
    P ^ k < (q + 1) ^ (a + 1).totient := by
  obtain ⟨ht3, htd, hdvd⟩ := pow_dvd_cyclotomic_orderOf_of_pow_dvd_sigma hq hP hqP haP hk hd
  obtain ⟨hpos, hlt⟩ := cyclotomic_eval_int_pos_lt ht3 hq.one_lt
  have h1 := Int.le_of_dvd hpos hdvd
  have h2 : ((q : ℤ) + 1) ^ (orderOf (q : ZMod P)).totient ≤
      ((q : ℤ) + 1) ^ (a + 1).totient :=
    pow_le_pow_right₀ (by omega) (Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.succ_pos a))
      (Nat.totient_dvd_of_dvd htd))
  have : ((P ^ k : ℕ) : ℤ) < (((q + 1) ^ (a + 1).totient : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast this

/-! ## Size comparisons -/

private theorem mul_pow_succ_le {m x : ℤ} (n : ℕ) (hm : 0 ≤ m) (h : m ≤ x) :
    m ^ n * (x + 1) ^ n ≤ (m + 1) ^ n * x ^ n := by
  rw [← mul_pow, ← mul_pow]
  exact pow_le_pow_left₀ (by nlinarith) (by nlinarith) n

/-- `2 (q + 1) ^ k < q ^ (k + 3)` for `q ≥ 5` and `k ≤ 18`. -/
theorem two_mul_succ_pow_lt_pow {q k : ℕ} (hq : 5 ≤ q) (hk : k ≤ 18) :
    2 * (q + 1) ^ k < q ^ (k + 3) := by
  have h1 : 5 ^ k * (q + 1) ^ k ≤ 6 ^ k * q ^ k := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (by omega) k
  have h2 : 2 * 6 ^ k < 125 * 5 ^ k := by interval_cases k <;> norm_num
  have h3 : 125 ≤ q ^ 3 :=
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hqk : 0 < q ^ k := by positivity
  have h4 : 5 ^ k * (2 * (q + 1) ^ k) < 5 ^ k * q ^ (k + 3) :=
    calc 5 ^ k * (2 * (q + 1) ^ k) = 2 * (5 ^ k * (q + 1) ^ k) := by ring
      _ ≤ 2 * (6 ^ k * q ^ k) := Nat.mul_le_mul_left 2 h1
      _ = (2 * 6 ^ k) * q ^ k := by ring
      _ < (125 * 5 ^ k) * q ^ k := mul_lt_mul_of_pos_right h2 hqk
      _ = (5 ^ k * q ^ k) * 125 := by ring
      _ ≤ (5 ^ k * q ^ k) * q ^ 3 := Nat.mul_le_mul_left _ h3
      _ = 5 ^ k * q ^ (k + 3) := by ring
  exact Nat.lt_of_mul_lt_mul_left h4

/-- The size contradiction for the special exponent `17`: there are no integers `q ≥ 5`,
`P > 200000`, `S` with `P ^ 3 < (q + 1) ^ 6`, `q ^ 9 ≤ S` and `S (P - 1) < P ^ 5`. -/
theorem rankTwo_seventeen_false {q P S : ℤ} (hq : 5 ≤ q) (hP : 200000 < P)
    (hP3 : P ^ 3 < (q + 1) ^ 6) (hS : q ^ 9 ≤ S) (hSP : S * (P - 1) < P ^ 5) : False := by
  have hS0 : 0 ≤ S := le_trans (by positivity) hS
  have hP1 : 0 < P - 1 := by linarith
  have h1 : q ^ 27 ≤ S ^ 3 :=
    calc q ^ 27 = (q ^ 9) ^ 3 := by ring
      _ ≤ S ^ 3 := pow_le_pow_left₀ (by positivity) hS 3
  have h2 : (S * (P - 1)) ^ 3 < (P ^ 5) ^ 3 :=
    pow_lt_pow_left₀ hSP (by positivity) (by norm_num)
  have h3 : (P ^ 3) ^ 4 < ((q + 1) ^ 6) ^ 4 :=
    pow_lt_pow_left₀ hP3 (by positivity) (by norm_num)
  have hc : q ^ 27 * (P - 1) ^ 3 < P ^ 3 * (q + 1) ^ 24 :=
    calc q ^ 27 * (P - 1) ^ 3 ≤ S ^ 3 * (P - 1) ^ 3 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (S * (P - 1)) ^ 3 := by ring
      _ < (P ^ 5) ^ 3 := h2
      _ = P ^ 3 * (P ^ 3) ^ 4 := by ring
      _ < P ^ 3 * ((q + 1) ^ 6) ^ 4 := mul_lt_mul_of_pos_left h3 (by positivity)
      _ = P ^ 3 * (q + 1) ^ 24 := by ring
  have n1 : 10000 * P ^ 3 ≤ 10001 * (P - 1) ^ 3 := by
    have := mul_pow_succ_le (m := 200000) (x := P - 1) 3 (by norm_num) (by linarith)
    rw [sub_add_cancel] at this
    nlinarith
  have n2 : 10001 * (q + 1) ^ 24 ≤ 10000 * q ^ 27 := by
    have := mul_pow_succ_le (m := 5) (x := q) 24 (by norm_num) hq
    have h3 : (125 : ℤ) ≤ q ^ 3 :=
      calc (125 : ℤ) = 5 ^ 3 := by norm_num
        _ ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq 3
    have hq24 : (0 : ℤ) ≤ q ^ 24 := by positivity
    have e : q ^ 27 = q ^ 24 * q ^ 3 := by ring
    rw [e]
    nlinarith
  have hpos1 : (0 : ℤ) ≤ P ^ 3 := by positivity
  have hpos2 : (0 : ℤ) ≤ q ^ 27 := by positivity
  nlinarith [mul_le_mul n1 n2 (by positivity) (by positivity)]

/-- Chain for `w ≥ 14` at the special exponent `21`: there are no integers `Q, R ≥ 5`, `G`, `S`
with `R ^ 3 ≤ G`, `G (Q - 1) < Q ^ 11`, `Q ^ 14 ≤ S` and `S (R - 1) < R ^ 5`. -/
theorem rankTwo_chain_fourteen_false {Q R G S : ℤ} (hQ : 5 ≤ Q) (hR : 5 ≤ R) (hRG : R ^ 3 ≤ G)
    (hG : G * (Q - 1) < Q ^ 11) (hS : Q ^ 14 ≤ S) (hSR : S * (R - 1) < R ^ 5) : False := by
  have hS0 : 0 ≤ S := le_trans (by positivity) hS
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity) hRG
  have hR1 : 0 < R - 1 := by linarith
  have hQ1 : 0 < Q - 1 := by linarith
  have h1 : Q ^ 42 ≤ S ^ 3 :=
    calc Q ^ 42 = (Q ^ 14) ^ 3 := by ring
      _ ≤ S ^ 3 := pow_le_pow_left₀ (by positivity) hS 3
  have h2 : (S * (R - 1)) ^ 3 < (R ^ 5) ^ 3 :=
    pow_lt_pow_left₀ hSR (by positivity) (by norm_num)
  have h3 : (R ^ 3) ^ 4 ≤ G ^ 4 := pow_le_pow_left₀ (by positivity) hRG 4
  have h4 : (G * (Q - 1)) ^ 4 < (Q ^ 11) ^ 4 :=
    pow_lt_pow_left₀ hG (by positivity) (by norm_num)
  have hc : Q ^ 42 * ((R - 1) ^ 3 * (Q - 1) ^ 4) < R ^ 3 * Q ^ 44 :=
    calc Q ^ 42 * ((R - 1) ^ 3 * (Q - 1) ^ 4) ≤ S ^ 3 * ((R - 1) ^ 3 * (Q - 1) ^ 4) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (S * (R - 1)) ^ 3 * (Q - 1) ^ 4 := by ring
      _ < (R ^ 5) ^ 3 * (Q - 1) ^ 4 := mul_lt_mul_of_pos_right h2 (by positivity)
      _ = R ^ 3 * ((R ^ 3) ^ 4 * (Q - 1) ^ 4) := by ring
      _ ≤ R ^ 3 * (G ^ 4 * (Q - 1) ^ 4) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (by positivity))
            (by positivity)
      _ = R ^ 3 * (G * (Q - 1)) ^ 4 := by ring
      _ < R ^ 3 * (Q ^ 11) ^ 4 := mul_lt_mul_of_pos_left h4 (by positivity)
      _ = R ^ 3 * Q ^ 44 := by ring
  have h5a : R ^ 3 ≤ 2 * (R - 1) ^ 3 := by nlinarith [sq_nonneg (R - 1), sq_nonneg (R - 5)]
  have h5b : 2 * Q ^ 2 ≤ (Q - 1) ^ 4 := by nlinarith [sq_nonneg (Q - 1), sq_nonneg (Q - 5)]
  have h5 : R ^ 3 * Q ^ 2 ≤ (R - 1) ^ 3 * (Q - 1) ^ 4 := by
    have := mul_le_mul h5a h5b (by positivity) (by positivity)
    nlinarith
  have := mul_le_mul_of_nonneg_left h5 (show (0 : ℤ) ≤ Q ^ 42 by positivity)
  have e : Q ^ 42 * (R ^ 3 * Q ^ 2) = R ^ 3 * Q ^ 44 := by ring
  linarith

private theorem chain_numeric {R Q : ℤ} (hR : 200000 < R) (hQ : 61 ≤ Q) :
    3 * (R ^ 10 * Q ^ 13) ≤ 4 * ((R - 1) ^ 10 * (Q - 1) ^ 13) := by
  have n1 := mul_pow_succ_le (m := 200000) (x := R - 1) 10 (by norm_num) (by linarith)
  have n2 := mul_pow_succ_le (m := 60) (x := Q - 1) 13 (by norm_num) (by linarith)
  rw [sub_add_cancel] at n1 n2
  have hY0 : (0 : ℤ) ≤ (R - 1) ^ 10 := by have : (0 : ℤ) ≤ R - 1 := by linarith
                                          positivity
  have hW0 : (0 : ℤ) ≤ (Q - 1) ^ 13 := by have : (0 : ℤ) ≤ Q - 1 := by linarith
                                          positivity
  have hX0 : (0 : ℤ) ≤ R ^ 10 := by positivity
  have hZ0 : (0 : ℤ) ≤ Q ^ 13 := by positivity
  generalize R ^ 10 = X at n1 hX0 ⊢
  generalize (R - 1) ^ 10 = Y at n1 hY0 ⊢
  generalize Q ^ 13 = Z at n2 hZ0 ⊢
  generalize (Q - 1) ^ 13 = W at n2 hW0 ⊢
  norm_num at n1 n2
  have H := mul_le_mul n1 n2 (by positivity) (by positivity)
  nlinarith [mul_nonneg hY0 hW0, mul_nonneg hX0 hZ0]

/-- Chain for `w = 13` at the special exponent `21`. Let `Q ≥ 61`, `R > 200000`, `h, k ≥ 1`,
`C > 0` be integers with `2 R k < 3 C ^ 10`, `R ^ 3 h (Q - 1) < Q ^ 11` and
`Q ^ 13 C (R - 1) < R ^ 5`. Then `k = 1` and `h = 1`. -/
theorem rankTwo_chain_eq_one {Q R C h k : ℤ} (hQ : 61 ≤ Q) (hR : 200000 < R) (hk : 1 ≤ k)
    (hh : 1 ≤ h) (hC0 : 0 < C) (hH : 2 * (R * k) < 3 * C ^ 10)
    (hG : R ^ 3 * h * (Q - 1) < Q ^ 11)
    (hS : Q ^ 13 * C * (R - 1) < R ^ 5) : k = 1 ∧ h = 1 := by
  have hh13 : h ≤ h ^ 13 := le_self_pow₀ hh (by norm_num)
  have n3 := chain_numeric hR hQ
  have hR0 : 0 < R := by linarith
  have hQ0 : 0 < Q := by linarith
  have hR1 : 0 < R - 1 := by linarith
  have hQ1 : 0 < Q - 1 := by linarith
  generalize R - 1 = a at *
  generalize Q - 1 = b at *
  suffices hkh : k * h ^ 13 < 2 by
    have h13 : 1 ≤ h ^ 13 := le_trans hh hh13
    constructor <;> nlinarith
  by_contra hcon
  push Not at hcon
  have E1 : 2 * (R * k) * (Q ^ 130 * a ^ 10) < 3 * R ^ 50 :=
    calc 2 * (R * k) * (Q ^ 130 * a ^ 10) < 3 * C ^ 10 * (Q ^ 130 * a ^ 10) :=
          mul_lt_mul_of_pos_right hH (by positivity)
      _ = 3 * (Q ^ 13 * C * a) ^ 10 := by ring
      _ < 3 * (R ^ 5) ^ 10 := by
          have := pow_lt_pow_left₀ hS (by positivity) (show (10 : ℕ) ≠ 0 by norm_num)
          linarith
      _ = 3 * R ^ 50 := by ring
  have E2 : (R ^ 3 * h * b) ^ 13 < (Q ^ 11) ^ 13 :=
    pow_lt_pow_left₀ hG (by positivity) (by norm_num)
  have E3 := mul_lt_mul'' E1 E2 (by positivity) (by positivity)
  have n4 : 4 * (a ^ 10 * b ^ 13) ≤ (k * h ^ 13) * (2 * (a ^ 10 * b ^ 13)) := by
    have hpos : (0 : ℤ) ≤ a ^ 10 * b ^ 13 := by positivity
    nlinarith
  have hRQ : (0 : ℤ) < R ^ 40 * Q ^ 130 := by positivity
  have e1 : 2 * (R * k) * (Q ^ 130 * a ^ 10) * (R ^ 3 * h * b) ^ 13 =
      (k * h ^ 13) * (2 * (a ^ 10 * b ^ 13)) * (R ^ 40 * Q ^ 130) := by ring
  have e2 : 3 * R ^ 50 * (Q ^ 11) ^ 13 = 3 * (R ^ 10 * Q ^ 13) * (R ^ 40 * Q ^ 130) := by ring
  rw [e1, e2] at E3
  have E4 := lt_of_mul_lt_mul_right E3 hRQ.le
  linarith

/-! ## A field lemma and six fifth roots of unity -/

/-- In a field with `11 ≠ 0`: if `1 + x + ⋯ + x ^ 10 = 0` and `x ^ 13 y = 1`, then
`1 + y + ⋯ + y ^ 10 = 0`. -/
theorem geom_eleven_eq_zero_of_pow_thirteen_mul {K : Type*} [Field K] {x y : K}
    (h11 : (11 : K) ≠ 0) (hx : ∑ i ∈ Finset.range 11, x ^ i = 0) (hxy : x ^ 13 * y = 1) :
    ∑ i ∈ Finset.range 11, y ^ i = 0 := by
  have hx11 : x ^ 11 = 1 := by
    have := geom_sum_mul x 11
    rw [hx, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hx
    exact h11 (by exact_mod_cast hx)
  have hx2y : x ^ 2 * y = 1 :=
    calc x ^ 2 * y = x ^ 11 * x ^ 2 * y := by rw [hx11, one_mul]
      _ = x ^ 13 * y := by ring
      _ = 1 := hxy
  have hy11 : y ^ 11 = 1 :=
    calc y ^ 11 = (x ^ 11) ^ 2 * y ^ 11 := by rw [hx11]; ring
      _ = (x ^ 2 * y) ^ 11 := by ring
      _ = 1 := by rw [hx2y, one_pow]
  have hy1 : y ≠ 1 := by
    rintro rfl
    have hx2 : (x - 1) * (x + 1) = 0 := by linear_combination hx2y
    rcases mul_eq_zero.mp hx2 with h | h
    · exact hx1 (sub_eq_zero.mp h)
    · have : x = -1 := eq_neg_of_add_eq_zero_left h
      rw [this] at hx
      norm_num [Finset.sum_range_succ] at hx
  have := geom_sum_mul y 11
  rw [hy11, sub_self] at this
  exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hy1)

private theorem pow_five_of_dvd {P w : ℕ} [Fact P.Prime] (hP5 : P ≠ 5)
    (hw : P ∣ ∑ i ∈ Finset.range 5, w ^ i) : (w : ZMod P) ^ 5 = 1 ∧ (w : ZMod P) ≠ 1 := by
  have hS : ∑ i ∈ Finset.range 5, (w : ZMod P) ^ i = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ P).mpr hw
    push_cast at this
    exact this
  refine ⟨?_, ?_⟩
  · have := geom_sum_mul (w : ZMod P) 5
    rw [hS, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  · intro h1
    rw [h1] at hS
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hS
    have h5 : ((5 : ℕ) : ZMod P) = 0 := by exact_mod_cast hS
    rw [ZMod.natCast_eq_zero_iff] at h5
    exact hP5 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_five).mp h5)

private theorem eq_of_dvd_geom_five_of_lt {P u v : ℕ} (hP : P.Prime) (hP5 : P ≠ 5)
    (hu : u.Prime) (hv : v.Prime) (huv : u < v) (hvv : v * v < P)
    (hdu : P ∣ ∑ i ∈ Finset.range 5, u ^ i) (hdv : P ∣ ∑ i ∈ Finset.range 5, v ^ i) : False := by
  have : Fact P.Prime := ⟨hP⟩
  obtain ⟨hu5, -⟩ := pow_five_of_dvd hP5 hdu
  obtain ⟨hv5, -⟩ := pow_five_of_dvd hP5 hdv
  have hu2 := hu.two_le
  have hvu : v ≠ u * u := by
    intro he
    exact Nat.not_prime_mul (by omega) (by omega) (he ▸ hv)
  have o1 : u < u * u := by nlinarith
  have o2 : u * u < u * v := by nlinarith
  have o3 : v < u * v := by nlinarith
  have o4 : u * v < v * v := by nlinarith
  set L : List ℕ := [1, u, v, u * u, u * v, v * v] with hL
  have hlt : ∀ x ∈ L, x < P := by
    intro x hx
    simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hnd : L.Nodup := by
    generalize hA : u * u = A at *
    generalize hB : u * v = B at *
    generalize hC : v * v = C at *
    simp only [hL, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true, not_false_eq_true]
    omega
  have hinj : ∀ x ∈ L, ∀ y ∈ L, (x : ZMod P) = (y : ZMod P) → x = y := by
    intro x hx y hy hxy
    rw [ZMod.natCast_eq_natCast_iff'] at hxy
    rwa [Nat.mod_eq_of_lt (hlt x hx), Nat.mod_eq_of_lt (hlt y hy)] at hxy
  have hnd' : (L.map (fun x : ℕ => (x : ZMod P))).Nodup := hnd.map_on hinj
  have hsub : (L.map (fun x : ℕ => (x : ZMod P))).toFinset ⊆
      nthRootsFinset 5 (1 : ZMod P) := by
    intro z hz
    rw [mem_nthRootsFinset (by norm_num)]
    simp only [List.mem_toFinset, List.mem_map, hL, List.mem_cons, List.not_mem_nil,
      or_false] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> push_cast <;>
      simp only [mul_pow, hu5, hv5, one_pow, mul_one]
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd'] at hc
  have hc2 : (nthRootsFinset 5 (1 : ZMod P)).card ≤ 5 := by
    classical
    rw [nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (card_nthRoots 5 1)
  simp [hL] at hc
  omega

/-- Two primes `u, v` with `u ^ 2, u v, v ^ 2 < P` such that the prime `P ≠ 5` divides both
`1 + u + ⋯ + u ^ 4` and `1 + v + ⋯ + v ^ 4` are equal: otherwise `1, u, v, u ^ 2, u v, v ^ 2`
would be six distinct fifth roots of unity modulo `P`. -/
theorem eq_of_dvd_geom_five_of_mul_lt {P u v : ℕ} (hP : P.Prime) (hP5 : P ≠ 5)
    (hu : u.Prime) (hv : v.Prime) (huu : u * u < P) (hvv : v * v < P)
    (hdu : P ∣ ∑ i ∈ Finset.range 5, u ^ i) (hdv : P ∣ ∑ i ∈ Finset.range 5, v ^ i) :
    u = v := by
  rcases lt_trichotomy u v with h | h | h
  · exact (eq_of_dvd_geom_five_of_lt hP hP5 hu hv h hvv hdu hdv).elim
  · exact h
  · exact (eq_of_dvd_geom_five_of_lt hP hP5 hv hu h huu hdv hdu).elim

/-! ## The special exponent 21 -/

/-- Bounds for the signed geometric sum `F(x) = ∑_{i < 11} (s x) ^ i`, `s = ± 1`, `x ≥ 3`:
`0 < F(x)`, `2 F(x) < 3 x ^ 10` and `F(x) (x - 1) < x ^ 11`. -/
theorem rankTwo_signed_bounds {s x : ℤ} (hs : s = 1 ∨ s = -1) (hx : 3 ≤ x) :
    0 < ∑ i ∈ Finset.range 11, (s * x) ^ i ∧
      2 * ∑ i ∈ Finset.range 11, (s * x) ^ i < 3 * x ^ 10 ∧
      (∑ i ∈ Finset.range 11, (s * x) ^ i) * (x - 1) < x ^ 11 := by
  have hy : 3 ≤ x ^ 10 := le_trans hx (le_self_pow₀ (by linarith) (by norm_num))
  have e11 : x ^ 11 = x * x ^ 10 := by ring
  rw [e11]
  rcases hs with rfl | rfl
  · have e : (∑ i ∈ Finset.range 11, (1 * x) ^ i) * (x - 1) = x * x ^ 10 - 1 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      ring
    generalize ∑ i ∈ Finset.range 11, (1 * x) ^ i = A at e ⊢
    generalize x ^ 10 = y at e hy ⊢
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · have e : (∑ i ∈ Finset.range 11, (-1 * x) ^ i) * (x + 1) = x * x ^ 10 + 1 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      ring
    generalize ∑ i ∈ Finset.range 11, (-1 * x) ^ i = B at e ⊢
    generalize x ^ 10 = y at e hy ⊢
    have hB : 0 < B := by nlinarith
    have hBy : B < y := by nlinarith
    refine ⟨hB, by linarith, by nlinarith⟩

/-- If `P ^ 3 ∣ σ(q ^ 21)` for primes `q`, `P` with `q + 1 < P`, then `P ^ 3` divides
`∑_{i < 11} (s q) ^ i` for a sign `s = ± 1`: `σ(q ^ 21) = A B (q + 1)` with
`A = ∑ q ^ i`, `B = ∑ (-q) ^ i`, and `P` divides at most one of `A`, `B` since
`(q + 1) B - (q - 1) A = 2`. -/
theorem rankTwo_twentyone_signed {q P : ℕ} (hq : q.Prime) (hP : P.Prime) (hqP : q + 1 < P)
    (hd : P ^ 3 ∣ σ 1 (q ^ 21)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (P : ℤ) ^ 3 ∣ ∑ i ∈ Finset.range 11, (s * q) ^ i := by
  set A : ℤ := ∑ i ∈ Finset.range 11, (1 * (q : ℤ)) ^ i with hA
  set B : ℤ := ∑ i ∈ Finset.range 11, (-1 * (q : ℤ)) ^ i with hB
  have hsig : ((σ 1 (q ^ 21) : ℕ) : ℤ) = A * B * ((q : ℤ) + 1) := by
    rw [sigma_one_apply_prime_pow hq, hA, hB]
    push_cast
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have hz : (P : ℤ) ^ 3 ∣ A * B * ((q : ℤ) + 1) := by
    rw [← hsig]
    exact_mod_cast hd
  have hPz : Prime (P : ℤ) := Nat.prime_iff_prime_int.mp hP
  have hq1 : ¬ (P : ℤ) ∣ (q : ℤ) + 1 := by
    intro hh
    have := Int.le_of_dvd (by positivity) hh
    omega
  have hAB : ¬ ((P : ℤ) ∣ A ∧ (P : ℤ) ∣ B) := by
    rintro ⟨h1, h2⟩
    have eA : A * ((q : ℤ) - 1) = (q : ℤ) ^ 11 - 1 := by
      rw [hA]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring
    have eB : B * ((q : ℤ) + 1) = (q : ℤ) ^ 11 + 1 := by
      rw [hB]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring
    have h3 : (P : ℤ) ∣ B * ((q : ℤ) + 1) - A * ((q : ℤ) - 1) :=
      dvd_sub (h2.mul_right _) (h1.mul_right _)
    rw [eA, eB, show (q : ℤ) ^ 11 + 1 - ((q : ℤ) ^ 11 - 1) = 2 by ring] at h3
    have := Int.le_of_dvd (by norm_num) h3
    have := hq.two_le
    omega
  by_cases hBd : (P : ℤ) ∣ B
  · have hAd : ¬ (P : ℤ) ∣ A := fun hh => hAB ⟨hh, hBd⟩
    have hcop : IsCoprime ((P : ℤ) ^ 3) (A * ((q : ℤ) + 1)) := by
      refine IsCoprime.pow_left ((hPz.coprime_iff_not_dvd).mpr ?_)
      intro hh
      rcases hPz.dvd_or_dvd hh with h1 | h1
      · exact hAd h1
      · exact hq1 h1
    refine ⟨-1, Or.inr rfl, hcop.dvd_of_dvd_mul_right ?_⟩
    rw [show B * (A * ((q : ℤ) + 1)) = A * B * ((q : ℤ) + 1) by ring]
    exact hz
  · have hcop : IsCoprime ((P : ℤ) ^ 3) (B * ((q : ℤ) + 1)) := by
      refine IsCoprime.pow_left ((hPz.coprime_iff_not_dvd).mpr ?_)
      intro hh
      rcases hPz.dvd_or_dvd hh with h1 | h1
      · exact hBd h1
      · exact hq1 h1
    refine ⟨1, Or.inl rfl, hcop.dvd_of_dvd_mul_right ?_⟩
    rw [show A * (B * ((q : ℤ) + 1)) = A * B * ((q : ℤ) + 1) by ring]
    exact hz

private theorem sigma_four_eq {P : ℕ} (hP : P.Prime) :
    σ 1 (P ^ 4) = 1 + P + P ^ 2 + P ^ 3 + P ^ 4 := by
  rw [sigma_one_apply_prime_pow hP]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The case `w ≥ 14` at the special exponent `21`: primes `q ≥ 5` and `P` with `q + 1 < P`
allow no `P ^ 3 ∣ σ(q ^ 21)` together with `q ^ 14 ∣ σ(P ^ 4)`. -/
theorem rankTwo_twentyone_le_thirteen {q P : ℕ} (hq : q.Prime) (hP : P.Prime) (hq5 : 5 ≤ q)
    (hqP : q + 1 < P) (hd : P ^ 3 ∣ σ 1 (q ^ 21)) (hw : q ^ 14 ∣ σ 1 (P ^ 4)) : False := by
  obtain ⟨s, hs, hG⟩ := rankTwo_twentyone_signed hq hP hqP hd
  obtain ⟨hG0, -, hGq⟩ := rankTwo_signed_bounds (x := (q : ℤ)) hs (by exact_mod_cast (by omega))
  have hRG := Int.le_of_dvd hG0 hG
  have hS : ((q ^ 14 : ℕ) : ℤ) ≤ ((σ 1 (P ^ 4) : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_of_dvd (ArithmeticFunction.sigma_pos 1 _
      (pow_ne_zero _ hP.ne_zero)) hw
  have hSR := rankTwo_sigma_mul_sub_one (k := 4) hP
  push_cast at hS
  exact rankTwo_chain_fourteen_false (Q := q) (R := P) (by exact_mod_cast hq5)
    (by exact_mod_cast (by omega)) hRG hGq hS (by rw [hSR]; norm_num)

/-- Residues modulo `9` for the sign `+`. -/
theorem rankTwo_mod_nine_pos : ∀ q P C : ZMod 9, (q = 1 ∨ q = 4 ∨ q = 7) →
    ∑ i ∈ Finset.range 11, q ^ i = P ^ 3 → q ^ 13 * C = 1 + P + P ^ 2 + P ^ 3 + P ^ 4 →
    ∑ i ∈ Finset.range 11, C ^ i = P → False := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  decide

/-- Residues modulo `9` for the sign `-`. -/
theorem rankTwo_mod_nine_neg : ∀ q P C : ZMod 9, (q = 1 ∨ q = 4 ∨ q = 7) →
    ∑ i ∈ Finset.range 11, (-q) ^ i = P ^ 3 → q ^ 13 * C = 1 + P + P ^ 2 + P ^ 3 + P ^ 4 →
    ∑ i ∈ Finset.range 11, (-C) ^ i = P → False := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  decide

/-- The case `w = 13` at the special exponent `21`. For primes `q ≥ 61` with `q % 3 = 1` and
`P > 200000` with `q + 1 < P`, the conditions `P ^ 3 ∣ σ(q ^ 21)` and `q ^ 13 ∣ σ(P ^ 4)` are
incompatible. With `F(x) = ∑_{i < 11} (s x) ^ i` and `P ^ 3 ∣ F(q)`, write
`σ(P ^ 4) = q ^ 13 C`. Modulo `P`, `q ^ 13 C ≡ 1`, so `P ∣ F(C)`; the sizes force
`F(q) = P ^ 3` and `F(C) = P`, which fails modulo `9`. -/
theorem rankTwo_twentyone_thirteen_false {q P : ℕ} (hq : q.Prime) (hP : P.Prime)
    (hq61 : 61 ≤ q) (hq3 : q % 3 = 1) (hP200 : 200000 < P) (hqP : q + 1 < P)
    (hd : P ^ 3 ∣ σ 1 (q ^ 21)) (hw : q ^ 13 ∣ σ 1 (P ^ 4)) : False := by
  have : Fact P.Prime := ⟨hP⟩
  obtain ⟨s, hs, hG⟩ := rankTwo_twentyone_signed hq hP hqP hd
  obtain ⟨C, hC⟩ := hw
  have hσ := sigma_four_eq hP
  have hPodd : P % 2 = 1 := Nat.odd_iff.mp (hP.odd_of_ne_two (by omega))
  have hσ2 : (1 + P + P ^ 2 + P ^ 3 + P ^ 4) % 2 = 1 := by
    simp [Nat.add_mod, Nat.pow_mod, hPodd]
  have hC2 : C % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one C with h0 | h1
    · exfalso
      have : (q ^ 13 * C) % 2 = 0 := by simp [Nat.mul_mod, h0]
      rw [← hC, hσ] at this
      omega
    · exact h1
  have hx : ∑ i ∈ Finset.range 11, ((s : ZMod P) * q) ^ i = 0 := by
    have h1 : (P : ℤ) ∣ ∑ i ∈ Finset.range 11, (s * q) ^ i :=
      (dvd_pow_self _ (by norm_num)).trans hG
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).mpr h1
    push_cast at this
    exact this
  have hs2 : (s : ZMod P) ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hqC : (q : ZMod P) ^ 13 * C = 1 := by
    have : ((q ^ 13 * C : ℕ) : ZMod P) = ((1 + P + P ^ 2 + P ^ 3 + P ^ 4 : ℕ) : ZMod P) := by
      rw [← hC, hσ]
    push_cast at this
    rw [ZMod.natCast_self] at this
    simpa using this
  have hxy : ((s : ZMod P) * q) ^ 13 * ((s : ZMod P) * C) = 1 :=
    calc ((s : ZMod P) * q) ^ 13 * ((s : ZMod P) * C)
        = ((s : ZMod P) ^ 2) ^ 7 * ((q : ZMod P) ^ 13 * C) := by ring
      _ = 1 := by rw [hs2, hqC, one_pow, one_mul]
  have h11 : (11 : ZMod P) ≠ 0 := by
    intro h0
    have h0' : ((11 : ℕ) : ZMod P) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    have := Nat.le_of_dvd (by norm_num) h0'
    omega
  have hy := geom_eleven_eq_zero_of_pow_thirteen_mul h11 hx hxy
  have hH : (P : ℤ) ∣ ∑ i ∈ Finset.range 11, (s * (C : ℤ)) ^ i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).mp
    push_cast
    exact hy
  have hC1 : C ≠ 1 := by
    rintro rfl
    simp only [Nat.cast_one, mul_one] at hH
    rcases hs with rfl | rfl
    · have e : ∑ i ∈ Finset.range 11, (1 : ℤ) ^ i = 11 := by norm_num
      rw [e] at hH
      have := Int.le_of_dvd (by norm_num) hH
      omega
    · have e : ∑ i ∈ Finset.range 11, (-1 : ℤ) ^ i = 1 := by
        norm_num [Finset.sum_range_succ]
      rw [e] at hH
      have := Int.le_of_dvd (by norm_num) hH
      omega
  have hC3 : 3 ≤ C := by omega
  obtain ⟨hG0, -, hGq⟩ := rankTwo_signed_bounds (x := (q : ℤ)) hs (by exact_mod_cast (by omega))
  obtain ⟨hH0, hH2, -⟩ := rankTwo_signed_bounds (x := (C : ℤ)) hs (by exact_mod_cast hC3)
  obtain ⟨h', hh'⟩ := hG
  obtain ⟨k, hk⟩ := hH
  have hh1 : 0 < h' := by
    rw [hh'] at hG0
    exact pos_of_mul_pos_right hG0 (by positivity)
  have hk1 : 0 < k := by
    rw [hk] at hH0
    exact pos_of_mul_pos_right hH0 (by positivity)
  have hSR := rankTwo_sigma_mul_sub_one (k := 4) hP
  rw [hC] at hSR
  push_cast at hSR
  have hS : (q : ℤ) ^ 13 * C * ((P : ℤ) - 1) < (P : ℤ) ^ 5 := by rw [hSR]; norm_num
  rw [hk] at hH2
  rw [hh'] at hGq
  obtain ⟨rfl, rfl⟩ := rankTwo_chain_eq_one (Q := q) (R := P) (C := C) (h := h') (k := k)
    (by exact_mod_cast hq61) (by exact_mod_cast hP200) hk1 hh1 (by exact_mod_cast (by omega))
    hH2 hGq hS
  have hq9 : (q : ZMod 9) = 1 ∨ (q : ZMod 9) = 4 ∨ (q : ZMod 9) = 7 := by
    have : q % 9 = 1 ∨ q % 9 = 4 ∨ q % 9 = 7 := by omega
    rw [← ZMod.natCast_mod q 9]
    rcases this with h | h | h <;> rw [h] <;> simp
  have e1 := congrArg (Int.cast : ℤ → ZMod 9) hh'
  have e3 := congrArg (Int.cast : ℤ → ZMod 9) hk
  have e2 : ((q ^ 13 * C : ℕ) : ZMod 9) = ((1 + P + P ^ 2 + P ^ 3 + P ^ 4 : ℕ) : ZMod 9) := by
    rw [← hC, hσ]
  push_cast at e1 e2 e3
  rcases hs with rfl | rfl
  · simp only [Int.cast_one, one_mul, mul_one] at e1 e3
    exact rankTwo_mod_nine_pos q P C hq9 e1 e2 e3
  · simp only [Int.cast_neg, Int.cast_one, neg_one_mul, mul_one] at e1 e3
    exact rankTwo_mod_nine_neg q P C hq9 e1 e2 e3

end OddPerfect

#print axioms OddPerfect.rankTwo_sigma_mul_sub_one
#print axioms OddPerfect.rankTwo_sigma_lt_two_mul
#print axioms OddPerfect.pow_dvd_cyclotomic_orderOf_of_pow_dvd_sigma
#print axioms OddPerfect.pow_lt_succ_pow_totient_of_pow_dvd_sigma
#print axioms OddPerfect.two_mul_succ_pow_lt_pow
#print axioms OddPerfect.rankTwo_seventeen_false
#print axioms OddPerfect.rankTwo_chain_fourteen_false
#print axioms OddPerfect.rankTwo_chain_eq_one
#print axioms OddPerfect.geom_eleven_eq_zero_of_pow_thirteen_mul
#print axioms OddPerfect.eq_of_dvd_geom_five_of_mul_lt
#print axioms OddPerfect.rankTwo_signed_bounds
#print axioms OddPerfect.rankTwo_twentyone_signed
#print axioms OddPerfect.rankTwo_twentyone_le_thirteen
#print axioms OddPerfect.rankTwo_mod_nine_pos
#print axioms OddPerfect.rankTwo_mod_nine_neg
#print axioms OddPerfect.rankTwo_twentyone_thirteen_false
