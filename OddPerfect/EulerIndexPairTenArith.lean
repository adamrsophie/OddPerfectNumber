import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases

/-!
# Arithmetic for the emitter exponent `10` in the two prime Euler index family

Restricted result; no published source was checked; novelty not verified.

Write `F(t) = t ^ 10 + t ^ 9 + ... + t + 2`, so that `F(t) = σ(t ^ 10) + 1`. The lemmas below
are statements about natural numbers only; no perfect number appears.

* `pairTen_receiver_cases`: an odd prime `u` dividing `F(t)` with `t ^ j ≡ 1 (mod u)`, `j` odd
  and `j < 10`, is `3`, or `43` with `j = 7`, or `19` with `j = 9`. Integer combinations
  `A_j F + B_j (X ^ j - 1) = C_j` with `C_j ∈ {12, 36, 12, 516, 2052}`.
* `sigma_prime_pow_mod_cube`: `σ(p ^ f) ≡ 1 + p + p ^ 2 (mod p ^ 3)` for `f ≥ 2`.
* `pairTen_three_mod27`: from `t ^ j ≡ 13 (mod 27)` with `j` odd, `j < 10`: either `j = 1`,
  `t ≡ 13` and `F(t) ≡ 24`, or `j = 5`, `t ≡ 7` and `F(t) ≡ 18`, or `j = 7`, `t ≡ 22` and
  `F(t) ≡ 6`, all modulo `27`.
* `pairTen_fortythree_lift`, `pairTen_fortythree_not`: from `t ^ 7 ≡ 1893 (mod 43 ^ 3)` and
  `43 ∣ F(t)` follow `t ≡ 59344` and `F(t) ≡ 35 * 43 ^ 2 (mod 43 ^ 3)` (three lifts of `43`
  residues each), and then `F(t) = 2 * 43 ^ d * w ^ 2` with `43 ∤ w` is impossible.
* `pairTen_small_prime`, `pairTen_nineteen_not`: for `p ∈ {5, 7, 11, 13, 17, 19}`, an odd `x`
  with `t ^ x ≡ 1 (mod p)` and `p ∣ F(t)` force `p = 19` and `t ≡ 17 (mod 19)`, which is
  incompatible with `2 t + 1 = 3 ^ n`, `n` odd.
* `pairTen_three_rows`: `R_3(7) = 3 * 19`, `R_3(13) = 3 * 61`, `R_3(19) = 3 * 127`, with
  `19, 61, 127` not `4 (mod 9)`.
* `pairTen_envelope`: `(3 / 2) * ∏ p / (p - 1) < 2` over the eleven primes from `23` to `67`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairTenArith

/-- The polynomial `t ^ 10 + ... + t + 2`. -/
private def F (t : ℕ) : ℕ :=
  t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2

private lemma F_mod (m t : ℕ) : F (t % m) % m = F t % m := by
  have ht := Nat.mod_modEq t m
  have h : F (t % m) ≡ F t [MOD m] := by unfold F; gcongr
  exact h

/-- `a % u = 1` as an integer divisibility. -/
private lemma int_dvd_sub_one {a u : ℕ} (h : a % u = 1) : (u : ℤ) ∣ (a : ℤ) - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, a = u * k + 1 := ⟨a / u, by have := Nat.div_add_mod a u; omega⟩
  subst hk
  exact ⟨k, by push_cast; ring⟩

/-- An odd prime dividing `4 * k` divides `k`. -/
private lemma dvd_of_dvd_four_mul {u k : ℕ} (hu : u.Prime) (hu2 : u ≠ 2) (h : u ∣ 4 * k) :
    u ∣ k := by
  rcases (Nat.Prime.dvd_mul hu).mp h with h4 | h4
  · exfalso
    have : u ∣ 2 ^ 2 := by simpa using h4
    exact hu2 ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_two).mp (hu.dvd_of_dvd_pow this))
  · exact h4

end EulerIndexPairTenArith

open EulerIndexPairTenArith

/-- **Receiver primes.** Let `u` be an odd prime dividing `F(t) = t ^ 10 + ... + t + 2` with
`t ^ j ≡ 1 (mod u)`, `j` odd and `j < 10`. Then `u = 3`, or `j = 7` and `u = 43`, or `j = 9`
and `u = 19`. Restricted result; novelty not verified. -/
theorem pairTen_receiver_cases {u t j : ℕ} (hu : u.Prime) (hu2 : u ≠ 2)
    (hF : u ∣ t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2)
    (ht : t ^ j % u = 1) (hj : Odd j) (hj10 : j < 10) :
    u = 3 ∨ (j = 7 ∧ u = 43) ∨ (j = 9 ∧ u = 19) := by
  have hFi : (u : ℤ) ∣ (t : ℤ) ^ 10 + (t : ℤ) ^ 9 + (t : ℤ) ^ 8 + (t : ℤ) ^ 7 + (t : ℤ) ^ 6 +
      (t : ℤ) ^ 5 + (t : ℤ) ^ 4 + (t : ℤ) ^ 3 + (t : ℤ) ^ 2 + t + 2 := by
    exact_mod_cast Int.natCast_dvd_natCast.mpr hF
  have hti := int_dvd_sub_one ht
  push_cast at hti
  have h3 : ∀ k, u ∣ 4 * (3 * k) → u = 3 ∨ u ∣ k := by
    intro k hk
    rcases (Nat.Prime.dvd_mul hu).mp (dvd_of_dvd_four_mul hu hu2 hk) with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_three).mp h)
    · exact Or.inr h
  -- `u ∣ C` from `C = A F + B (t ^ j - 1)`
  have key : ∀ (C : ℕ) (A B : ℤ), (C : ℤ) = A * ((t : ℤ) ^ 10 + (t : ℤ) ^ 9 + (t : ℤ) ^ 8 +
      (t : ℤ) ^ 7 + (t : ℤ) ^ 6 + (t : ℤ) ^ 5 + (t : ℤ) ^ 4 + (t : ℤ) ^ 3 + (t : ℤ) ^ 2 + t +
      2) + B * ((t : ℤ) ^ j - 1) → u ∣ C := by
    intro C A B hC
    have : (u : ℤ) ∣ (C : ℤ) := by
      rw [hC]; exact dvd_add (dvd_mul_of_dvd_right hFi _) (dvd_mul_of_dvd_right hti _)
    exact_mod_cast this
  obtain ⟨k, rfl⟩ := hj
  have hk : k < 5 := by omega
  interval_cases k
  · -- `j = 1`, `C = 12`
    left
    have := key (4 * (3 * 1)) 1 (-(t : ℤ) ^ 9 - 2 * t ^ 8 - 3 * t ^ 7 - 4 * t ^ 6 - 5 * t ^ 5 -
      6 * t ^ 4 - 7 * t ^ 3 - 8 * t ^ 2 - 9 * t - 10) (by push_cast; ring)
    rcases h3 1 this with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd one_pos h) (by have := hu.two_le; omega)
  · -- `j = 3`, `C = 36`
    left
    have := key (4 * (3 * 3)) ((t : ℤ) ^ 2 - 11 * t + 13) (-(t : ℤ) ^ 9 + 10 * t ^ 8 -
      3 * t ^ 7 - 4 * t ^ 6 + 7 * t ^ 5 - 6 * t ^ 4 - 7 * t ^ 3 + 4 * t ^ 2 - 9 * t - 10)
      (by push_cast; ring)
    rcases h3 3 this with h | h
    · exact h
    · exact (Nat.prime_dvd_prime_iff_eq hu Nat.prime_three).mp h
  · -- `j = 5`, `C = 12`
    left
    have := key (4 * (3 * 1)) (-(t : ℤ) ^ 4 - t ^ 3 - t ^ 2 - t + 5) ((t : ℤ) ^ 9 + 2 * t ^ 8 +
      3 * t ^ 7 + 4 * t ^ 6 - t ^ 5 + t ^ 3 + 2 * t ^ 2 + 3 * t - 2) (by push_cast; ring)
    rcases h3 1 this with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd one_pos h) (by have := hu.two_le; omega)
  · -- `j = 7`, `C = 516 = 4 * 3 * 43`
    have := key (4 * (3 * 43)) (-35 * (t : ℤ) ^ 6 - 11 * t ^ 5 + 85 * t ^ 4 - 47 * t ^ 3 -
      59 * t ^ 2 - 107 * t + 217) (35 * (t : ℤ) ^ 9 + 46 * t ^ 8 - 39 * t ^ 7 + 8 * t ^ 6 +
      67 * t ^ 5 + 174 * t ^ 4 - 43 * t ^ 3 - 8 * t ^ 2 + 3 * t - 82) (by push_cast; ring)
    rcases h3 43 this with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, (Nat.prime_dvd_prime_iff_eq hu (by norm_num)).mp h⟩)
  · -- `j = 9`, `C = 2052 = 4 * 3 * 171`, `171 = 9 * 19`
    have := key (4 * (3 * 171)) (-53 * (t : ℤ) ^ 8 - 65 * t ^ 7 - 41 * t ^ 6 - 89 * t ^ 5 +
      7 * t ^ 4 - 185 * t ^ 3 + 199 * t ^ 2 - 569 * t + 967) (53 * (t : ℤ) ^ 9 + 118 * t ^ 8 +
      159 * t ^ 7 + 248 * t ^ 6 + 241 * t ^ 5 + 426 * t ^ 4 + 227 * t ^ 3 + 796 * t ^ 2 -
      171 * t - 118) (by push_cast; ring)
    rcases h3 171 this with h | h
    · exact Or.inl h
    · have h' : u ∣ 3 * (3 * 19) := h
      rcases (Nat.Prime.dvd_mul hu).mp h' with h1 | h1
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_three).mp h1)
      rcases (Nat.Prime.dvd_mul hu).mp h1 with h2 | h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_three).mp h2)
      · exact Or.inr (Or.inr ⟨rfl, (Nat.prime_dvd_prime_iff_eq hu (by norm_num)).mp h2⟩)

/-- **`σ(p ^ f)` modulo `p ^ 3`.** For a prime `p` and `f ≥ 2`,
`σ(p ^ f) ≡ 1 + p + p ^ 2 (mod p ^ 3)`. -/
theorem sigma_prime_pow_mod_cube {p f : ℕ} (hp : p.Prime) (hf : 2 ≤ f) :
    σ 1 (p ^ f) % p ^ 3 = (1 + p + p ^ 2) % p ^ 3 := by
  rw [sigma_one_apply_prime_pow hp]
  have : ∀ n, 3 ≤ n → (∑ i ∈ Finset.range n, p ^ i) % p ^ 3 = (1 + p + p ^ 2) % p ^ 3 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, pow_zero, pow_one, zero_add]
    | succ n hn ih =>
      rw [Finset.sum_range_succ, Nat.add_mod (∑ i ∈ Finset.range n, p ^ i), ih,
        Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow p hn), add_zero, Nat.mod_mod]
  exact this (f + 1) (by omega)

/-- **The prime `3` as receiver.** If `t ^ j ≡ 13 (mod 27)` with `j` odd and `j < 10`, then
`j = 1`, `t ≡ 13`, `F(t) ≡ 24`, or `j = 5`, `t ≡ 7`, `F(t) ≡ 18`, or `j = 7`, `t ≡ 22`,
`F(t) ≡ 6`, all modulo `27`. In particular `j ≠ 3, 9`. -/
theorem pairTen_three_mod27 {t j : ℕ} (ht : t ^ j % 27 = 13) (hj : Odd j) (hj10 : j < 10) :
    (j = 1 ∧ t % 27 = 13 ∧
        (t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2) % 27 =
          24) ∨
      (j = 5 ∧ t % 27 = 7 ∧
        (t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2) % 27 =
          18) ∨
      (j = 7 ∧ t % 27 = 22 ∧
        (t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2) % 27 =
          6) := by
  have tab : ∀ a < 27, ∀ i < 10, i % 2 = 1 → a ^ i % 27 = 13 →
      (i = 1 ∧ a = 13 ∧ F a % 27 = 24) ∨ (i = 5 ∧ a = 7 ∧ F a % 27 = 18) ∨
        (i = 7 ∧ a = 22 ∧ F a % 27 = 6) := by
    refine @of_decide_eq_true _ (@Nat.decidableBallLT 27 _ fun _ _ =>
      @Nat.decidableBallLT 10 _ fun _ _ => inferInstance) ?_
    decide +kernel
  have h := tab (t % 27) (Nat.mod_lt _ (by norm_num)) j hj10 (Nat.odd_iff.mp hj)
    (by rw [← Nat.pow_mod]; exact ht)
  rw [F_mod] at h
  exact h

/-- **The prime `43` as receiver: the lifts.** If `t ^ 7 ≡ 1893 (mod 43 ^ 3)` and
`43 ∣ F(t)`, then `t ≡ 59344 (mod 43 ^ 3)` and `F(t) ≡ 35 * 43 ^ 2 (mod 43 ^ 3)`. Proved by
lifting `t mod 43`, `t mod 43 ^ 2`, `t mod 43 ^ 3` in turn. -/
theorem pairTen_fortythree_lift {t : ℕ} (ht : t ^ 7 % 79507 = 1893)
    (hF : 43 ∣ t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2) :
    t % 79507 = 59344 ∧
      (t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2) %
        79507 = 35 * 43 ^ 2 := by
  have hF' : F t % 43 = 0 := Nat.mod_eq_zero_of_dvd hF
  -- first lift: `t mod 43`
  have l1 : ∀ a < 43, a ^ 7 % 43 = 1 → F a % 43 = 0 → a = 4 := by decide +kernel
  have h43 : t % 43 = 4 := by
    refine l1 (t % 43) (Nat.mod_lt _ (by norm_num)) ?_ (by rw [F_mod]; exact hF')
    rw [← Nat.pow_mod, ← Nat.mod_mod_of_dvd (t ^ 7) (show 43 ∣ 79507 by norm_num), ht]
  -- second lift: `t mod 43 ^ 2`
  have l2 : ∀ k < 43, (4 + 43 * k) ^ 7 % 1849 = 44 → k = 4 := by decide +kernel
  have h1849 : t % 1849 = 176 := by
    have e1 : t % 1849 % 43 = 4 := by
      rw [Nat.mod_mod_of_dvd t (show 43 ∣ 1849 by norm_num)]; exact h43
    have e2 := Nat.div_add_mod (t % 1849) 43
    have e3 : t % 1849 / 43 < 43 := by omega
    have e4 : (t % 1849) ^ 7 % 1849 = 44 := by
      rw [← Nat.pow_mod, ← Nat.mod_mod_of_dvd (t ^ 7) (show 1849 ∣ 79507 by norm_num), ht]
    rw [e1] at e2
    have := l2 (t % 1849 / 43) e3 (by rw [add_comm, e2]; exact e4)
    omega
  -- third lift: `t mod 43 ^ 3`
  have l3 : ∀ k < 43, (176 + 1849 * k) ^ 7 % 79507 = 1893 → k = 32 := by decide +kernel
  have hc : t % 79507 = 59344 := by
    have e1 : t % 79507 % 1849 = 176 := by
      rw [Nat.mod_mod_of_dvd t (show 1849 ∣ 79507 by norm_num)]; exact h1849
    have e2 := Nat.div_add_mod (t % 79507) 1849
    have e3 : t % 79507 / 1849 < 43 := by omega
    have e4 : (t % 79507) ^ 7 % 79507 = 1893 := by rw [← Nat.pow_mod]; exact ht
    rw [e1] at e2
    have := l3 (t % 79507 / 1849) e3 (by rw [add_comm, e2]; exact e4)
    omega
  refine ⟨hc, ?_⟩
  change F t % 79507 = 35 * 43 ^ 2
  rw [← F_mod, hc]
  decide +kernel

/-- **The prime `43` as receiver: no square cofactor.** Under the hypotheses of
`pairTen_fortythree_lift`, `F(t) = 2 * 43 ^ d * w ^ 2` with `43 ∤ w` is impossible. -/
theorem pairTen_fortythree_not {t d w : ℕ} (ht : t ^ 7 % 79507 = 1893)
    (hF : 43 ∣ t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2)
    (hw : ¬ 43 ∣ w)
    (hd : t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2 =
      2 * 43 ^ d * w ^ 2) : False := by
  have hm := (pairTen_fortythree_lift ht hF).2
  rw [hd] at hm
  have hw2 : ¬ 43 ∣ w ^ 2 := fun h => hw ((by norm_num : Nat.Prime 43).dvd_of_dvd_pow h)
  have hW : w ^ 2 % 43 ≠ 0 := fun h => hw2 (Nat.dvd_of_mod_eq_zero h)
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d by omega) with rfl | rfl | rfl | h3
  · norm_num at hm; omega
  · norm_num at hm; omega
  · have h39 : w ^ 2 % 43 = 39 := by norm_num at hm; omega
    have tab : ∀ a < 43, a ^ 2 % 43 ≠ 39 := by decide +kernel
    exact tab (w % 43) (Nat.mod_lt _ (by norm_num)) (by rw [← Nat.pow_mod]; exact h39)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h3
    rw [pow_add] at hm
    have : 2 * (43 ^ 3 * 43 ^ k) * w ^ 2 = 79507 * (2 * 43 ^ k * w ^ 2) := by ring
    rw [this, Nat.mul_mod_right] at hm
    norm_num at hm

namespace EulerIndexPairTenArith

/-- Reduction of an exponent modulo `n` when `a ^ n ≡ 1 (mod p)`. -/
private lemma pow_mod_of_pow_eq_one {a n p : ℕ} (hp : 1 < p) (h : a ^ n % p = 1) (x : ℕ) :
    a ^ x % p = a ^ (x % n) % p := by
  have h1 : (a ^ n) ^ (x / n) % p = 1 := by
    rw [Nat.pow_mod, h, one_pow, Nat.mod_eq_of_lt hp]
  calc a ^ x % p = ((a ^ n) ^ (x / n) * a ^ (x % n)) % p := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ = a ^ (x % n) % p := by rw [Nat.mul_mod, h1, one_mul, Nat.mod_mod]

/-- The small prime step for one modulus `p`, from kernel checked tables. -/
private lemma small_gen (p : ℕ) (hp1 : 1 < p) (hev : (p - 1) % 2 = 0)
    (hferm : ∀ a < p, 0 < a → a ^ (p - 1) % p = 1)
    (htab : ∀ a < p, ∀ r < p - 1, r % 2 = 1 → a ^ r % p = 1 → F a % p = 0 → p = 19 ∧ a = 17)
    {t x : ℕ} (hx : x % 2 = 1) (ht : t ^ x % p = 1) (hF : p ∣ F t) :
    p = 19 ∧ t % p = 17 := by
  have ht' : (t % p) ^ x % p = 1 := by rw [← Nat.pow_mod]; exact ht
  have ha : 0 < t % p := by
    rcases Nat.eq_zero_or_pos (t % p) with h0 | h0
    · rw [h0, zero_pow (by omega), Nat.zero_mod] at ht'; exact absurd ht' (by norm_num)
    · exact h0
  rw [pow_mod_of_pow_eq_one hp1 (hferm _ (Nat.mod_lt _ (by omega)) ha)] at ht'
  exact htab (t % p) (Nat.mod_lt _ (by omega)) (x % (p - 1)) (Nat.mod_lt _ (by omega))
    (by rw [Nat.mod_mod_of_dvd x (Nat.dvd_of_mod_eq_zero hev)]; exact hx) ht'
    (by rw [F_mod]; exact Nat.mod_eq_zero_of_dvd hF)

end EulerIndexPairTenArith

/-- **Small primes.** For `p ∈ {5, 7, 11, 13, 17, 19}`, an odd `x` with `t ^ x ≡ 1 (mod p)`
and `p ∣ F(t)` force `p = 19` and `t ≡ 17 (mod 19)`. Restricted result; novelty not
verified. -/
theorem pairTen_small_prime {p t x : ℕ}
    (hp : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) (hx : Odd x)
    (ht : t ^ x % p = 1)
    (hF : p ∣ t ^ 10 + t ^ 9 + t ^ 8 + t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2) :
    p = 19 ∧ t % 19 = 17 := by
  have hx' := Nat.odd_iff.mp hx
  have key : p = 19 ∧ t % p = 17 := by
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · refine small_gen 5 (by norm_num) (by norm_num) (by decide +kernel) ?_ hx' ht hF
      refine @of_decide_eq_true _ (@Nat.decidableBallLT _ _ fun _ _ =>
        @Nat.decidableBallLT _ _ fun _ _ => inferInstance) ?_
      decide +kernel
    · refine small_gen 7 (by norm_num) (by norm_num) (by decide +kernel) ?_ hx' ht hF
      refine @of_decide_eq_true _ (@Nat.decidableBallLT _ _ fun _ _ =>
        @Nat.decidableBallLT _ _ fun _ _ => inferInstance) ?_
      decide +kernel
    · refine small_gen 11 (by norm_num) (by norm_num) (by decide +kernel) ?_ hx' ht hF
      refine @of_decide_eq_true _ (@Nat.decidableBallLT _ _ fun _ _ =>
        @Nat.decidableBallLT _ _ fun _ _ => inferInstance) ?_
      decide +kernel
    · refine small_gen 13 (by norm_num) (by norm_num) (by decide +kernel) ?_ hx' ht hF
      refine @of_decide_eq_true _ (@Nat.decidableBallLT _ _ fun _ _ =>
        @Nat.decidableBallLT _ _ fun _ _ => inferInstance) ?_
      decide +kernel
    · refine small_gen 17 (by norm_num) (by norm_num) (by decide +kernel) ?_ hx' ht hF
      refine @of_decide_eq_true _ (@Nat.decidableBallLT _ _ fun _ _ =>
        @Nat.decidableBallLT _ _ fun _ _ => inferInstance) ?_
      decide +kernel
    · refine small_gen 19 (by norm_num) (by norm_num) (by decide +kernel) ?_ hx' ht hF
      refine @of_decide_eq_true _ (@Nat.decidableBallLT _ _ fun _ _ =>
        @Nat.decidableBallLT _ _ fun _ _ => inferInstance) ?_
      decide +kernel
  obtain ⟨rfl, h⟩ := key
  exact ⟨rfl, h⟩

/-- **The residue `17 (mod 19)` against a power of `3`.** If `t ≡ 17 (mod 19)` then
`2 t + 1` is not an odd power of `3`. -/
theorem pairTen_nineteen_not {t n : ℕ} (ht : t % 19 = 17) (hn : Odd n) (h : 2 * t + 1 = 3 ^ n) :
    False := by
  have h1 : 3 ^ n % 19 = 3 ^ (n % 18) % 19 :=
    pow_mod_of_pow_eq_one (by norm_num) (by norm_num) n
  have tab : ∀ r < 18, r % 2 = 1 → 3 ^ r % 19 ≠ 16 := by decide +kernel
  have hn' := Nat.odd_iff.mp hn
  apply tab (n % 18) (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [← h1, ← h]
  omega

/-- **Three rows of length `3`.** `R_3(7) = 3 * 19`, `R_3(13) = 3 * 61`, `R_3(19) = 3 * 127`,
and none of `19, 61, 127` is `4 (mod 9)`. -/
theorem pairTen_three_rows :
    7 ^ 2 + 7 + 1 = 3 * 19 ∧ 13 ^ 2 + 13 + 1 = 3 * 61 ∧ 19 ^ 2 + 19 + 1 = 3 * 127 ∧
      19 % 9 ≠ 4 ∧ 61 % 9 ≠ 4 ∧ 127 % 9 ≠ 4 := by
  norm_num

/-- **Abundancy envelope.** `(3 / 2) * ∏ p / (p - 1) < 2` over the eleven primes
`23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67`; the value is
`1214635883296783 / 613735170048000`. -/
theorem pairTen_envelope :
    (3 / 2 : ℚ) * (23 / 22) * (29 / 28) * (31 / 30) * (37 / 36) * (41 / 40) * (43 / 42) *
      (47 / 46) * (53 / 52) * (59 / 58) * (61 / 60) * (67 / 66) < 2 := by
  norm_num

end OddPerfect

#print axioms OddPerfect.pairTen_receiver_cases
#print axioms OddPerfect.sigma_prime_pow_mod_cube
#print axioms OddPerfect.pairTen_three_mod27
#print axioms OddPerfect.pairTen_fortythree_lift
#print axioms OddPerfect.pairTen_fortythree_not
#print axioms OddPerfect.pairTen_small_prime
#print axioms OddPerfect.pairTen_nineteen_not
#print axioms OddPerfect.pairTen_three_rows
#print axioms OddPerfect.pairTen_envelope
