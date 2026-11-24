import OddPerfect.EscapeRowUnique
import Mathlib.NumberTheory.FLT.Three

/-!
# Three parts of the equation `x ^ 2 + x + 1 = 3 * y ^ n`

These are three parts of the classical theorem that `x ^ 2 + x + 1 = 3 * y ^ n` has no solution
with `x ≥ 2` and `n ≥ 3` (Nagell; Ljunggren).

* `not_phi3_eq_three_mul_cube`: the cube case. It uses mathlib's Fermat theorem for exponent 3.
* `eq_one_of_four_mul_pow_four` and `not_phi3_eq_three_mul_pow_four`: the fourth power case, by
  an elementary descent with coprime factors.
* `eis_not_pow_add_twist`: for exponents `n ≥ 5` prime to 6, the Eisenstein integer equation
  `β ^ n + ω ^ 2 * (star β) ^ n = -ω` has no solution when a prime of norm at least 5 divides
  `β`. The proof compares the exponent of that prime in the binomial expansion.

The value `Φ₃(313) = 3 * 181 ^ 2` shows that the exponent 2 occurs. This is known mathematics and
decides nothing about odd perfect numbers.
-/

open Finset QuadraticAlgebra

namespace OddPerfect

/-! ### The cube case -/

/-- `x ^ 2 + x + 1 = 3 * y ^ 3` has no solution with `x ≥ 2`. -/
theorem not_phi3_eq_three_mul_cube {x y : ℕ} (hx : 2 ≤ x) : x ^ 2 + x + 1 ≠ 3 * y ^ 3 := by
  intro h
  rcases (show x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 by omega) with h3 | h3 | h3
  · obtain ⟨b, rfl⟩ : ∃ b, x = 3 * b := ⟨x / 3, by omega⟩
    have e : (3 * b) ^ 2 + 3 * b + 1 = 3 * (3 * b ^ 2 + b) + 1 := by ring
    omega
  · obtain ⟨b, rfl⟩ : ∃ b, x = 3 * b + 1 := ⟨x / 3, by omega⟩
    have e : (3 * b + 1) ^ 2 + (3 * b + 1) + 1 = 3 * (3 * b ^ 2 + 3 * b + 1) := by ring
    have hy : y ^ 3 = 3 * b ^ 2 + 3 * b + 1 := by omega
    have hb : b ≠ 0 := by omega
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hy
      omega
    exact fermatLastTheoremThree y b (b + 1) hy0 hb (by omega) (by rw [hy]; ring)
  · obtain ⟨b, rfl⟩ : ∃ b, x = 3 * b + 2 := ⟨x / 3, by omega⟩
    have e : (3 * b + 2) ^ 2 + (3 * b + 2) + 1 = 3 * (3 * b ^ 2 + 5 * b + 2) + 1 := by ring
    omega

/-! ### The fourth power case -/

/-- Coprimality of an odd number with a number when every common divisor divides a power of 2. -/
private theorem cop_of_dvd_two_pow {m n c : ℕ} (hm : m % 2 = 1)
    (h : ∀ k, k ∣ m → k ∣ n → k ∣ 2 ^ c) : Nat.Coprime m n :=
  Nat.coprime_of_dvd fun k hk h1 h2 => by
    have h2k := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).1 (hk.dvd_of_dvd_pow (h k h1 h2))
    subst h2k
    omega

/-- Coprime factors of a square are squares. -/
private theorem sq_of_cop {a b c : ℕ} (h : Nat.Coprime a b) (e : a * b = c ^ 2) :
    ∃ d, a = d ^ 2 :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.2 h) e

/-- Coprime factors of three times a square, the first prime to 3. -/
private theorem split_three {P Q w : ℕ} (hc : Nat.Coprime P Q) (h3 : ¬ 3 ∣ P)
    (e : P * Q = 3 * w ^ 2) : ∃ b a, P = b ^ 2 ∧ Q = 3 * a ^ 2 := by
  have hQ : 3 ∣ Q :=
    ((Nat.Prime.dvd_mul Nat.prime_three).1 ⟨w ^ 2, e⟩).resolve_left h3
  obtain ⟨Q', rfl⟩ := hQ
  have e' : P * Q' = w ^ 2 := by
    have : 3 * (P * Q') = 3 * w ^ 2 := by rw [← e]; ring
    omega
  have hc' : Nat.Coprime P Q' := Nat.Coprime.coprime_dvd_right (dvd_mul_left Q' 3) hc
  obtain ⟨b, hb⟩ := sq_of_cop hc' e'
  obtain ⟨a, ha⟩ := sq_of_cop hc'.symm (by rw [mul_comm]; exact e')
  exact ⟨b, a, hb, by rw [ha]⟩

/-- The last step of the descent: odd `a`, `b` with
`(b ^ 2 + 3 a ^ 2) ^ 2 - 2 (b ^ 2 - 3 a ^ 2) ^ 2 = 8` have `b ^ 2 + 3 a ^ 2 = 4`. -/
private theorem descent_end {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (e : ((b : ℤ) ^ 2 + 3 * a ^ 2) ^ 2 - 2 * ((b : ℤ) ^ 2 - 3 * a ^ 2) ^ 2 = 8) :
    b ^ 2 + 3 * a ^ 2 = 4 := by
  obtain ⟨s, rfl⟩ : ∃ s, a = 2 * s + 1 := ⟨a / 2, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, b = 2 * t + 1 := ⟨b / 2, by omega⟩
  have key : ((4 * t ^ 2 + 4 * t : ℕ) : ℤ) * ((2 * t ^ 2 + 2 * t + 1 : ℕ) : ℤ) =
      9 * ((s : ℤ) ^ 2 + s - t ^ 2 - t) ^ 2 := by
    have h16 : (16 : ℤ) * (((4 * t ^ 2 + 4 * t : ℕ) : ℤ) * ((2 * t ^ 2 + 2 * t + 1 : ℕ) : ℤ) -
        9 * ((s : ℤ) ^ 2 + s - t ^ 2 - t) ^ 2) = 0 := by
      push_cast at e ⊢
      linear_combination e
    have := mul_eq_zero.1 h16
    rcases this with h0 | h0
    · norm_num at h0
    · linarith
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    have hs : ((s : ℤ) ^ 2 + s - 0 ^ 2 - 0) ^ 2 = 0 := by
      push_cast at key; linarith
    have hs' : (s : ℤ) ^ 2 + s = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hs
      linarith
    have hs0 : s = 0 := by
      have : (s : ℤ) = 0 := by nlinarith [sq_nonneg (s : ℤ), (Nat.cast_nonneg s : (0 : ℤ) ≤ s)]
      exact_mod_cast this
    subst hs0
    norm_num
  · exfalso
    set z : ℤ := (s : ℤ) ^ 2 + s - t ^ 2 - t
    have hNM : (4 * t ^ 2 + 4 * t) * (2 * t ^ 2 + 2 * t + 1) = (3 * z.natAbs) ^ 2 := by
      have h1 : (((4 * t ^ 2 + 4 * t) * (2 * t ^ 2 + 2 * t + 1) : ℕ) : ℤ) =
          (((3 * z.natAbs) ^ 2 : ℕ) : ℤ) := by
        rw [Nat.cast_mul, key, Nat.cast_pow, Nat.cast_mul, Int.natCast_natAbs, mul_pow, sq_abs]
        norm_num
      exact_mod_cast h1
    have hcop : Nat.Coprime (4 * t ^ 2 + 4 * t) (2 * t ^ 2 + 2 * t + 1) := by
      refine Nat.Coprime.symm (cop_of_dvd_two_pow (c := 1) (by omega) fun k h1 h2 => ?_)
      have h3 : k ∣ 2 * (2 * t ^ 2 + 2 * t + 1) := dvd_mul_of_dvd_right h1 2
      rw [show 2 * (2 * t ^ 2 + 2 * t + 1) = (4 * t ^ 2 + 4 * t) + 2 by ring] at h3
      rw [pow_one]
      exact (Nat.dvd_add_right h2).1 h3
    obtain ⟨c, hc⟩ := sq_of_cop hcop hNM
    rcases le_or_gt c (2 * t) with h | h
    · have : c ^ 2 ≤ (2 * t) ^ 2 := Nat.pow_le_pow_left h 2
      nlinarith
    · have : (2 * t + 1) ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left h 2
      nlinarith

/-- `4 * Y ^ 4 = 3 * u ^ 2 + 1` forces `Y = 1`. -/
theorem eq_one_of_four_mul_pow_four {Y u : ℕ} (h : 4 * Y ^ 4 = 3 * u ^ 2 + 1) : Y = 1 := by
  have hY : 1 ≤ Y := by
    rcases Nat.eq_zero_or_pos Y with h0 | h0
    · subst h0
      rw [zero_pow (by norm_num), mul_zero] at h
      omega
    · exact h0
  have hY2 : 1 ≤ Y ^ 2 := Nat.one_le_pow 2 Y hY
  obtain ⟨A, hA⟩ : ∃ A, 2 * Y ^ 2 = A + 1 := ⟨2 * Y ^ 2 - 1, by omega⟩
  have hAB : A * (A + 2) = 3 * u ^ 2 := by
    have e1 : (A + 1) ^ 2 = 3 * u ^ 2 + 1 := by rw [← hA, ← h]; ring
    have e2 : (A + 1) ^ 2 = A * (A + 2) + 1 := by ring
    omega
  have hA3 : ¬ 3 ∣ A := by
    intro h3
    have : Y ^ 2 % 3 ≠ 2 := by
      rw [Nat.pow_mod]
      have := Nat.mod_lt Y (show 3 > 0 by norm_num)
      interval_cases Y % 3 <;> norm_num
    omega
  have hcopA : Nat.Coprime A (A + 2) :=
    cop_of_dvd_two_pow (c := 1) (by omega) fun k h1 h2 => by
      rw [pow_one]; exact (Nat.dvd_add_right h1).1 h2
  obtain ⟨v, w, hv, hw⟩ := split_three hcopA hA3 hAB
  subst hv
  have hv2 : v < 2 * Y := by
    by_contra hc
    have : (2 * Y) ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left (not_lt.1 hc) 2
    nlinarith
  obtain ⟨P, hP⟩ : ∃ P, P + v = 2 * Y := ⟨2 * Y - v, by omega⟩
  have hPQ : P * (P + 2 * v) = 3 * w ^ 2 := by
    have e1 : P * (P + 2 * v) + v ^ 2 = (P + v) ^ 2 := by ring
    have e2 : (P + v) ^ 2 = 4 * Y ^ 2 := by rw [hP]; ring
    omega
  have hPodd : P % 2 = 1 := by
    have : (P * (P + 2 * v)) % 2 = 1 := by omega
    rcases Nat.even_or_odd P with hp | hp
    · obtain ⟨r, rfl⟩ := hp
      have : (r + r) * (r + r + 2 * v) = 2 * (r * (r + r + 2 * v)) := by ring
      omega
    · obtain ⟨r, rfl⟩ := hp
      omega
  have hrel : P ^ 2 + (P + 2 * v) ^ 2 + 8 = 6 * (P * (P + 2 * v)) := by
    have e : P ^ 2 + (P + 2 * v) ^ 2 + 8 = 2 * (P * (P + 2 * v)) + 4 * (v ^ 2 + 2) := by ring
    omega
  have hcop : Nat.Coprime P (P + 2 * v) :=
    cop_of_dvd_two_pow (c := 3) hPodd fun k h1 h2 => by
      have h6 : k ∣ 6 * (P * (P + 2 * v)) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h1 _) 6
      rw [← hrel] at h6
      have h7 : k ∣ P ^ 2 + (P + 2 * v) ^ 2 :=
        dvd_add (dvd_pow h1 two_ne_zero) (dvd_pow h2 two_ne_zero)
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
      exact (Nat.dvd_add_right h7).1 h6
  have hE : (((P : ℤ) + (P + 2 * v)) ^ 2 - 2 * ((P : ℤ) - (P + 2 * v)) ^ 2) = 8 := by
    have hP' : (P : ℤ) + v = 2 * Y := by exact_mod_cast hP
    have hA' : (v : ℤ) ^ 2 + 1 = 2 * Y ^ 2 := by exact_mod_cast hA.symm
    linear_combination 4 * ((P : ℤ) + v + 2 * Y) * hP' - 8 * hA'
  have hsum : ∀ a b : ℕ, a % 2 = 1 → b % 2 = 1 →
      ((b : ℤ) ^ 2 + 3 * a ^ 2) ^ 2 - 2 * ((b : ℤ) ^ 2 - 3 * a ^ 2) ^ 2 = 8 →
      P + (P + 2 * v) = b ^ 2 + 3 * a ^ 2 → Y = 1 := by
    intro a b ha hb e hs
    have := descent_end ha hb e
    omega
  have hodd_sq : ∀ b : ℕ, (b ^ 2) % 2 = 1 → b % 2 = 1 := by
    intro b hb
    rcases Nat.even_or_odd b with hp | hp
    · obtain ⟨r, rfl⟩ := hp
      have : (r + r) ^ 2 = 2 * (2 * r ^ 2) := by ring
      omega
    · obtain ⟨r, rfl⟩ := hp
      omega
  by_cases h3P : 3 ∣ P
  · have h3Q : ¬ 3 ∣ P + 2 * v := fun h3 => by
      have := Nat.dvd_gcd h3P h3
      rw [hcop.gcd_eq_one] at this
      omega
    obtain ⟨b, a, hb, ha⟩ := split_three hcop.symm h3Q (by rw [mul_comm]; exact hPQ)
    have hbo : b % 2 = 1 := hodd_sq b (by omega)
    have hao : a % 2 = 1 := hodd_sq a (by omega)
    refine hsum a b hao hbo ?_ (by omega)
    have hb' : ((P : ℤ) + 2 * v) = (b : ℤ) ^ 2 := by exact_mod_cast hb
    have ha' : (P : ℤ) = 3 * (a : ℤ) ^ 2 := by exact_mod_cast ha
    rw [← hb', ← ha']
    linear_combination hE
  · obtain ⟨b, a, hb, ha⟩ := split_three hcop h3P hPQ
    have hbo : b % 2 = 1 := hodd_sq b (by omega)
    have hao : a % 2 = 1 := hodd_sq a (by omega)
    refine hsum a b hao hbo ?_ (by omega)
    have hb' : (P : ℤ) = (b : ℤ) ^ 2 := by exact_mod_cast hb
    have ha' : ((P : ℤ) + 2 * v) = 3 * (a : ℤ) ^ 2 := by exact_mod_cast ha
    rw [← hb', ← ha']
    linear_combination hE

/-- `x ^ 2 + x + 1 = 3 * Y ^ 4` has no solution with `x ≥ 2`. -/
theorem not_phi3_eq_three_mul_pow_four {x Y : ℕ} (hx : 2 ≤ x) : x ^ 2 + x + 1 ≠ 3 * Y ^ 4 := by
  intro h
  have e0 : (2 * x + 1) ^ 2 + 3 = 4 * (x ^ 2 + x + 1) := by ring
  rw [h] at e0
  have h3 : 3 ∣ (2 * x + 1) ^ 2 := by omega
  obtain ⟨u, hu⟩ := Nat.prime_three.dvd_of_dvd_pow h3
  have e1 : 4 * Y ^ 4 = 3 * u ^ 2 + 1 := by
    rw [hu] at e0
    have : (3 * u) ^ 2 = 9 * u ^ 2 := by ring
    omega
  have hY := eq_one_of_four_mul_pow_four e1
  subst hY
  nlinarith

/-! ### Exponents prime to 6 -/

private theorem nrm_pow (z : Eis) (m : ℕ) : Eis.nrm (z ^ m) = Eis.nrm z ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Eis.nrm_one]
  | succ m ih => rw [pow_succ, pow_succ, Eis.nrm_mul, ih]

private theorem sq_lt_five_pow (m : ℕ) : (m + 1 + 1) ^ 2 < 5 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ 5 (m + 1)]
    nlinarith

/-- A power `ρ ^ m` with `5 ^ m > j ^ 2` does not divide the integer `j`. -/
private theorem not_pow_dvd_natCast {ρ : Eis} (hρn : 5 ≤ Eis.nrm ρ) {j m : ℕ} (hj : 0 < j)
    (hjm : j ^ 2 < 5 ^ m) : ¬ ρ ^ m ∣ (j : Eis) := by
  rintro ⟨c, hc⟩
  have e := congrArg Eis.nrm hc
  rw [← Int.cast_natCast (R := Eis) j, Eis.nrm_intCast, Eis.nrm_mul,
    nrm_pow] at e
  have hj' : (0 : ℤ) < (j : ℤ) ^ 2 := by positivity
  have h5 : (5 : ℤ) ^ m ≤ Eis.nrm ρ ^ m := pow_le_pow_left₀ (by norm_num) hρn m
  have hjm' : (j : ℤ) ^ 2 < 5 ^ m := by exact_mod_cast hjm
  have hc0 := Eis.nrm_nonneg c
  have hp0 : 0 ≤ Eis.nrm ρ ^ m := pow_nonneg (Eis.nrm_nonneg ρ) m
  rcases hc0.eq_or_lt with h0 | h0
  · rw [← h0, mul_zero] at e; linarith
  · have h1 : 1 ≤ Eis.nrm c := by omega
    nlinarith

/-- If `ρ ^ (a + b) ∣ x * y` and `ρ ^ b ∤ x` for a prime `ρ`, then `ρ ^ (a + 1) ∣ y`. -/
private theorem pow_dvd_of_pow_add_dvd_mul {ρ : Eis} (hρ : Prime ρ) (a : ℕ) :
    ∀ (b : ℕ) {x y : Eis}, ρ ^ (a + b) ∣ x * y → ¬ ρ ^ b ∣ x → ρ ^ (a + 1) ∣ y := by
  intro b
  induction b with
  | zero => intro x y _ hx; exact (hx (by rw [pow_zero]; exact one_dvd x)).elim
  | succ b ih =>
    intro x y h hx
    by_cases hρx : ρ ∣ x
    · obtain ⟨x', rfl⟩ := hρx
      have h' : ρ ^ (a + b) ∣ x' * y := by
        have : ρ * ρ ^ (a + b) ∣ ρ * (x' * y) := by
          rw [← pow_succ', ← mul_assoc]; exact h
        exact (mul_dvd_mul_iff_left hρ.ne_zero).1 this
      exact ih h' fun hb => hx (by rw [pow_succ']; exact mul_dvd_mul_left ρ hb)
    · exact (pow_dvd_pow ρ (by omega)).trans (hρ.pow_dvd_of_dvd_mul_left _ hρx h)

/-- If `(1 + γ) ^ n = 1 + γ ^ n` with `n ≥ 2` and `γ ≠ 0`, no prime of norm at least 5
divides `γ`. -/
private theorem binom_core {γ ρ : Eis} {n : ℕ} (hn : 2 ≤ n) (hρ : Prime ρ)
    (hρn : 5 ≤ Eis.nrm ρ) (hd : ρ ∣ γ) (hγ : γ ≠ 0) (h : (1 + γ) ^ n = 1 + γ ^ n) : False := by
  classical
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 + 1 := ⟨n - 2, by omega⟩
  have hex : ∃ k, ¬ ρ ^ k ∣ ((N + 1 + 1 : ℕ) : Eis) :=
    ⟨N + 1 + 1, not_pow_dvd_natCast hρn (by omega)
      ((sq_lt_five_pow N).trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))⟩
  have hk1 : ¬ ρ ^ (Nat.find hex) ∣ ((N + 1 + 1 : ℕ) : Eis) := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := fun h0 => hk1 (by rw [h0, pow_zero]; exact one_dvd _)
  obtain ⟨V, hV⟩ : ∃ V, Nat.find hex = V + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hVd : ρ ^ V ∣ ((N + 1 + 1 : ℕ) : Eis) :=
    not_not.1 (Nat.find_min hex (by omega : V < Nat.find hex))
  rw [hV] at hk1
  have e2 : ((N + 1 + 1 : ℕ) : Eis) * γ = -(∑ m ∈ range N,
      γ ^ (m + 1 + 1) * 1 ^ (N + 1 + 1 - (m + 1 + 1)) *
        ((N + 1 + 1).choose (m + 1 + 1) : Eis)) := by
    have e := add_pow γ 1 (N + 1 + 1)
    rw [add_comm γ 1, h, sum_range_succ, sum_range_succ', sum_range_succ'] at e
    have f1 : γ ^ (0 + 1) * 1 ^ (N + 1 + 1 - (0 + 1)) * ((N + 1 + 1).choose (0 + 1) : Eis) =
        ((N + 1 + 1 : ℕ) : Eis) * γ := by
      rw [zero_add, pow_one, one_pow, mul_one, Nat.choose_one_right, mul_comm]
    have f0 : γ ^ 0 * 1 ^ (N + 1 + 1 - 0) * ((N + 1 + 1).choose 0 : Eis) = 1 := by
      rw [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, one_mul]
    have fN : γ ^ (N + 1 + 1) * 1 ^ (N + 1 + 1 - (N + 1 + 1)) *
        ((N + 1 + 1).choose (N + 1 + 1) : Eis) = γ ^ (N + 1 + 1) := by
      rw [one_pow, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
    rw [f1, f0, fN] at e
    linear_combination (-1 : Eis) * e
  have key : ∀ m : ℕ, ρ ^ (V + 1) ∣ γ ^ (m + 1) * ((N + 1 + 1).choose (m + 1 + 1) : Eis) := by
    intro m
    have hx : ¬ ρ ^ (m + 1) ∣ ((m + 1 + 1 : ℕ) : Eis) :=
      not_pow_dvd_natCast hρn (by omega) (sq_lt_five_pow m)
    refine pow_dvd_of_pow_add_dvd_mul hρ V (m + 1) ?_ hx
    have hc : ((m + 1 + 1 : ℕ) : Eis) * ((N + 1 + 1).choose (m + 1 + 1) : Eis) =
        ((N + 1 + 1 : ℕ) : Eis) * ((N + 1).choose (m + 1) : Eis) := by
      have hn : (m + 1 + 1) * (N + 1 + 1).choose (m + 1 + 1) =
          (N + 1 + 1) * (N + 1).choose (m + 1) := by
        rw [mul_comm]; exact (Nat.add_one_mul_choose_eq (N + 1) (m + 1)).symm
      exact_mod_cast hn
    rw [pow_add, show ((m + 1 + 1 : ℕ) : Eis) * (γ ^ (m + 1) *
        ((N + 1 + 1).choose (m + 1 + 1) : Eis)) =
        (((N + 1 + 1 : ℕ) : Eis) * ((N + 1).choose (m + 1) : Eis)) * γ ^ (m + 1) by
      rw [← hc]; ring]
    exact mul_dvd_mul (dvd_mul_of_dvd_left hVd _) (pow_dvd_pow_of_dvd hd _)
  have hT : ρ ^ (V + 1) * γ ∣ ((N + 1 + 1 : ℕ) : Eis) * γ := by
    rw [e2]
    refine dvd_neg.2 (dvd_sum fun m _ => ?_)
    exact (mul_dvd_mul (key m) (dvd_refl γ)).trans
      (dvd_of_eq (by rw [one_pow, mul_one, pow_succ γ (m + 1)]; ring))
  exact hk1 ((mul_dvd_mul_iff_right hγ).1 hT)

/-- If `β ^ n + δ ^ n = -ω` with `n ≥ 2` odd, no prime of norm at least 5 divides `β ≠ 0`. -/
private theorem pow_add_pow_core {β δ ρ : Eis} {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n)
    (hρ : Prime ρ) (hρn : 5 ≤ Eis.nrm ρ) (hd : ρ ∣ β) (hβ : β ≠ 0)
    (h : β ^ n + δ ^ n = ⟨0, -1⟩) : False := by
  have hω : (⟨0, -1⟩ : Eis) = -⟨0, 1⟩ := by ext <;> simp
  rw [hω] at h
  have hu : IsUnit (-(⟨0, 1⟩ : Eis)) := by
    rw [← hω, Eis.isUnit_iff_nrm_eq_one, Eis.nrm_mk]; norm_num
  have hdv : β + δ ∣ -(⟨0, 1⟩ : Eis) := by rw [← h]; exact hodd.add_dvd_pow_add_pow β δ
  have hεu : IsUnit (β + δ) := isUnit_of_dvd_unit hdv hu
  obtain ⟨ε', hε'⟩ := hεu.exists_right_inv
  have hdiv : β ∣ (β + δ) ^ n + ⟨0, 1⟩ := by
    have h1 : δ - (β + δ) ∣ δ ^ n - (β + δ) ^ n := sub_dvd_pow_sub_pow _ _ n
    rw [show δ - (β + δ) = -β by ring, neg_dvd] at h1
    have h2 : β ∣ β ^ n := dvd_pow_self β (by omega)
    have e : (β + δ) ^ n + ⟨0, 1⟩ = -(β ^ n) - (δ ^ n - (β + δ) ^ n) := by
      linear_combination h
    rw [e]
    exact dvd_sub (dvd_neg.2 h2) h1
  have hεn : (β + δ) ^ n = -⟨0, 1⟩ := by
    obtain ⟨c, hc⟩ := hd.trans hdiv
    have hu1 : Eis.nrm ((β + δ) ^ n) = 1 := (Eis.isUnit_iff_nrm_eq_one _).1 (hεu.pow n)
    have hle : Eis.nrm ((β + δ) ^ n + ⟨0, 1⟩) ≤ 4 := by
      rcases Eis.eq_of_nrm_eq_one hu1 with h' | h' | h' | h' | h' | h' <;> rw [h'] <;>
        norm_num [Eis.nrm]
    by_contra hne
    have hnz : (β + δ) ^ n + ⟨0, 1⟩ ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
    have hpos : 0 < Eis.nrm ((β + δ) ^ n + ⟨0, 1⟩) :=
      lt_of_le_of_ne (Eis.nrm_nonneg _) (fun h0 => hnz ((Eis.nrm_eq_zero _).1 h0.symm))
    rw [hc, Eis.nrm_mul] at hpos hle
    rcases (Eis.nrm_nonneg c).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hpos; exact lt_irrefl _ hpos
    · have h1 : 1 ≤ Eis.nrm c := by omega
      nlinarith
  have hmain : β ^ n + δ ^ n = (β + δ) ^ n := by rw [h, hεn]
  refine binom_core (γ := -(β * ε')) hn hρ hρn (dvd_neg.2 (hd.mul_right ε')) ?_ ?_
  · rw [neg_ne_zero]
    exact mul_ne_zero hβ (right_ne_zero_of_mul_eq_one hε')
  · have e1 : 1 + -(β * ε') = δ * ε' := by linear_combination (-1 : Eis) * hε'
    rw [e1, mul_pow, Odd.neg_pow hodd, mul_pow]
    have e2 : (β + δ) ^ n * ε' ^ n = 1 := by rw [← mul_pow, hε', one_pow]
    linear_combination ε' ^ n * hmain + e2

/-- For `n ≥ 5` with `n % 6 = 1` or `n % 6 = 5`, the equation
`β ^ n + ω ^ 2 * (star β) ^ n = -ω` in the Eisenstein integers has no solution when a prime of
norm at least 5 divides `β`. -/
theorem eis_not_pow_add_twist {β ρ : Eis} {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n % 6 = 1 ∨ n % 6 = 5) (hρ : Prime ρ) (hρn : 5 ≤ Eis.nrm ρ) (hd : ρ ∣ β)
    (h : β ^ n + (⟨-1, -1⟩ : Eis) * (star β) ^ n = ⟨0, -1⟩) : False := by
  have hodd : Odd n := ⟨n / 2, by omega⟩
  have hω3 : (⟨0, 1⟩ : Eis) ^ 3 = 1 := by ext <;> simp [pow_succ]
  have hω2 : (⟨0, 1⟩ : Eis) ^ 2 = ⟨-1, -1⟩ := by ext <;> simp [pow_succ]
  obtain ⟨c, hc⟩ : ∃ c : Eis, c ^ n = ⟨-1, -1⟩ := by
    rcases hn6 with h6 | h6
    · refine ⟨⟨-1, -1⟩, ?_⟩
      rw [← hω2, ← pow_mul, show 2 * n = 3 * (2 * (n / 3)) + 2 by omega, pow_add, pow_mul, hω3,
        one_pow, one_mul]
    · refine ⟨⟨0, 1⟩, ?_⟩
      rw [← hω2, show n = 3 * (n / 3) + 2 by omega, pow_add, pow_mul, hω3, one_pow, one_mul]
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [star_zero, zero_pow (by omega), mul_zero, add_zero] at h
    have := congrArg QuadraticAlgebra.im h
    simp at this
  refine pow_add_pow_core (δ := c * star β) (by omega) hodd hρ hρn hd hβ0 ?_
  rw [mul_pow, hc]
  exact h

end OddPerfect

#print axioms OddPerfect.not_phi3_eq_three_mul_cube
#print axioms OddPerfect.eq_one_of_four_mul_pow_four
#print axioms OddPerfect.not_phi3_eq_three_mul_pow_four
#print axioms OddPerfect.eis_not_pow_add_twist
