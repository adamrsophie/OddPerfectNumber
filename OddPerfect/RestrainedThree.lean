import OddPerfect.RestrainedTwo

/-!
# Restrained odd perfect numbers divisible by 3: the leaf `q = 13, r = 7`

Setting of `restrained_three_sq_cases`: `N` is an odd perfect number with special prime `q`,
`r ≠ q` is a further prime, every other prime factor has exponent exactly 2, and `3^2 ∥ N`.
This file shows that the configuration `q = 13, r = 7` is impossible.

Let `K = {3, 7, 13}` and let `T` be the other prime factors, all exact squares. Split `T` into
`O1` (primes `≡ 1 (mod 3)`) and `O2` (primes `≡ 2 (mod 3)`).

* Each prime of `O1` sends one factor `3` into `σ(N)`, so `|O1| ≤ 2`.
* For `w ∈ T`, every prime factor of `σ(w^2) = phi3 w` is `3`, `7`, `13` or lies in `O1 \ {w}`.
* Every `z ∈ O1` satisfies `z ≥ 10^4`. Otherwise let `m` be `phi3 z / 3` with all factors `7`
  and `13` removed. If `m ≠ 1`, a prime `y ∣ m` lies in `O1`, so `O1 = {z, y}` and
  `m ∈ {y, y^2}` (the exponent of `y` in `σ(z^2)` is at most `v_y(N) = 2`); then `phi3 y / 3` is
  supported on `{7, 13, z}`. An exact kernel check over all `z < 10^4` with `z ≡ 1 (mod 3)`
  refutes this (`kill`), and also excludes `m = 1` for odd `z > 1`.
* Choose distinct primes `x, y ≥ 10^4` with `O1 ⊆ {x, y}`. For `t ∈ O2`,
  `phi3 t = 7^a 13^b x^c y^d`. If `c = d = 0`, an exact check of the values `7^a 13^b` below
  `10^16` shows `phi3 t ≥ 10^16`, and Rankin's trick with exponent `1/4` applies. Otherwise
  `1/(t+1) ≤ 0.378^a 0.2774^b (1/100)^(c+d)`. The tail sum is at most `0.0559`.
* The known components give at most `13/9 · 7/6 · 13/12 < 1.826`, and
  `1.826 / (1 - 0.0559) < 2`.

The exponents of `7` and `13` enter only through the bound `p/(p - 1)`.

Main results: `restrained_not_thirteen_seven` and `restrained_cases_three`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace RestrainedThree

/-! ## Rational helpers -/

/-- `σ(s^2)/s^2` as a rational function of `s`. -/
private def fv (s : ℕ) : ℚ := ((s : ℚ) ^ 2 + s + 1) / s ^ 2

private theorem abundancy_sq {p : ℕ} (hp : p.Prime) : abundancy (p ^ 2) = fv p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [abundancy_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fv]
  field_simp
  ring

private theorem abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy; positivity

private theorem one_le_fv {s : ℕ} (hs : 1 ≤ s) : 1 ≤ fv s := by
  have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
  unfold fv
  rw [le_div_iff₀ (pow_pos (by linarith) 2)]
  nlinarith

private theorem fv_sub_le {s : ℕ} (hs : 10 ≤ s) :
    fv s - 1 ≤ 121 / 100 * (1 / ((s : ℚ) + 1)) := by
  have hs' : (10 : ℚ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℚ) < s := by linarith
  unfold fv
  rw [div_sub_one (pow_pos hs0 2).ne', mul_one_div,
    div_le_div_iff₀ (pow_pos hs0 2) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs') (by positivity : (0 : ℚ) ≤ 21 * s + 10)]

private theorem prod_mul_one_sub_le {ι : Type*} [DecidableEq ι] (T : Finset ι) (x : ι → ℚ)
    (hx : ∀ i ∈ T, 0 ≤ x i) : (∏ i ∈ T, (1 + x i)) * (1 - ∑ i ∈ T, x i) ≤ 1 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have xa := hx a (Finset.mem_insert_self a s)
    have hs := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hP : 0 ≤ ∏ i ∈ s, (1 + x i) :=
      Finset.prod_nonneg fun i hi => by linarith [hx i (Finset.mem_insert_of_mem hi)]
    have hS : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    nlinarith [mul_nonneg hP (add_nonneg (mul_nonneg xa xa) (mul_nonneg xa hS))]

private theorem geom_partial_le {α : ℚ} (h0 : 0 ≤ α) (h1 : α < 1) (K : ℕ) :
    ∑ i ∈ Finset.range K, α ^ i ≤ 1 / (1 - α) := by
  have := geom_sum_Ico_le_of_lt_one (x := α) (m := 0) (n := K) h0 h1
  rwa [← Finset.range_eq_Ico, pow_zero] at this

/-! ## Rankin weights -/

/-- Exponent `1/2`: if `a^i b^j c^k d^l < (t + 1)^2` and every weight satisfies
`α^2 g ≥ 1`, then `1/(t + 1) ≤ α₁^i α₂^j α₃^k α₄^l`. -/
private theorem inv_succ_le {t a b c d i j k l : ℕ} {α₁ α₂ α₃ α₄ : ℚ}
    (h1 : 0 ≤ α₁) (h2 : 0 ≤ α₂) (h3 : 0 ≤ α₃) (h4 : 0 ≤ α₄)
    (g1 : 1 ≤ α₁ ^ 2 * a) (g2 : 1 ≤ α₂ ^ 2 * b) (g3 : 1 ≤ α₃ ^ 2 * c) (g4 : 1 ≤ α₄ ^ 2 * d)
    (hlt : a ^ i * b ^ j * c ^ k * d ^ l < (t + 1) ^ 2) :
    1 / ((t : ℚ) + 1) ≤ α₁ ^ i * α₂ ^ j * α₃ ^ k * α₄ ^ l := by
  set P := α₁ ^ i * α₂ ^ j * α₃ ^ k * α₄ ^ l with hP
  have hP0 : 0 ≤ P := by positivity
  have hPV : 1 ≤ P ^ 2 * ((a ^ i * b ^ j * c ^ k * d ^ l : ℕ) : ℚ) := by
    have e : P ^ 2 * ((a ^ i * b ^ j * c ^ k * d ^ l : ℕ) : ℚ) =
        (α₁ ^ 2 * a) ^ i * (α₂ ^ 2 * b) ^ j * (α₃ ^ 2 * c) ^ k * (α₄ ^ 2 * d) ^ l := by
      simp only [hP]; push_cast; ring
    rw [e]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ g1) (one_le_pow₀ g2)) (one_le_pow₀ g3))
      (one_le_pow₀ g4)
  have hVt : ((a ^ i * b ^ j * c ^ k * d ^ l : ℕ) : ℚ) < ((t : ℚ) + 1) ^ 2 := by
    exact_mod_cast hlt
  have ht0 : (0 : ℚ) < (t : ℚ) + 1 := by positivity
  have hsq : 1 ≤ (P * ((t : ℚ) + 1)) ^ 2 := by
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left hVt.le (pow_nonneg hP0 2)
    linarith
  have hx1 : 1 ≤ P * ((t : ℚ) + 1) := by
    by_contra hc
    rw [not_le] at hc
    have h0 : 0 ≤ P * ((t : ℚ) + 1) := by positivity
    nlinarith
  rw [div_le_iff₀ ht0]
  linarith

/-- Exponent `1/4` with a floor: if `B ≤ a^i b^j < (t + 1)^2`, `β₁^4 a ≥ 1`, `β₂^4 b ≥ 1` and
`β^4 B ≥ 1`, then `1/(t + 1) ≤ β β₁^i β₂^j`. -/
private theorem inv_succ_le_floor {t a b i j B : ℕ} {β₁ β₂ β : ℚ}
    (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) (hβ : 0 ≤ β)
    (g1 : 1 ≤ β₁ ^ 4 * a) (g2 : 1 ≤ β₂ ^ 4 * b) (gB : 1 ≤ β ^ 4 * B)
    (hB : B ≤ a ^ i * b ^ j) (hlt : a ^ i * b ^ j < (t + 1) ^ 2) :
    1 / ((t : ℚ) + 1) ≤ β * (β₁ ^ i * β₂ ^ j) := by
  set P := β₁ ^ i * β₂ ^ j with hP
  set V : ℕ := a ^ i * b ^ j with hV
  have hP0 : 0 ≤ P := by positivity
  have hPV : 1 ≤ P ^ 4 * V := by
    have : P ^ 4 * (V : ℚ) = (β₁ ^ 4 * a) ^ i * (β₂ ^ 4 * b) ^ j := by
      simp only [hP, hV]; push_cast; ring
    rw [this]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ g1) (one_le_pow₀ g2)
  have hBV : (B : ℚ) ≤ V := by exact_mod_cast hB
  have hVt : (V : ℚ) < ((t : ℚ) + 1) ^ 2 := by exact_mod_cast hlt
  have hV0 : (0 : ℚ) ≤ V := by positivity
  have ht0 : (0 : ℚ) < (t : ℚ) + 1 := by positivity
  set x := β * P * ((t : ℚ) + 1) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx4 : 1 ≤ x ^ 4 := by
    have e1 : x ^ 4 = β ^ 4 * P ^ 4 * (((t : ℚ) + 1) ^ 2) ^ 2 := by rw [hx]; ring
    have e2 : β ^ 4 * P ^ 4 * (V : ℚ) ^ 2 ≤ x ^ 4 := by
      rw [e1]
      have : (V : ℚ) ^ 2 ≤ (((t : ℚ) + 1) ^ 2) ^ 2 := pow_le_pow_left₀ hV0 hVt.le 2
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have e3 : 1 ≤ β ^ 4 * P ^ 4 * (V : ℚ) ^ 2 := by
      have hb4 : 0 ≤ β ^ 4 := by positivity
      have : β ^ 4 * B ≤ β ^ 4 * V := mul_le_mul_of_nonneg_left hBV hb4
      nlinarith
    linarith
  have hx1 : 1 ≤ x := by
    by_contra hc
    rw [not_le] at hc
    have := pow_lt_one₀ hx0 hc (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  rw [div_le_iff₀ ht0]
  linarith

/-- A positive integer whose prime factors lie in `{a, b, c, d}` is the product of the
corresponding prime powers. -/
private theorem eq_four_pow {V a b c d : ℕ} (hV : V ≠ 0) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hsub : V.primeFactors ⊆ {a, b, c, d}) :
    V = a ^ V.factorization a * b ^ V.factorization b * c ^ V.factorization c *
      d ^ V.factorization d := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hV]
  rw [Finsupp.prod_of_support_subset _ (s := {a, b, c, d}) (by rwa [Nat.support_factorization])
    _ (fun _ _ => pow_zero _)]
  rw [Finset.prod_insert (by simp [hab, hac, had]), Finset.prod_insert (by simp [hbc, hbd]),
    Finset.prod_pair hcd]
  ring

private theorem sum_pair_mul {γ : Type*} (s : Finset ℕ) (t : Finset γ) (f : ℕ → ℚ)
    (g : γ → ℚ) : ∑ u ∈ s ×ˢ t, f u.1 * g u.2 = (∑ i ∈ s, f i) * ∑ v ∈ t, g v := by
  rw [Finset.sum_product, Finset.sum_mul_sum]

/-- Summing product weights over an injective image in `ℕ^4`. -/
private theorem sum_weights_le (T : Finset ℕ) (π : ℕ → ℕ × ℕ × ℕ × ℕ) (hinj : Set.InjOn π T)
    {w₁ w₂ w₃ w₄ : ℚ} (h1 : 0 ≤ w₁) (h2 : 0 ≤ w₂) (h3 : 0 ≤ w₃) (h4 : 0 ≤ w₄)
    (l1 : w₁ < 1) (l2 : w₂ < 1) (l3 : w₃ < 1) (l4 : w₄ < 1) :
    ∑ t ∈ T, w₁ ^ (π t).1 * (w₂ ^ (π t).2.1 * (w₃ ^ (π t).2.2.1 * w₄ ^ (π t).2.2.2)) ≤
      1 / (1 - w₁) * (1 / (1 - w₂) * (1 / (1 - w₃) * (1 / (1 - w₄)))) := by
  set F : ℕ × ℕ × ℕ × ℕ → ℚ := fun u => w₁ ^ u.1 * (w₂ ^ u.2.1 * (w₃ ^ u.2.2.1 * w₄ ^ u.2.2.2))
    with hF
  set K := (T.image π).sup (fun u => max (max u.1 u.2.1) (max u.2.2.1 u.2.2.2)) + 1 with hK
  set box := Finset.range K ×ˢ Finset.range K ×ˢ Finset.range K ×ˢ Finset.range K with hbox
  have hsub : T.image π ⊆ box := by
    intro u hu
    have := Finset.le_sup (f := fun u : ℕ × ℕ × ℕ × ℕ => max (max u.1 u.2.1)
      (max u.2.2.1 u.2.2.2)) hu
    simp only [hbox, Finset.mem_product, Finset.mem_range]
    omega
  have hF0 : ∀ u, 0 ≤ F u := fun u => by positivity
  have hsum : ∑ u ∈ box, F u = (∑ i ∈ Finset.range K, w₁ ^ i) *
      ((∑ i ∈ Finset.range K, w₂ ^ i) * ((∑ i ∈ Finset.range K, w₃ ^ i) *
        (∑ i ∈ Finset.range K, w₄ ^ i))) := by
    rw [hbox, sum_pair_mul _ _ (fun i => w₁ ^ i)
        (fun v : ℕ × ℕ × ℕ => w₂ ^ v.1 * (w₃ ^ v.2.1 * w₄ ^ v.2.2)),
      sum_pair_mul _ _ (fun i => w₂ ^ i) (fun v : ℕ × ℕ => w₃ ^ v.1 * w₄ ^ v.2),
      sum_pair_mul _ _ (fun i => w₃ ^ i) (fun i => w₄ ^ i)]
  have q1 := geom_partial_le h1 l1 K
  have q2 := geom_partial_le h2 l2 K
  have q3 := geom_partial_le h3 l3 K
  have q4 := geom_partial_le h4 l4 K
  have p1 : 0 ≤ ∑ i ∈ Finset.range K, w₁ ^ i := Finset.sum_nonneg fun i _ => pow_nonneg h1 i
  have p2 : 0 ≤ ∑ i ∈ Finset.range K, w₂ ^ i := Finset.sum_nonneg fun i _ => pow_nonneg h2 i
  have p3 : 0 ≤ ∑ i ∈ Finset.range K, w₃ ^ i := Finset.sum_nonneg fun i _ => pow_nonneg h3 i
  have p4 : 0 ≤ ∑ i ∈ Finset.range K, w₄ ^ i := Finset.sum_nonneg fun i _ => pow_nonneg h4 i
  calc ∑ t ∈ T, w₁ ^ (π t).1 * (w₂ ^ (π t).2.1 * (w₃ ^ (π t).2.2.1 * w₄ ^ (π t).2.2.2))
        = ∑ u ∈ T.image π, F u := by
        rw [Finset.sum_image fun x hx y hy h => hinj hx hy h]
    _ ≤ ∑ u ∈ box, F u := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hF0 u)
    _ ≤ _ := by
        rw [hsum]
        gcongr

/-- Rankin bound for the exact squares `t ≡ 2 (mod 3)`: `σ(t^2)` is supported on
`{g₁, g₂, g₃, g₄}`, and when neither `g₃` nor `g₄` divides it, `σ(t^2) ≥ B`. -/
private theorem tail_le (T : Finset ℕ) {g₁ g₂ g₃ g₄ B : ℕ} {α₁ α₂ α₃ α₄ β₁ β₂ β : ℚ}
    (p3 : g₃.Prime) (p4 : g₄.Prime)
    (h12 : g₁ ≠ g₂) (h13 : g₁ ≠ g₃) (h14 : g₁ ≠ g₄) (h23 : g₂ ≠ g₃) (h24 : g₂ ≠ g₄)
    (h34 : g₃ ≠ g₄)
    (a1 : 0 ≤ α₁) (a2 : 0 ≤ α₂) (a3 : 0 ≤ α₃) (a4 : 0 ≤ α₄)
    (l1 : α₁ < 1) (l2 : α₂ < 1) (l3 : α₃ < 1) (l4 : α₄ < 1)
    (w1 : 1 ≤ α₁ ^ 2 * g₁) (w2 : 1 ≤ α₂ ^ 2 * g₂) (w3 : 1 ≤ α₃ ^ 2 * g₃) (w4 : 1 ≤ α₄ ^ 2 * g₄)
    (b1 : 0 ≤ β₁) (b2 : 0 ≤ β₂) (bβ : 0 ≤ β) (m1 : β₁ < 1) (m2 : β₂ < 1)
    (v1 : 1 ≤ β₁ ^ 4 * g₁) (v2 : 1 ≤ β₂ ^ 4 * g₂) (vB : 1 ≤ β ^ 4 * B)
    (hT : ∀ t ∈ T, 10 ≤ t ∧ (phi3 t).primeFactors ⊆ {g₁, g₂, g₃, g₄} ∧
      (¬ g₃ ∣ phi3 t → ¬ g₄ ∣ phi3 t → B ≤ phi3 t)) :
    ∑ t ∈ T, (fv t - 1) ≤ 121 / 100 * (β * (1 / (1 - β₁) * (1 / (1 - β₂) * (1 * 1))) +
      (α₃ + α₄) * (1 / (1 - α₁) * (1 / (1 - α₂) * (1 / (1 - α₃) * (1 / (1 - α₄)))))) := by
  set G := 1 / (1 - α₁) * (1 / (1 - α₂) * (1 / (1 - α₃) * (1 / (1 - α₄)))) with hG
  have hV0 : ∀ t, phi3 t ≠ 0 := fun t => by unfold phi3; omega
  have hrep : ∀ t ∈ T, phi3 t = g₁ ^ (phi3 t).factorization g₁ *
      g₂ ^ (phi3 t).factorization g₂ * g₃ ^ (phi3 t).factorization g₃ *
      g₄ ^ (phi3 t).factorization g₄ := fun t ht =>
    eq_four_pow (hV0 t) h12 h13 h14 h23 h24 h34 (hT t ht).2.1
  have hlt : ∀ t ∈ T, phi3 t < (t + 1) ^ 2 := fun t ht =>
    phi3_lt_succ_sq (by have := (hT t ht).1; omega)
  have hw : ∀ t ∈ T, 1 / ((t : ℚ) + 1) ≤ α₁ ^ (phi3 t).factorization g₁ *
      α₂ ^ (phi3 t).factorization g₂ * α₃ ^ (phi3 t).factorization g₃ *
      α₄ ^ (phi3 t).factorization g₄ := by
    intro t ht
    have h := hlt t ht
    rw [hrep t ht] at h
    exact inv_succ_le a1 a2 a3 a4 w1 w2 w3 w4 h
  have hfv : ∀ t ∈ T, fv t - 1 ≤ 121 / 100 * (1 / ((t : ℚ) + 1)) := fun t ht =>
    fv_sub_le (hT t ht).1
  have inj4 : ∀ x ∈ T, ∀ y ∈ T, (phi3 x).factorization g₁ = (phi3 y).factorization g₁ →
      (phi3 x).factorization g₂ = (phi3 y).factorization g₂ →
      (phi3 x).factorization g₃ = (phi3 y).factorization g₃ →
      (phi3 x).factorization g₄ = (phi3 y).factorization g₄ → x = y := by
    intro x hx y hy e1 e2 e3 e4
    have : phi3 x = phi3 y := by rw [hrep x hx, hrep y hy, e1, e2, e3, e4]
    exact phi3_strictMono.injective this
  -- the three parts
  set Tx := T.filter (fun t => g₃ ∣ phi3 t) with hTx
  set Tr := T.filter (fun t => ¬ g₃ ∣ phi3 t) with hTr
  set Ty := Tr.filter (fun t => g₄ ∣ phi3 t) with hTy
  set T0 := Tr.filter (fun t => ¬ g₄ ∣ phi3 t) with hT0
  have memTx : ∀ {t}, t ∈ Tx → t ∈ T ∧ 1 ≤ (phi3 t).factorization g₃ := fun ht =>
    ⟨(Finset.mem_filter.mp ht).1,
      (p3.dvd_iff_one_le_factorization (hV0 _)).mp (Finset.mem_filter.mp ht).2⟩
  have memTy : ∀ {t}, t ∈ Ty → t ∈ T ∧ (phi3 t).factorization g₃ = 0 ∧
      1 ≤ (phi3 t).factorization g₄ := fun ht => by
    obtain ⟨htr, h4⟩ := Finset.mem_filter.mp ht
    obtain ⟨htT, h3⟩ := Finset.mem_filter.mp htr
    exact ⟨htT, Nat.factorization_eq_zero_of_not_dvd h3,
      (p4.dvd_iff_one_le_factorization (hV0 _)).mp h4⟩
  have memT0 : ∀ {t}, t ∈ T0 → t ∈ T ∧ (phi3 t).factorization g₃ = 0 ∧
      (phi3 t).factorization g₄ = 0 ∧ B ≤ phi3 t := fun ht => by
    obtain ⟨htr, h4⟩ := Finset.mem_filter.mp ht
    obtain ⟨htT, h3⟩ := Finset.mem_filter.mp htr
    exact ⟨htT, Nat.factorization_eq_zero_of_not_dvd h3,
      Nat.factorization_eq_zero_of_not_dvd h4, (hT _ htT).2.2 h3 h4⟩
  set πx : ℕ → ℕ × ℕ × ℕ × ℕ := fun t => ((phi3 t).factorization g₁,
    (phi3 t).factorization g₂, (phi3 t).factorization g₃ - 1, (phi3 t).factorization g₄)
    with hπx
  set πy : ℕ → ℕ × ℕ × ℕ × ℕ := fun t => ((phi3 t).factorization g₁,
    (phi3 t).factorization g₂, 0, (phi3 t).factorization g₄ - 1) with hπy
  set π0 : ℕ → ℕ × ℕ × ℕ × ℕ := fun t => ((phi3 t).factorization g₁,
    (phi3 t).factorization g₂, 0, 0) with hπ0
  have ix : Set.InjOn πx Tx := by
    intro x hx y hy hxy
    obtain ⟨hxT, hx3⟩ := memTx (Finset.mem_coe.mp hx)
    obtain ⟨hyT, hy3⟩ := memTx (Finset.mem_coe.mp hy)
    simp only [hπx, Prod.mk.injEq] at hxy
    exact inj4 x hxT y hyT hxy.1 hxy.2.1 (by omega) hxy.2.2.2
  have iy : Set.InjOn πy Ty := by
    intro x hx y hy hxy
    obtain ⟨hxT, hx3, hx4⟩ := memTy (Finset.mem_coe.mp hx)
    obtain ⟨hyT, hy3, hy4⟩ := memTy (Finset.mem_coe.mp hy)
    simp only [hπy, Prod.mk.injEq] at hxy
    exact inj4 x hxT y hyT hxy.1 hxy.2.1 (by omega) (by omega)
  have i0 : Set.InjOn π0 T0 := by
    intro x hx y hy hxy
    obtain ⟨hxT, hx3, hx4, -⟩ := memT0 (Finset.mem_coe.mp hx)
    obtain ⟨hyT, hy3, hy4, -⟩ := memT0 (Finset.mem_coe.mp hy)
    simp only [hπ0, Prod.mk.injEq] at hxy
    exact inj4 x hxT y hyT hxy.1 hxy.2.1 (by omega) (by omega)
  have sx : ∑ t ∈ Tx, 1 / ((t : ℚ) + 1) ≤ α₃ * G := by
    calc ∑ t ∈ Tx, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ Tx, α₃ * (α₁ ^ (πx t).1 * (α₂ ^ (πx t).2.1 *
          (α₃ ^ (πx t).2.2.1 * α₄ ^ (πx t).2.2.2))) := by
          refine Finset.sum_le_sum fun t ht => (hw t (memTx ht).1).trans_eq ?_
          simp only [hπx]
          obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (memTx ht).2
          rw [hm, Nat.add_sub_cancel_left, pow_add]
          ring
      _ = α₃ * ∑ t ∈ Tx, α₁ ^ (πx t).1 * (α₂ ^ (πx t).2.1 *
          (α₃ ^ (πx t).2.2.1 * α₄ ^ (πx t).2.2.2)) := by rw [Finset.mul_sum]
      _ ≤ α₃ * G := mul_le_mul_of_nonneg_left
          (sum_weights_le Tx πx ix a1 a2 a3 a4 l1 l2 l3 l4) a3
  have sy : ∑ t ∈ Ty, 1 / ((t : ℚ) + 1) ≤ α₄ * G := by
    calc ∑ t ∈ Ty, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ Ty, α₄ * (α₁ ^ (πy t).1 * (α₂ ^ (πy t).2.1 *
          (α₃ ^ (πy t).2.2.1 * α₄ ^ (πy t).2.2.2))) := by
          refine Finset.sum_le_sum fun t ht => (hw t (memTy ht).1).trans_eq ?_
          simp only [hπy]
          obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (memTy ht).2.2
          rw [(memTy ht).2.1, hm, Nat.add_sub_cancel_left, pow_add]
          ring
      _ = α₄ * ∑ t ∈ Ty, α₁ ^ (πy t).1 * (α₂ ^ (πy t).2.1 *
          (α₃ ^ (πy t).2.2.1 * α₄ ^ (πy t).2.2.2)) := by rw [Finset.mul_sum]
      _ ≤ α₄ * G := mul_le_mul_of_nonneg_left
          (sum_weights_le Ty πy iy a1 a2 a3 a4 l1 l2 l3 l4) a4
  have s0 : ∑ t ∈ T0, 1 / ((t : ℚ) + 1) ≤
      β * (1 / (1 - β₁) * (1 / (1 - β₂) * (1 * 1))) := by
    calc ∑ t ∈ T0, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ T0, β * (β₁ ^ (π0 t).1 * (β₂ ^ (π0 t).2.1 *
          ((0 : ℚ) ^ (π0 t).2.2.1 * (0 : ℚ) ^ (π0 t).2.2.2))) := by
          refine Finset.sum_le_sum fun t ht => ?_
          obtain ⟨htT, h3, h4, hB⟩ := memT0 ht
          have h := hlt t htT
          have hr := hrep t htT
          rw [h3, h4, pow_zero, pow_zero, mul_one, mul_one] at hr
          rw [hr] at h hB
          refine (inv_succ_le_floor b1 b2 bβ v1 v2 vB hB h).trans_eq ?_
          simp only [hπ0, pow_zero, mul_one]
      _ = β * ∑ t ∈ T0, β₁ ^ (π0 t).1 * (β₂ ^ (π0 t).2.1 *
          ((0 : ℚ) ^ (π0 t).2.2.1 * (0 : ℚ) ^ (π0 t).2.2.2)) := by rw [Finset.mul_sum]
      _ ≤ β * (1 / (1 - β₁) * (1 / (1 - β₂) * (1 / (1 - 0) * (1 / (1 - 0))))) :=
          mul_le_mul_of_nonneg_left (sum_weights_le T0 π0 i0 b1 b2 le_rfl le_rfl m1 m2
            (by norm_num) (by norm_num)) bβ
      _ = β * (1 / (1 - β₁) * (1 / (1 - β₂) * (1 * 1))) := by norm_num
  have split1 : ∑ t ∈ Tx, (fv t - 1) + ∑ t ∈ Tr, (fv t - 1) = ∑ t ∈ T, (fv t - 1) :=
    Finset.sum_filter_add_sum_filter_not T _ _
  have split2 : ∑ t ∈ Ty, (fv t - 1) + ∑ t ∈ T0, (fv t - 1) = ∑ t ∈ Tr, (fv t - 1) :=
    Finset.sum_filter_add_sum_filter_not Tr _ _
  have ex : ∑ t ∈ Tx, (fv t - 1) ≤ 121 / 100 * ∑ t ∈ Tx, 1 / ((t : ℚ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t ht => hfv t (memTx ht).1
  have ey : ∑ t ∈ Ty, (fv t - 1) ≤ 121 / 100 * ∑ t ∈ Ty, 1 / ((t : ℚ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t ht => hfv t (memTy ht).1
  have e0 : ∑ t ∈ T0, (fv t - 1) ≤ 121 / 100 * ∑ t ∈ T0, 1 / ((t : ℚ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t ht => hfv t (memT0 ht).1
  have k1 := mul_le_mul_of_nonneg_left sx (by norm_num : (0 : ℚ) ≤ 121 / 100)
  have k2 := mul_le_mul_of_nonneg_left sy (by norm_num : (0 : ℚ) ≤ 121 / 100)
  have k3 := mul_le_mul_of_nonneg_left s0 (by norm_num : (0 : ℚ) ≤ 121 / 100)
  rw [← split1, ← split2]
  linarith

/-! ## Closing by abundancy -/

private theorem close {N : ℕ} (h : OddPerfect N) (K : Finset ℕ) (hK : K ⊆ N.primeFactors)
    (c : ℕ → ℚ) (hC : ∀ p ∈ K, abundancy (p ^ N.factorization p) ≤ c p) (S : ℚ)
    (hT : ∀ t ∈ N.primeFactors \ K, N.factorization t = 2)
    (hS : ∑ t ∈ N.primeFactors \ K, (fv t - 1) ≤ S)
    (hfin : ∏ p ∈ K, c p < 2 * (1 - S)) : False := by
  have hN0 := h.ne_zero
  set T := N.primeFactors \ K with hTdef
  have ht1 : ∀ t ∈ T, 1 ≤ t := fun t ht =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp ht).1).one_lt.le
  have hx0 : ∀ t ∈ T, 0 ≤ fv t - 1 := fun t ht => sub_nonneg.mpr (one_le_fv (ht1 t ht))
  have hG := prod_mul_one_sub_le T (fun t => fv t - 1) hx0
  simp only [add_sub_cancel] at hG
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors hN0, ← Finset.prod_sdiff hK] at hab
  have hTeq : ∏ t ∈ T, abundancy (t ^ N.factorization t) = ∏ t ∈ T, fv t :=
    Finset.prod_congr rfl fun t ht => by
      rw [hT t ht, abundancy_sq (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp ht).1)]
  rw [← hTdef, hTeq] at hab
  have hP0 : 0 ≤ ∏ t ∈ T, fv t :=
    Finset.prod_nonneg fun t ht => le_trans zero_le_one (one_le_fv (ht1 t ht))
  have hK0 : 0 ≤ ∏ p ∈ K, abundancy (p ^ N.factorization p) :=
    Finset.prod_nonneg fun _ _ => abundancy_nonneg _
  have hKC : ∏ p ∈ K, abundancy (p ^ N.factorization p) ≤ ∏ p ∈ K, c p :=
    Finset.prod_le_prod (fun _ _ => abundancy_nonneg _) hC
  have hPT : (∏ t ∈ T, fv t) * (1 - S) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hS hP0]
  have hpos : 0 < 1 - S := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hPT hK0]

/-! ## Removing a prime from a number, with fuel -/

/-- Divide `n` by `p` while possible, at most `f` times. -/
private def strip (p : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | f + 1, n => if n % p = 0 ∧ n ≠ 0 then strip p f (n / p) else n

private theorem strip_dvd (p : ℕ) : ∀ f n, strip p f n ∣ n
  | 0, n => by simp [strip]
  | f + 1, n => by
    unfold strip
    split_ifs with hc
    · exact (strip_dvd p f (n / p)).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hc.1))
    · exact dvd_rfl

private theorem strip_ne_zero {p f n : ℕ} (hn : n ≠ 0) : strip p f n ≠ 0 := by
  intro h0
  have := strip_dvd p f n
  rw [h0, zero_dvd_iff] at this
  exact hn this

private theorem strip_not_dvd {p : ℕ} (hp : 2 ≤ p) : ∀ f n, n ≠ 0 → n < 2 ^ f →
    ¬ p ∣ strip p f n
  | 0, n, hn, hlt => by simp at hlt; omega
  | f + 1, n, hn, hlt => by
    unfold strip
    split_ifs with hc
    · have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mod_eq_zero hc.1)
      have h1 : n / p ≠ 0 := (Nat.div_pos hpn (by omega)).ne'
      have h2 : n / p < 2 ^ f := by
        have : n / p ≤ n / 2 := Nat.div_le_div_left hp (by norm_num)
        rw [pow_succ] at hlt
        omega
      exact strip_not_dvd hp f (n / p) h1 h2
    · intro hd
      exact hc ⟨Nat.mod_eq_zero_of_dvd hd, hn⟩

/-- Bisection with fuel for the integer square root; any output is acceptable. -/
private def sqLo (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if ((lo + hi) / 2) * ((lo + hi) / 2) ≤ m then sqLo m f ((lo + hi) / 2) hi
    else sqLo m f lo ((lo + hi) / 2)

/-- The part of `phi3 x / 3` prime to `7` and `13`. -/
private def mpart (x : ℕ) : ℕ := strip 13 64 (strip 7 64 (phi3 x / 3))

/-- `y` cannot be a second slot prime next to `x`. -/
private def yfail (x y : ℕ) : Bool :=
  y % 2 == 0 || y == 1 || y % 3 != 1 || strip x 64 (mpart y) != 1

private def killM (x m s : ℕ) : Bool :=
  m != 1 && yfail x m && decide (s * s ≤ m) && decide (m < (s + 1) * (s + 1)) &&
    (s * s != m || yfail x s)

/-- Certificate that `x` is not a slot prime. -/
private def kill (x : ℕ) : Bool :=
  x % 2 == 0 || x == 1 || killM x (mpart x) (sqLo (mpart x) 40 0 (2 ^ 20))

private theorem kill_all : (List.range 10000).all (fun x => x % 3 != 1 || kill x) = true := by
  decide +kernel

private theorem kill_of_lt {x : ℕ} (hx : x < 10000) (h3 : x % 3 = 1) : kill x = true := by
  have := kill_all
  rw [List.all_eq_true] at this
  have h := this x (List.mem_range.mpr hx)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  exact h.resolve_left (by simp [h3])

/-! ## Root checks for small smooth values -/

private def lowRoot (V : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if phi3 ((lo + hi) / 2) ≤ V then lowRoot V f ((lo + hi) / 2) hi
    else lowRoot V f lo ((lo + hi) / 2)

/-- Either `V` is not a value of `phi3`, or it is `phi3` of a member of `L`. -/
private def rootIn (L : List ℕ) (V : ℕ) : Bool :=
  (decide (phi3 (lowRoot V 64 0 (2 ^ 40)) < V) &&
      decide (V < phi3 (lowRoot V 64 0 (2 ^ 40) + 1))) ||
    (phi3 (lowRoot V 64 0 (2 ^ 40)) == V && L.contains (lowRoot V 64 0 (2 ^ 40)))

private theorem mem_of_rootIn {L : List ℕ} {V t : ℕ} (hV : rootIn L V = true)
    (ht : phi3 t = V) : t ∈ L := by
  unfold rootIn at hV
  set m := lowRoot V 64 0 (2 ^ 40)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at hV
  rcases hV with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← ht] at h1 h2
    have := phi3_strictMono.lt_iff_lt.mp h1
    have := phi3_strictMono.lt_iff_lt.mp h2
    omega
  · rw [← ht] at h1
    rw [← phi3_strictMono.injective h1]
    exact h2

private theorem box_7_13 : ∀ a < 19, ∀ b < 15, 7 ^ a * 13 ^ b < 10 ^ 16 →
    rootIn [0, 2, 3, 9, 18] (7 ^ a * 13 ^ b) = true := by
  decide +kernel

/-! ## Small helpers -/

private theorem one_le_pv {x n : ℕ} (hx : x.Prime) (hn : n ≠ 0) (hd : x ∣ n) :
    1 ≤ padicValNat x n := by
  have := Fact.mk hx
  exact one_le_padicValNat_of_dvd hn hd

private theorem exp_lt_of_pow {c k V B K : ℕ} (hc : 1 ≤ c) (hV0 : 0 < V) (hdvd : c ^ k ∣ V)
    (hV : V < B) (hK : B ≤ c ^ K) : k < K := by
  by_contra hk
  have h1 : c ^ K ≤ c ^ k := Nat.pow_le_pow_right hc (by omega)
  have h2 : c ^ k ≤ V := Nat.le_of_dvd hV0 hdvd
  omega

private theorem small_cases {t : ℕ} (h1 : t < 10) (h2 : t % 3 = 2) :
    t = 2 ∨ t = 5 ∨ t = 8 := by
  omega

private theorem three_le_card {O : Finset ℕ} {a b c : ℕ} (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ O.card := by
  have hsub : ({a, b, c} : Finset ℕ) ⊆ O := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this
  exact this

/-- `phi3 w = 3 · (phi3 w / 3)` with `3 ∤ phi3 w / 3` when `w ≡ 1 (mod 3)`. -/
private theorem phi3_div_three {w : ℕ} (hw : w % 3 = 1) :
    phi3 w = 3 * (phi3 w / 3) ∧ ¬ 3 ∣ phi3 w / 3 := by
  have h3 := (three_dvd_phi3_iff w).2 hw
  have e : phi3 w = 3 * (phi3 w / 3) := (Nat.mul_div_cancel' h3).symm
  refine ⟨e, fun hd => not_nine_dvd_phi3 w ?_⟩
  rw [e]
  exact Nat.mul_dvd_mul_left 3 hd

/-! ## The slot primes are large -/

/-- If `phi3 y / 3` has all its prime factors in `{7, 13, x}`, then `yfail x y = false`. -/
private theorem yfail_false {x y : ℕ} (hx : 2 ≤ x) (hy : y.Prime) (hy3 : y % 3 = 1)
    (hlt : phi3 y / 3 < 2 ^ 64)
    (hsupp : ∀ d, d.Prime → d ∣ phi3 y / 3 → d = 7 ∨ d = 13 ∨ d = x) :
    yfail x y = false := by
  have hy2 : y ≠ 2 := by rintro rfl; norm_num at hy3
  have hyodd : y % 2 = 1 := Nat.odd_iff.mp (hy.odd_of_ne_two hy2)
  have hy1 : y ≠ 1 := hy.one_lt.ne'
  have hn0 : phi3 y / 3 ≠ 0 := by
    have := (phi3_div_three hy3).1
    intro h0; rw [h0] at this; unfold phi3 at this; omega
  set n := phi3 y / 3 with hn
  have hs7 := strip_dvd 7 64 n
  have hs7n := strip_not_dvd (by norm_num : 2 ≤ 7) 64 n hn0 hlt
  have hs7z := strip_ne_zero (p := 7) (f := 64) hn0
  have hs7lt : strip 7 64 n < 2 ^ 64 := lt_of_le_of_lt (Nat.le_of_dvd (by omega) hs7) hlt
  have hs13 := strip_dvd 13 64 (strip 7 64 n)
  have hs13n := strip_not_dvd (by norm_num : 2 ≤ 13) 64 _ hs7z hs7lt
  have hs13z := strip_ne_zero (p := 13) (f := 64) hs7z
  have hs13lt : strip 13 64 (strip 7 64 n) < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hs7z) hs13) hs7lt
  have hsx := strip_dvd x 64 (strip 13 64 (strip 7 64 n))
  have hsxn := strip_not_dvd hx 64 _ hs13z hs13lt
  have hsxz := strip_ne_zero (p := x) (f := 64) hs13z
  have hone : strip x 64 (strip 13 64 (strip 7 64 n)) = 1 := by
    by_contra hne
    obtain ⟨d, hd, hdd⟩ := Nat.exists_prime_and_dvd hne
    have hdn : d ∣ n := hdd.trans (hsx.trans (hs13.trans hs7))
    rcases hsupp d hd hdn with rfl | rfl | rfl
    · exact hs7n ((hdd.trans hsx).trans hs13)
    · exact hs13n (hdd.trans hsx)
    · exact hsxn hdd
  unfold yfail mpart
  rw [← hn, hone]
  simp [hyodd, hy1, hy3]

/-- Every slot prime is at least `10^4`. -/
private theorem slot_large {O : Finset ℕ} (hO : O.card ≤ 2)
    (hOp : ∀ w ∈ O, w.Prime ∧ w % 3 = 1)
    (hstr : ∀ w ∈ O, ∀ d, d.Prime → d ∣ phi3 w → d = 3 ∨ d = 7 ∨ d = 13 ∨ (d ∈ O ∧ d ≠ w))
    (hcap : ∀ w ∈ O, ∀ y ∈ O, y ≠ w → (phi3 w).factorization y ≤ 2)
    {z : ℕ} (hz : z ∈ O) : 10000 ≤ z := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hzp, hz3⟩ := hOp z hz
  have hkk := kill_of_lt hlt hz3
  have hz2 : z ≠ 2 := by rintro rfl; norm_num at hz3
  have hzodd : z % 2 = 1 := Nat.odd_iff.mp (hzp.odd_of_ne_two hz2)
  have hz1 : z ≠ 1 := hzp.one_lt.ne'
  have hk' : killM z (mpart z) (sqLo (mpart z) 40 0 (2 ^ 20)) = true := by
    unfold kill at hkk
    simpa [hzodd, hz1] using hkk
  set m := mpart z with hm
  set s := sqLo m 40 0 (2 ^ 20) with hs
  unfold killM at hk'
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hk'
  obtain ⟨⟨⟨⟨hm1, hym⟩, hs1⟩, hs2⟩, hsq⟩ := hk'
  obtain ⟨he, hn3⟩ := phi3_div_three hz3
  set n := phi3 z / 3 with hn
  have hn0 : n ≠ 0 := by intro h0; rw [h0] at he; unfold phi3 at he; omega
  have hnlt : n < 33554432 := by
    have hz2' : z ^ 2 ≤ 99980001 :=
      (Nat.pow_le_pow_left (show z ≤ 9999 by omega) 2).trans (by norm_num)
    have : phi3 z < 100663296 := by unfold phi3; omega
    omega
  have hn64 : n < 2 ^ 64 := lt_of_lt_of_le hnlt (by norm_num)
  have hs7 := strip_dvd 7 64 n
  have hs7n := strip_not_dvd (by norm_num : 2 ≤ 7) 64 n hn0 hn64
  have hs7z := strip_ne_zero (p := 7) (f := 64) hn0
  have hs7lt : strip 7 64 n < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hs7) hn64
  have hs13 := strip_dvd 13 64 (strip 7 64 n)
  have hs13n := strip_not_dvd (by norm_num : 2 ≤ 13) 64 _ hs7z hs7lt
  have hmn : m ∣ n := hs13.trans hs7
  have hm0 : m ≠ 0 := strip_ne_zero hs7z
  have hmz : m ∣ phi3 z := hmn.trans ⟨3, by rw [he]; ring⟩
  -- every prime factor of `m` is a slot prime other than `z`
  have hfac : ∀ d, d.Prime → d ∣ m → d ∈ O ∧ d ≠ z := by
    intro d hd hdm
    rcases hstr z hz d hd (hdm.trans hmz) with rfl | rfl | rfl | h'
    · exact absurd (hdm.trans hmn) hn3
    · exact absurd ((hdm.trans hs13)) hs7n
    · exact absurd hdm hs13n
    · exact h'
  obtain ⟨y, hy, hym'⟩ := Nat.exists_prime_and_dvd hm1
  obtain ⟨hyO, hyz⟩ := hfac y hy hym'
  have huniq : ∀ {d}, d.Prime → d ∣ m → d = y := by
    intro d hd hdm
    obtain ⟨hdO, hdz⟩ := hfac d hd hdm
    by_contra hdy
    have := three_le_card hz hyO hdO (Ne.symm hyz) (Ne.symm hdz) (Ne.symm hdy)
    omega
  have hmy := Nat.eq_prime_pow_of_unique_prime_dvd hm0 huniq
  set k := m.primeFactorsList.length with hk
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    rw [this, pow_zero] at hmy
    exact hm1 hmy
  have hk2 : k ≤ 2 := by
    have hdv : y ^ k ∣ phi3 z := by rw [← hmy]; exact hmz
    have := (hy.pow_dvd_iff_le_factorization (by unfold phi3; omega)).mp hdv
    have := hcap z hz y hyO hyz
    omega
  -- `y` would be a slot prime next to `z`
  have hyO' := hOp y hyO
  have hyle : y ≤ n := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hym')
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hmn)
  have hylt : phi3 y / 3 < 2 ^ 64 := by
    have hy2' : y ^ 2 ≤ 1125899906842624 :=
      (Nat.pow_le_pow_left (show y ≤ 33554432 by omega) 2).trans (by norm_num)
    have : phi3 y / 3 < 18446744073709551616 := by unfold phi3; omega
    exact lt_of_lt_of_le this (by norm_num)
  have hysupp : ∀ d, d.Prime → d ∣ phi3 y / 3 → d = 7 ∨ d = 13 ∨ d = z := by
    intro d hd hdd
    obtain ⟨hey, hn3y⟩ := phi3_div_three hyO'.2
    have hdy : d ∣ phi3 y := hdd.trans (Dvd.intro_left 3 hey.symm)
    rcases hstr y hyO d hd hdy with rfl | h7 | h13 | ⟨hdO, hdy'⟩
    · exact absurd hdd hn3y
    · exact Or.inl h7
    · exact Or.inr (Or.inl h13)
    · right; right
      by_contra hdz
      have := three_le_card hz hyO hdO (Ne.symm hyz) (Ne.symm hdz) (Ne.symm hdy')
      omega
  have hyf := yfail_false (x := z) hzp.two_le hy hyO'.2 hylt hysupp
  rcases (by omega : k = 1 ∨ k = 2) with h1 | h2
  · rw [h1, pow_one] at hmy
    rw [hmy] at hym
    rw [hyf] at hym
    exact absurd hym (by decide)
  · rw [h2, sq] at hmy
    have hsy : s = y := by
      rw [hmy] at hs1 hs2
      have e1 : s ≤ y := by
        by_contra hc
        rw [not_le] at hc
        have : (y + 1) * (y + 1) ≤ s * s := Nat.mul_le_mul hc hc
        nlinarith
      have e2 : y < s + 1 := by
        by_contra hc
        rw [not_lt] at hc
        have : (s + 1) * (s + 1) ≤ y * y := Nat.mul_le_mul hc hc
        omega
      omega
    rcases hsq with hne | hyes
    · exact hne (by rw [hsy, hmy])
    · rw [hsy, hyf] at hyes
      exact absurd hyes (by decide)

end RestrainedThree

open RestrainedThree

/-! ## The leaf `q = 13, r = 7` -/

/-- **Restrained, leaf `q = 13, r = 7`.** Under the hypotheses of `restrained_three_sq_cases`,
the configuration `q = 13, r = 7` is impossible. -/
theorem restrained_not_thirteen_seven {N q r : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (h3 : N.factorization 3 = 2) : ¬ (q = 13 ∧ r = 7) := by
  rintro ⟨rfl, rfl⟩
  have hN0 := h.ne_zero
  have mem : ∀ {p}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN0⟩
  have d3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have d13 : 13 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have d7 : 7 ∣ N := OPNStarter.force_prime h.perfect (by norm_num : Nat.Prime 13) rfl
    (by norm_num) (by norm_num) ((by norm_num : 7 ∣ 13 + 1).trans
      (succ_dvd_sigma_special (by norm_num) hodd))
  set K : Finset ℕ := {3, 7, 13} with hK
  have hKsub : K ⊆ N.primeFactors := by
    intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact mem Nat.prime_three d3
    · exact mem (by norm_num) d7
    · exact mem (by norm_num) d13
  set T := N.primeFactors \ K with hT
  have hTmem : ∀ {t}, t ∈ T → t.Prime ∧ t ∣ N ∧ t ≠ 3 ∧ t ≠ 7 ∧ t ≠ 13 := by
    intro t ht
    obtain ⟨htN, htK⟩ := Finset.mem_sdiff.mp ht
    simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or] at htK
    exact ⟨Nat.prime_of_mem_primeFactors htN, Nat.dvd_of_mem_primeFactors htN, htK.1,
      htK.2.1, htK.2.2⟩
  have key2 : ∀ {t}, t ∈ T → N.factorization t = 2 := fun ht =>
    hsq _ (Finset.mem_sdiff.mp ht).1 (hTmem ht).2.2.2.2 (hTmem ht).2.2.2.1
  have mod3 : ∀ {t}, t ∈ T → t % 3 = 1 ∨ t % 3 = 2 := by
    intro t ht
    obtain ⟨htp, -, t3, -, -⟩ := hTmem ht
    have h0 : t % 3 ≠ 0 := fun h0 => t3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three htp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
    omega
  set O := T.filter (fun t => t % 3 = 1) with hO
  have memO : ∀ {t}, t ∈ O ↔ t ∈ T ∧ t % 3 = 1 := Finset.mem_filter
  -- at most two slot primes
  have hOcard : O.card ≤ 2 := by
    have hle := sum_padicValNat_sigma_le_factorization h.perfect Nat.prime_three (by norm_num) O
    have hc : ∑ p ∈ O, padicValNat 3 (σ 1 (p ^ N.factorization p)) = O.card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hpT, hp1⟩ := memO.mp hp
      rw [key2 hpT, sigma_prime_sq (hTmem hpT).1, padicValNat_three_phi3, if_pos hp1]
    omega
  -- prime factors of `σ(w^2)`
  have hstr : ∀ w ∈ T, ∀ d, d.Prime → d ∣ phi3 w → d = 3 ∨ d = 7 ∨ d = 13 ∨ (d ∈ O ∧ d ≠ w) := by
    intro w hw d hd hdd
    obtain ⟨hwp, -, -, -, -⟩ := hTmem hw
    by_cases hd3 : d = 3
    · exact Or.inl hd3
    have hd2 : d ≠ 2 := by rintro rfl; have := Nat.odd_iff.mp (phi3_odd w); omega
    have hdN : d ∣ N := OPNStarter.force_prime h.perfect hwp (key2 hw) hd hd2
      (by rw [sigma_prime_sq hwp]; exact hdd)
    have hd1 := prime_dvd_phi3_mod_three hd hd3 hdd
    have hdw : d ≠ w := by
      rintro rfl
      have := Nat.Coprime.eq_one_of_dvd (phi3_coprime_self d).symm hdd
      exact hd.one_lt.ne' this
    by_cases h7 : d = 7
    · exact Or.inr (Or.inl h7)
    by_cases h13 : d = 13
    · exact Or.inr (Or.inr (Or.inl h13))
    refine Or.inr (Or.inr (Or.inr ⟨memO.mpr ⟨Finset.mem_sdiff.mpr ⟨mem hd hdN, ?_⟩, hd1⟩, hdw⟩))
    simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hd3, h7, h13⟩
  have hlarge : ∀ z ∈ O, 10000 ≤ z := by
    intro z hz
    refine slot_large hOcard (fun w hw => ⟨(hTmem (memO.mp hw).1).1, (memO.mp hw).2⟩)
      (fun w hw => hstr w (memO.mp hw).1) (fun w hw y hy hyw => ?_) hz
    have hwT := (memO.mp hw).1
    have hyT := (memO.mp hy).1
    have hyp := (hTmem hyT).1
    have hle := sum_padicValNat_sigma_le_factorization h.perfect hyp
      (by have := (memO.mp hy).2; rintro rfl; norm_num at this) {w}
    rw [Finset.sum_singleton, key2 hwT, sigma_prime_sq (hTmem hwT).1, key2 hyT] at hle
    rwa [Nat.factorization_def _ hyp]
  -- two distinct large primes covering the slots
  obtain ⟨x, y, hxp, hyp, hx, hy, hxy, hOxy⟩ : ∃ x y : ℕ, x.Prime ∧ y.Prime ∧ 10000 ≤ x ∧
      10000 ≤ y ∧ x ≠ y ∧ O ⊆ {x, y} := by
    have p1 : Nat.Prime 10007 := by norm_num
    have p2 : Nat.Prime 10009 := by norm_num
    rcases Nat.lt_or_ge O.card 2 with hc | hc
    · rcases Nat.lt_or_ge O.card 1 with hc' | hc'
      · have : O = ∅ := Finset.card_eq_zero.mp (by omega : O.card = 0)
        exact ⟨10007, 10009, p1, p2, by norm_num, by norm_num, by norm_num, by simp [this]⟩
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by omega : O.card = 1)
        have haO : a ∈ O := by rw [ha]; exact Finset.mem_singleton_self a
        have hap := (hTmem (memO.mp haO).1).1
        by_cases h1 : a = 10007
        · exact ⟨a, 10009, hap, p2, hlarge a haO, by norm_num, by omega,
            by rw [ha]; simp⟩
        · exact ⟨a, 10007, hap, p1, hlarge a haO, by norm_num, h1, by rw [ha]; simp⟩
    · obtain ⟨a, b, hab, hOab⟩ := Finset.card_eq_two.mp (by omega : O.card = 2)
      have haO : a ∈ O := by rw [hOab]; simp
      have hbO : b ∈ O := by rw [hOab]; simp
      exact ⟨a, b, (hTmem (memO.mp haO).1).1, (hTmem (memO.mp hbO).1).1, hlarge a haO,
        hlarge b hbO, hab, hOab.subset⟩
  -- the tail over the primes `≡ 2 (mod 3)`
  set O2 := T.filter (fun t => ¬ t % 3 = 1) with hO2
  have hS2 := tail_le O2 (g₁ := 7) (g₂ := 13) (g₃ := x) (g₄ := y) (B := 10 ^ 16)
    (α₁ := 378 / 1000) (α₂ := 2774 / 10000) (α₃ := 1 / 100) (α₄ := 1 / 100)
    (β₁ := 615 / 1000) (β₂ := 527 / 1000) (β := 1 / 10 ^ 4) hxp hyp (by norm_num)
    (by omega) (by omega) (by omega) (by omega) hxy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by have : (10000 : ℚ) ≤ x := by exact_mod_cast hx
        rw [show ((1 : ℚ) / 100) ^ 2 = 1 / 10000 by norm_num]; linarith)
    (by have : (10000 : ℚ) ≤ y := by exact_mod_cast hy
        rw [show ((1 : ℚ) / 100) ^ 2 = 1 / 10000 by norm_num]; linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      intro t ht
      obtain ⟨htT, ht1⟩ := Finset.mem_filter.mp ht
      have ht2 : t % 3 = 2 := (mod3 htT).resolve_left ht1
      obtain ⟨htp, -, t3, t7, t13⟩ := hTmem htT
      have hsupp : (phi3 t).primeFactors ⊆ {7, 13, x, y} := by
        intro d hd
        have hdp := Nat.prime_of_mem_primeFactors hd
        have hdd := Nat.dvd_of_mem_primeFactors hd
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hstr t htT d hdp hdd with rfl | h7 | h13 | ⟨hdO, -⟩
        · have := (three_dvd_phi3_iff t).1 hdd; omega
        · exact Or.inl h7
        · exact Or.inr (Or.inl h13)
        · have := hOxy hdO
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          exact Or.inr (Or.inr this)
      refine ⟨?_, hsupp, fun hx' hy' => ?_⟩
      · by_contra hlt
        rw [not_le] at hlt
        rcases small_cases hlt ht2 with e | e | e
        · exact h.not_two_dvd (e ▸ (hTmem htT).2.1)
        · have h31 : 31 ∣ phi3 t := by rw [e]; norm_num [phi3]
          rcases hstr t htT 31 (by norm_num) h31 with h' | h' | h' | ⟨hO31, -⟩
          · norm_num at h'
          · norm_num at h'
          · norm_num at h'
          · have := hlarge 31 hO31
            norm_num at this
        · exact absurd (e ▸ htp) (by norm_num)
      · have hV0 : phi3 t ≠ 0 := by unfold phi3; omega
        have hrep := eq_four_pow hV0 (by norm_num : (7 : ℕ) ≠ 13) (by omega : (7 : ℕ) ≠ x)
          (by omega : (7 : ℕ) ≠ y) (by omega : (13 : ℕ) ≠ x) (by omega : (13 : ℕ) ≠ y) hxy hsupp
        rw [Nat.factorization_eq_zero_of_not_dvd hx', Nat.factorization_eq_zero_of_not_dvd hy',
          pow_zero, pow_zero, mul_one, mul_one] at hrep
        by_contra hlt
        rw [not_le] at hlt
        have hpos : 0 < phi3 t := Nat.pos_of_ne_zero hV0
        have ha : (phi3 t).factorization 7 < 19 := exp_lt_of_pow (c := 7) (by norm_num) hpos
          ⟨13 ^ (phi3 t).factorization 13, hrep⟩ hlt (by norm_num)
        have hb : (phi3 t).factorization 13 < 15 := exp_lt_of_pow (c := 13) (by norm_num) hpos
          ⟨7 ^ (phi3 t).factorization 7, by rw [mul_comm]; exact hrep⟩ hlt (by norm_num)
        have hmem := mem_of_rootIn (box_7_13 _ ha _ hb (by rw [← hrep]; exact hlt)) hrep
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with e | e | e | e | e
        · exact absurd (e ▸ htp) (by norm_num)
        · exact h.not_two_dvd (e ▸ (hTmem htT).2.1)
        · exact t3 e
        · exact absurd (e ▸ htp) (by norm_num)
        · exact absurd (e ▸ htp) (by norm_num))
  -- the slot part
  have hS1 : ∑ t ∈ O, (fv t - 1) ≤ 2 * (121 / 100 * (1 / ((10000 : ℚ) + 1))) := by
    have hb : ∀ t ∈ O, fv t - 1 ≤ 121 / 100 * (1 / ((10000 : ℚ) + 1)) := by
      intro t ht
      have h10 := hlarge t ht
      refine (fv_sub_le (by omega)).trans ?_
      have : (10000 : ℚ) ≤ t := by exact_mod_cast h10
      gcongr
    calc ∑ t ∈ O, (fv t - 1) ≤ ∑ _t ∈ O, 121 / 100 * (1 / ((10000 : ℚ) + 1)) :=
          Finset.sum_le_sum hb
      _ = O.card * (121 / 100 * (1 / ((10000 : ℚ) + 1))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (121 / 100 * (1 / ((10000 : ℚ) + 1))) := by
          have : (O.card : ℚ) ≤ 2 := by exact_mod_cast hOcard
          gcongr
  have hsplit : ∑ t ∈ O, (fv t - 1) + ∑ t ∈ O2, (fv t - 1) = ∑ t ∈ T, (fv t - 1) :=
    Finset.sum_filter_add_sum_filter_not T _ _
  set c : ℕ → ℚ := fun p => if p = 3 then 13 / 9 else if p = 7 then 7 / 6 else 13 / 12 with hc
  refine close h K hKsub c ?_ _ (fun t ht => key2 ht)
    (hsplit.symm.trans_le (add_le_add hS1 hS2)) ?_
  · intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · rw [h3, abundancy_sq Nat.prime_three]; norm_num [hc, fv]
    · refine (abundancy_prime_pow_lt (by norm_num) _).le.trans (le_of_eq ?_)
      norm_num [hc]
    · refine (abundancy_prime_pow_lt (by norm_num) _).le.trans (le_of_eq ?_)
      norm_num [hc]
  · rw [hK, Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
    norm_num [hc]

/-! ## Sharpened case theorem -/

/-- **Restrained odd perfect numbers, sharpened again.** With the hypotheses of
`three_dvd_of_one_exception`, either the exceptional prime is `3` (with `v_3(N)` even, at least
`4`, `q ≡ 1 (mod 3)`, `5 ∤ N` and `7 ∤ N`), or `3^2 ∥ N` and either `r = 13`, or `r = 61` with
`13^2 ∥ N` and `q ≡ 1 (mod 3)`. -/
theorem restrained_cases_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (r = 3 ∧ 4 ≤ N.factorization 3 ∧ Even (N.factorization 3) ∧ q % 3 = 1 ∧ ¬ 5 ∣ N ∧
      ¬ 7 ∣ N) ∨
    (N.factorization 3 = 2 ∧ (r = 13 ∨ (r = 61 ∧ N.factorization 13 = 2 ∧ q % 3 = 1))) := by
  rcases restrained_cases_two h hq hodd hr hrq hsq with h1 | ⟨h3, h2 | h2 | h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h3, Or.inl h2⟩
  · exact absurd h2 (restrained_not_thirteen_seven h hodd hsq h3)
  · exact Or.inr ⟨h3, Or.inr h2⟩

end OddPerfect

#print axioms OddPerfect.restrained_not_thirteen_seven
#print axioms OddPerfect.restrained_cases_three
