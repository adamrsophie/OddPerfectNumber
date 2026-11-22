import OddPerfect.RestrainedThree

/-!
# Restrained odd perfect numbers divisible by 3: the leaf `r = 61`

Setting of `restrained_three_sq_cases`: `N` is an odd perfect number with special prime `q`,
`r ≠ q` is a further prime, every other prime factor has exponent exactly 2, and `3^2 ∥ N`.
This file shows that the configuration `r = 61`, `13^2 ∥ N`, `q ≡ 1 (mod 3)` is impossible.

Then `q ≡ 1 (mod 12)`, `13 ∣ N` (from `σ(3^2) = 13`) and `61 ∣ N` (from `σ(13^2) = 3 · 61`).
Let `K = {3, 13, 61, q}` and let `T` be the other prime factors, all exact squares, split into
the slots `O` (primes `≡ 1 (mod 3)`) and the rest.

* The 3-adic ledger over `{13} ∪ O` gives `|O| ≤ 1`.
* For a slot `x`, `σ(x^2) = 3 · 13^d 61^a q^b`. An exact kernel check (`slotOK`) of all these
  values shows `x ≥ 8836` for every prime `q ∈ [157, 9277)` outside ten exceptions, and
  `x ≥ 169` for `q ∈ [9277, 9465)`. For `q ≥ 9465`, either `q ∣ σ(x^2)`, so
  `x^2 + x + 1 ≥ 3q`, or `b = 0` and the same check gives `x ≥ 169`.
* The exceptions below `157` and the values `181, 1801, 3169, 8269` are refuted by forcing
  through `q + 1 ∣ σ(q^e)`: each produces two different slots.
* For the other `t`, `σ(t^2) = 61^a 13^b q^c x^d`, and `rankin_tail` bounds the sum of
  `σ(t^2)/t^2 - 1`; the values `61^a 13^b` below `10^16` are checked directly.

The exponents of `q` and `61` enter only through the bound `p/(p - 1)`.

Main results: `restrained_not_sixty_one` and `restrained_cases_four`. The lemmas `rankin_tail`
and `abundancy_close` are stated for an arbitrary set of exact squares and four generators. The
configuration `r = 13` left by `restrained_cases_four` is closed in `OddPerfect.RestrainedFive`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace RestrainedFour

/-! ## Rational helpers -/

/-- `σ(s^2)/s^2` as a rational function of `s`. -/
def fv (s : ℕ) : ℚ := ((s : ℚ) ^ 2 + s + 1) / s ^ 2

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

/-- Rankin bound for a set of exact squares `t ≡ 2 (mod 3)`: `σ(t^2)` is supported on
`{g₁, g₂, g₃, g₄}`, and when neither `g₃` nor `g₄` divides it, `σ(t^2) ≥ B`. -/
theorem rankin_tail (T : Finset ℕ) {g₁ g₂ g₃ g₄ B : ℕ} {α₁ α₂ α₃ α₄ β₁ β₂ β : ℚ}
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

/-- If the exact squares outside `K` have `∑ (σ(t^2)/t^2 - 1) ≤ S` and the components over
`K` are bounded by `c` with `∏ c < 2 (1 - S)`, then `N` is not perfect. -/
theorem abundancy_close {N : ℕ} (h : OddPerfect N) (K : Finset ℕ) (hK : K ⊆ N.primeFactors)
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

/-! ## Small helpers -/

private theorem exp_lt_of_pow {c k V B K : ℕ} (hc : 1 ≤ c) (hV0 : 0 < V) (hdvd : c ^ k ∣ V)
    (hV : V < B) (hK : B ≤ c ^ K) : k < K := by
  by_contra hk
  have h1 : c ^ K ≤ c ^ k := Nat.pow_le_pow_right hc (by omega)
  have h2 : c ^ k ≤ V := Nat.le_of_dvd hV0 hdvd
  omega

private theorem small_cases {t : ℕ} (h1 : t < 10) (h2 : t % 3 = 2) :
    t = 2 ∨ t = 5 ∨ t = 8 := by
  omega

/-- `phi3 w = 3 · (phi3 w / 3)` with `3 ∤ phi3 w / 3` when `w ≡ 1 (mod 3)`. -/
private theorem phi3_div_three {w : ℕ} (hw : w % 3 = 1) :
    phi3 w = 3 * (phi3 w / 3) ∧ ¬ 3 ∣ phi3 w / 3 := by
  have h3 := (three_dvd_phi3_iff w).2 hw
  have e : phi3 w = 3 * (phi3 w / 3) := (Nat.mul_div_cancel' h3).symm
  refine ⟨e, fun hd => not_nine_dvd_phi3 w ?_⟩
  rw [e]
  exact Nat.mul_dvd_mul_left 3 hd

/-! ## Further helpers -/

private theorem eq_three_pow {V a b c : ℕ} (hV : V ≠ 0) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hsub : V.primeFactors ⊆ {a, b, c}) :
    V = a ^ V.factorization a * b ^ V.factorization b * c ^ V.factorization c := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hV]
  rw [Finsupp.prod_of_support_subset _ (s := {a, b, c}) (by rwa [Nat.support_factorization])
    _ (fun _ _ => pow_zero _)]
  rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc]
  ring

private theorem weight_ok {s g : ℕ} (hs : 1 ≤ s) (h : s ^ 2 ≤ g) :
    1 ≤ (1 / (s : ℚ)) ^ 2 * g := by
  have hs0 : (0 : ℚ) < s := by exact_mod_cast hs
  have hg : ((s : ℚ)) ^ 2 ≤ g := by exact_mod_cast h
  rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  linarith

private theorem inv_lt_one' {s : ℕ} (hs : 2 ≤ s) : 1 / (s : ℚ) < 1 := by
  have : (1 : ℚ) < s := by exact_mod_cast hs
  rw [div_lt_one (by linarith)]
  exact this

/-! ## Slot certificates -/

/-- `m` has a divisor `d` with `2 ≤ d < min m 100`. -/
private def hasSmallFactor (m : ℕ) : Bool :=
  (List.range 100).any fun d => decide (2 ≤ d) && decide (d < m) && m % d == 0

private theorem hasSmallFactor_false {m : ℕ} (hm : m.Prime) : hasSmallFactor m = false := by
  cases hb : hasSmallFactor m
  · rfl
  · exfalso
    unfold hasSmallFactor at hb
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hb
    obtain ⟨d, -, ⟨h2, hlt⟩, hmod⟩ := hb
    rcases hm.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with e | e <;> omega

/-- `m` cannot be a slot prime next to the special prime `q`. -/
private def badSlot (q m : ℕ) : Bool :=
  m % 2 == 0 || m % 3 != 1 || m == 13 || m == 61 || m == q || decide (m ≤ 1) ||
    hasSmallFactor m

private theorem badSlot_false {q x : ℕ} (hx : x.Prime) (hx3 : x % 3 = 1) (h13 : x ≠ 13)
    (h61 : x ≠ 61) (hq : x ≠ q) : badSlot q x = false := by
  have hx2 : x % 2 = 1 := by
    rcases hx.eq_two_or_odd with e | e
    · subst e; norm_num at hx3
    · exact e
  have h1 : ¬ x ≤ 1 := by have := hx.two_le; omega
  simp [badSlot, hx2, hx3, h13, h61, hq, h1, hasSmallFactor_false hx]

/-- `3V` is not `phi3` of a possible slot prime. -/
private def slotChk (q V : ℕ) : Bool :=
  (decide (phi3 (lowRoot (3 * V) 64 0 (2 ^ 40)) < 3 * V) &&
      decide (3 * V < phi3 (lowRoot (3 * V) 64 0 (2 ^ 40) + 1))) ||
    (phi3 (lowRoot (3 * V) 64 0 (2 ^ 40)) == 3 * V &&
      badSlot q (lowRoot (3 * V) 64 0 (2 ^ 40)))

private theorem slotChk_sound {q V x : ℕ} (h : slotChk q V = true) (hx : phi3 x = 3 * V) :
    badSlot q x = true := by
  unfold slotChk at h
  set m := lowRoot (3 * V) 64 0 (2 ^ 40)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← hx] at h1 h2
    have := phi3_strictMono.lt_iff_lt.mp h1
    have := phi3_strictMono.lt_iff_lt.mp h2
    omega
  · rw [← hx] at h1
    rw [← phi3_strictMono.injective h1]
    exact h2

private def loopQ (q X : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, v => decide (phi3 X ≤ 3 * v) || (slotChk q v && loopQ q X f (v * q))

private theorem loopQ_sound {q X : ℕ} (hq : 0 < q) : ∀ f v, loopQ q X f v = true →
    ∀ b, 3 * (v * q ^ b) < phi3 X → slotChk q (v * q ^ b) = true
  | 0, v, h => by simp [loopQ] at h
  | f + 1, v, h => by
    intro b hb
    simp only [loopQ, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · have : v ≤ v * q ^ b := Nat.le_mul_of_pos_right v (pow_pos hq b)
      omega
    · cases b with
      | zero => simpa using h1
      | succ b =>
        have e : v * q ^ (b + 1) = v * q * q ^ b := by ring
        rw [e] at hb ⊢
        exact loopQ_sound hq f (v * q) h2 b hb

private def loop61 (q X : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, v => decide (phi3 X ≤ 3 * v) || (loopQ q X 40 v && loop61 q X f (v * 61))

private theorem loop61_sound {q X : ℕ} (hq : 0 < q) : ∀ f v, loop61 q X f v = true →
    ∀ a b, 3 * (v * 61 ^ a * q ^ b) < phi3 X → slotChk q (v * 61 ^ a * q ^ b) = true
  | 0, v, h => by simp [loop61] at h
  | f + 1, v, h => by
    intro a b hb
    simp only [loop61, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · have : v ≤ v * 61 ^ a * q ^ b := by
        rw [mul_assoc]; exact Nat.le_mul_of_pos_right v (by positivity)
      omega
    · cases a with
      | zero =>
        simp only [pow_zero, mul_one] at hb ⊢
        exact loopQ_sound hq 40 v h1 b hb
      | succ a =>
        have e : v * 61 ^ (a + 1) * q ^ b = v * 61 * 61 ^ a * q ^ b := by ring
        rw [e] at hb ⊢
        exact loop61_sound hq f (v * 61) h2 a b hb

private def loop13 (q X : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, v => decide (phi3 X ≤ 3 * v) || (loop61 q X 40 v && loop13 q X f (v * 13))

private theorem loop13_sound {q X : ℕ} (hq : 0 < q) : ∀ f v, loop13 q X f v = true →
    ∀ d a b, 3 * (v * 13 ^ d * 61 ^ a * q ^ b) < phi3 X →
      slotChk q (v * 13 ^ d * 61 ^ a * q ^ b) = true
  | 0, v, h => by simp [loop13] at h
  | f + 1, v, h => by
    intro d a b hb
    simp only [loop13, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · have : v ≤ v * 13 ^ d * 61 ^ a * q ^ b := by
        rw [mul_assoc, mul_assoc]; exact Nat.le_mul_of_pos_right v (by positivity)
      omega
    · cases d with
      | zero =>
        simp only [pow_zero, mul_one] at hb ⊢
        exact loop61_sound hq 40 v h1 a b hb
      | succ d =>
        have e : v * 13 ^ (d + 1) * 61 ^ a * q ^ b = v * 13 * 13 ^ d * 61 ^ a * q ^ b := by
          ring
        rw [e] at hb ⊢
        exact loop13_sound hq f (v * 13) h2 d a b hb

/-- No slot prime below `X` has `σ(x^2) = 3 · 13^d 61^a q^b`. -/
private def slotOK (q X : ℕ) : Bool := loop13 q X 40 1

private theorem slot_ge {q X x d a b : ℕ} (hq : 0 < q) (hc : slotOK q X = true)
    (hx : x.Prime) (hx3 : x % 3 = 1) (h13 : x ≠ 13) (h61 : x ≠ 61) (hxq : x ≠ q)
    (he : phi3 x = 3 * (13 ^ d * 61 ^ a * q ^ b)) : X ≤ x := by
  by_contra hlt
  rw [not_le] at hlt
  have hlt' : 3 * (1 * 13 ^ d * 61 ^ a * q ^ b) < phi3 X := by
    rw [one_mul, ← he]; exact phi3_strictMono hlt
  have h1 := loop13_sound hq 40 1 hc d a b hlt'
  rw [one_mul] at h1
  have h2 := slotChk_sound h1 he
  rw [badSlot_false hx hx3 h13 h61 hxq] at h2
  exact absurd h2 (by decide)

/-- The special primes refuted by forcing. -/
private def excList : List ℕ := [13, 37, 61, 73, 97, 109, 181, 1801, 3169, 8269]

/-- `q` is not a prime `≡ 1 (mod 12)` outside the exceptions. -/
private def qSmall (q : ℕ) : Bool :=
  q % 12 != 1 || decide (q ≤ 1) || hasSmallFactor q || excList.contains q

private def qOK (X q : ℕ) : Bool := qSmall q || slotOK q X

private theorem qOK_of {X lo n q : ℕ}
    (h : (List.range n).all (fun i => qOK X (lo + i)) = true) (h1 : lo ≤ q) (h2 : q < lo + n) :
    qOK X q = true := by
  rw [List.all_eq_true] at h
  have := h (q - lo) (List.mem_range.mpr (by omega))
  rwa [show lo + (q - lo) = q by omega] at this

private theorem slotOK_of_qOK {X q : ℕ} (h : qOK X q = true) (hq : q.Prime) (h12 : q % 12 = 1)
    (hexc : q ∉ excList) : slotOK q X = true := by
  have h1 : ¬ q ≤ 1 := by have := hq.two_le; omega
  have hs : qSmall q = false := by simp [qSmall, h12, h1, hasSmallFactor_false hq, hexc]
  unfold qOK at h
  simpa [hs] using h

private theorem not_qSmall {q : ℕ} (hq : q.Prime) (h12 : q % 12 = 1) (hexc : q ∉ excList) :
    qSmall q = false := by
  have h1 : ¬ q ≤ 1 := by have := hq.two_le; omega
  simp [qSmall, h12, h1, hasSmallFactor_false hq, hexc]

private theorem cert_small : (List.range 157).all qSmall = true := by
  decide +kernel

private theorem cert_band1_0 :
    (List.range 2280).all (fun i => qOK 8836 (157 + i)) = true := by
  decide +kernel

private theorem cert_band1_1 :
    (List.range 2280).all (fun i => qOK 8836 (2437 + i)) = true := by
  decide +kernel

private theorem cert_band1_2 :
    (List.range 2280).all (fun i => qOK 8836 (4717 + i)) = true := by
  decide +kernel

private theorem cert_band1_3 :
    (List.range 2280).all (fun i => qOK 8836 (6997 + i)) = true := by
  decide +kernel


private theorem cert_band2 :
    (List.range 188).all (fun i => qOK 169 (9277 + i)) = true := by
  decide +kernel

private theorem cert_free : slotOK 1000000 169 = true := by
  decide +kernel

private theorem box_61_13 : ∀ a < 9, ∀ b < 15, 61 ^ a * 13 ^ b < 10 ^ 16 →
    rootIn [0, 3] (61 ^ a * 13 ^ b) = true := by
  decide +kernel

end RestrainedFour

open RestrainedFour

/-! ## The leaf `r = 61` -/

/-- **Restrained, leaf `r = 61`.** Under the hypotheses of `restrained_three_sq_cases`, the
configuration `r = 61`, `13^2 ∥ N`, `q ≡ 1 (mod 3)` is impossible. -/
theorem restrained_not_sixty_one {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (h3 : N.factorization 3 = 2) :
    ¬ (r = 61 ∧ N.factorization 13 = 2 ∧ q % 3 = 1) := by
  rintro ⟨rfl, h13, hq3⟩
  have hN0 := h.ne_zero
  have hq4 := (special_mod_four h hq hodd).1
  have hq12 : q % 12 = 1 := by omega
  have q3 : q ≠ 3 := by rintro rfl; norm_num at hq3
  have q13 : q ≠ 13 := by
    intro e; rw [e, h13, Nat.odd_iff] at hodd; norm_num at hodd
  have q61 : q ≠ 61 := Ne.symm hrq
  have mem : ∀ {p}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN0⟩
  have d3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have d13 : 13 ∣ N := OPNStarter.force_prime h.perfect Nat.prime_three h3 (by norm_num)
    (by norm_num) (by rw [sigma_prime_sq Nat.prime_three]; norm_num [phi3])
  have d61 : 61 ∣ N := OPNStarter.force_prime h.perfect (by norm_num : Nat.Prime 13) h13
    (by norm_num) (by norm_num) (by rw [sigma_prime_sq (by norm_num)]; norm_num [phi3])
  have dq : q ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  set K : Finset ℕ := {3, 13, 61, q} with hK
  have hKsub : K ⊆ N.primeFactors := by
    intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem Nat.prime_three d3
    · exact mem (by norm_num) d13
    · exact mem (by norm_num) d61
    · exact mem hq dq
  set T := N.primeFactors \ K with hT
  have hTmem : ∀ {t}, t ∈ T → t.Prime ∧ t ∣ N ∧ t ≠ 3 ∧ t ≠ 13 ∧ t ≠ 61 ∧ t ≠ q := by
    intro t ht
    obtain ⟨htN, htK⟩ := Finset.mem_sdiff.mp ht
    simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or] at htK
    exact ⟨Nat.prime_of_mem_primeFactors htN, Nat.dvd_of_mem_primeFactors htN, htK.1,
      htK.2.1, htK.2.2.1, htK.2.2.2⟩
  have toT : ∀ {p}, p.Prime → p ∣ N → p ≠ 3 → p ≠ 13 → p ≠ 61 → p ≠ q → p ∈ T := by
    intro p hp hd h3' h13' h61' hq'
    refine Finset.mem_sdiff.mpr ⟨mem hp hd, ?_⟩
    simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h3', h13', h61', hq'⟩
  have key2 : ∀ {t}, t ∈ T → N.factorization t = 2 := fun ht =>
    hsq _ (Finset.mem_sdiff.mp ht).1 (hTmem ht).2.2.2.2.2 (hTmem ht).2.2.2.2.1
  set O := T.filter (fun t => t % 3 = 1) with hO
  have memO : ∀ {t}, t ∈ O ↔ t ∈ T ∧ t % 3 = 1 := Finset.mem_filter
  -- at most one slot
  have hOcard : O.card ≤ 1 := by
    have hle := sum_padicValNat_sigma_le_factorization h.perfect Nat.prime_three (by norm_num)
      (insert 13 O)
    have h13O : 13 ∉ O := fun hm => (hTmem (memO.mp hm).1).2.2.2.1 rfl
    have hc : ∑ p ∈ O, padicValNat 3 (σ 1 (p ^ N.factorization p)) = O.card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hpT, hp1⟩ := memO.mp hp
      rw [key2 hpT, sigma_prime_sq (hTmem hpT).1, padicValNat_three_phi3, if_pos hp1]
    rw [Finset.sum_insert h13O, h13, sigma_prime_sq (by norm_num), padicValNat_three_phi3,
      if_pos (by norm_num), hc, h3] at hle
    omega
  have hOone : ∀ {x y}, x ∈ O → y ∈ O → x = y := fun hx hy =>
    Finset.card_le_one.mp hOcard _ hx _ hy
  -- prime factors of `σ(w^2)`
  have hstr : ∀ w ∈ T, ∀ d, d.Prime → d ∣ phi3 w →
      d = 3 ∨ d = 13 ∨ d = 61 ∨ d = q ∨ (d ∈ O ∧ d ≠ w) := by
    intro w hw d hd hdd
    obtain ⟨hwp, -, -, -, -, -⟩ := hTmem hw
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
    by_cases h13' : d = 13
    · exact Or.inr (Or.inl h13')
    by_cases h61' : d = 61
    · exact Or.inr (Or.inr (Or.inl h61'))
    by_cases hq' : d = q
    · exact Or.inr (Or.inr (Or.inr (Or.inl hq')))
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨memO.mpr ⟨toT hd hdN hd3 h13' h61' hq', hd1⟩, hdw⟩)))
  have nextO : ∀ w ∈ T, ∀ d, d.Prime → d ∣ phi3 w → d ≠ 3 → d ≠ 13 → d ≠ 61 → d ≠ q →
      d ∈ O := by
    intro w hw d hd hdd h3' h13' h61' hq'
    rcases hstr w hw d hd hdd with e | e | e | e | ⟨hdO, -⟩
    · exact absurd e h3'
    · exact absurd e h13'
    · exact absurd e h61'
    · exact absurd e hq'
    · exact hdO
  have bad : ∀ w ∈ O, ∀ d, d.Prime → d ∣ phi3 w → d ≠ 3 → d ≠ 13 → d ≠ 61 → d ≠ q →
      False := by
    intro w hw d hd hdd h3' h13' h61' hq'
    rcases hstr w (memO.mp hw).1 d hd hdd with e | e | e | e | ⟨hdO, hdw⟩
    · exact h3' e
    · exact h13' e
    · exact h61' e
    · exact hq' e
    · exact hdw (hOone hdO hw)
  have forced : ∀ p, p.Prime → p ∣ q + 1 → p ≠ 2 → p ∣ N := fun p hp hpd hp2 =>
    OPNStarter.force_prime h.perfect hq rfl hp hp2 (hpd.trans (succ_dvd_sigma_special hq hodd))
  -- the exceptional special primes
  have hexc : q ∉ excList := by
    intro hm
    simp only [excList, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e | e | e | e | e | e | e | e | e
    · exact q13 e
    · subst e
      have h19 : (19 : ℕ) ∈ O := memO.mpr ⟨toT (by norm_num)
        (forced 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), by norm_num⟩
      exact bad 19 h19 127 (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact q61 e
    · subst e
      have h37 : (37 : ℕ) ∈ O := memO.mpr ⟨toT (by norm_num)
        (forced 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), by norm_num⟩
      exact bad 37 h37 7 (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · subst e
      have h7 : (7 : ℕ) ∈ O := memO.mpr ⟨toT (by norm_num)
        (forced 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), by norm_num⟩
      exact bad 7 h7 19 (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · subst e
      have h5 : (5 : ℕ) ∈ T := toT (by norm_num)
        (forced 5 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
      have h31 := nextO 5 h5 31 (by norm_num) (by norm_num [phi3]) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      exact bad 31 h31 331 (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · subst e
      have h7 : (7 : ℕ) ∈ O := memO.mpr ⟨toT (by norm_num)
        (forced 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), by norm_num⟩
      exact bad 7 h7 19 (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · subst e
      have h17 : (17 : ℕ) ∈ T := toT (by norm_num)
        (forced 17 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
      have h307 := nextO 17 h17 307 (by norm_num) (by norm_num [phi3]) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      exact bad 307 h307 43 (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · subst e
      have h5 : (5 : ℕ) ∈ T := toT (by norm_num)
        (forced 5 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
      have h31 := nextO 5 h5 31 (by norm_num) (by norm_num [phi3]) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      exact bad 31 h31 331 (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · subst e
      have h5 : (5 : ℕ) ∈ T := toT (by norm_num)
        (forced 5 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
      have h31 := nextO 5 h5 31 (by norm_num) (by norm_num [phi3]) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      exact bad 31 h31 331 (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
  -- the shape of `σ(x^2)` for a slot `x`
  have slotRep : ∀ x ∈ O, phi3 x = 3 * (13 ^ (phi3 x / 3).factorization 13 *
      61 ^ (phi3 x / 3).factorization 61 * q ^ (phi3 x / 3).factorization q) := by
    intro x hx
    obtain ⟨hxT, hx3⟩ := memO.mp hx
    obtain ⟨he, hn3⟩ := phi3_div_three hx3
    have hn0 : phi3 x / 3 ≠ 0 := by
      intro h0; rw [h0] at he; unfold phi3 at he; omega
    have hsub : (phi3 x / 3).primeFactors ⊆ {13, 61, q} := by
      intro d hd
      have hdp := Nat.prime_of_mem_primeFactors hd
      have hdd := Nat.dvd_of_mem_primeFactors hd
      have hdx : d ∣ phi3 x := hdd.trans (Dvd.intro_left 3 he.symm)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hstr x hxT d hdp hdx with e | e | e | e | ⟨hdO, hdw⟩
      · subst e; exact absurd hdd hn3
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
      · exact absurd (hOone hdO hx) hdw
    exact he.trans (congrArg (3 * ·) (eq_three_pow hn0 (by norm_num) (fun e => q13 e.symm)
      (fun e => q61 e.symm) hsub))
  have slotX : ∀ X, slotOK q X = true → ∀ x ∈ O, X ≤ x := fun X hc x hx => by
    obtain ⟨hxT, hx3⟩ := memO.mp hx
    obtain ⟨hxp, -, -, h13', h61', hq'⟩ := hTmem hxT
    exact slot_ge hq.pos hc hxp hx3 h13' h61' hq' (slotRep x hx)
  -- the analytic core
  have core : ∀ Q X s u : ℕ, 2 ≤ s → 2 ≤ u → s ^ 2 ≤ Q → u ^ 2 ≤ X → Q ≤ q → 2 ≤ Q →
      169 ≤ X → X ≤ 10007 → (∀ x ∈ O, X ≤ x) →
      (13 / 9 : ℚ) * (183 / 169 * (61 / 60 * ((Q : ℚ) / ((Q : ℚ) - 1)))) <
        2 * (1 - (121 / 100 * (1 / ((X : ℚ) + 1)) +
          121 / 100 * (1 / 10 ^ 4 * (1 / (1 - 36 / 100) * (1 / (1 - 527 / 1000) * (1 * 1))) +
            (1 / (s : ℚ) + 1 / (u : ℚ)) * (1 / (1 - 129 / 1000) * (1 / (1 - 2774 / 10000) *
              (1 / (1 - 1 / (s : ℚ)) * (1 / (1 - 1 / (u : ℚ))))))))) → False := by
    intro Q X s u hs hu hsQ huX hQq hQ2 hX hX2 hOX hnum
    obtain ⟨x, hxp, hXx, hx13, hx61, hxq, hOx⟩ : ∃ x, x.Prime ∧ X ≤ x ∧ x ≠ 13 ∧ x ≠ 61 ∧
        x ≠ q ∧ O ⊆ {x} := by
      rcases O.eq_empty_or_nonempty with he | ⟨x, hx⟩
      · refine ⟨10007, by norm_num, hX2, by norm_num, by norm_num, ?_, by simp [he]⟩
        intro e; rw [← e] at hq12; norm_num at hq12
      · obtain ⟨hxT, -⟩ := memO.mp hx
        obtain ⟨hxp, -, -, h13', h61', hq'⟩ := hTmem hxT
        exact ⟨x, hxp, hOX x hx, h13', h61', hq', fun y hy => by
          rw [Finset.mem_singleton]; exact hOone hy hx⟩
    set O2 := T.filter (fun t => ¬ t % 3 = 1) with hO2
    have hS2 := rankin_tail O2 (g₁ := 61) (g₂ := 13) (g₃ := q) (g₄ := x) (B := 10 ^ 16)
      (α₁ := 129 / 1000) (α₂ := 2774 / 10000) (α₃ := 1 / (s : ℚ)) (α₄ := 1 / (u : ℚ))
      (β₁ := 36 / 100) (β₂ := 527 / 1000) (β := 1 / 10 ^ 4) hq hxp (by norm_num)
      (fun e => q61 e.symm) (fun e => hx61 e.symm) (fun e => q13 e.symm)
      (fun e => hx13 e.symm) (fun e => hxq e.symm)
      (by norm_num) (by norm_num) (by positivity) (by positivity)
      (by norm_num) (by norm_num) (inv_lt_one' hs) (inv_lt_one' hu)
      (by norm_num) (by norm_num) (weight_ok (by omega) (hsQ.trans hQq))
      (weight_ok (by omega) (huX.trans hXx))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by
        intro t ht
        obtain ⟨htT, ht1⟩ := Finset.mem_filter.mp ht
        obtain ⟨htp, htN, t3, t13, t61, tq⟩ := hTmem htT
        have ht2 : t % 3 = 2 := by
          have : t % 3 ≠ 0 := fun h0 => t3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three
            htp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
          omega
        have hsupp : (phi3 t).primeFactors ⊆ {61, 13, q, x} := by
          intro d hd
          have hdp := Nat.prime_of_mem_primeFactors hd
          have hdd := Nat.dvd_of_mem_primeFactors hd
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hstr t htT d hdp hdd with e | e | e | e | ⟨hdO, -⟩
          · subst e; have := (three_dvd_phi3_iff t).1 hdd; omega
          · exact Or.inr (Or.inl e)
          · exact Or.inl e
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp (hOx hdO))))
        refine ⟨?_, hsupp, fun hq' hx' => ?_⟩
        · by_contra hlt
          rw [not_le] at hlt
          rcases small_cases hlt ht2 with e | e | e
          · exact h.not_two_dvd (e ▸ htN)
          · have h31 := nextO t htT 31 (by norm_num) (by rw [e]; norm_num [phi3])
              (by norm_num) (by norm_num) (by norm_num)
              (fun e' => by rw [← e'] at hq12; norm_num at hq12)
            have := hOX 31 h31
            omega
          · exact absurd (e ▸ htp) (by norm_num)
        · have hV0 : phi3 t ≠ 0 := by unfold phi3; omega
          have hrep := eq_four_pow hV0 (by norm_num : (61 : ℕ) ≠ 13) (fun e => q61 e.symm)
            (fun e => hx61 e.symm) (fun e => q13 e.symm) (fun e => hx13 e.symm)
            (fun e => hxq e.symm) hsupp
          rw [Nat.factorization_eq_zero_of_not_dvd hq', Nat.factorization_eq_zero_of_not_dvd hx',
            pow_zero, pow_zero, mul_one, mul_one] at hrep
          by_contra hlt
          rw [not_le] at hlt
          have hpos : 0 < phi3 t := Nat.pos_of_ne_zero hV0
          have ha : (phi3 t).factorization 61 < 9 := exp_lt_of_pow (c := 61) (by norm_num) hpos
            ⟨13 ^ (phi3 t).factorization 13, hrep⟩ hlt (by norm_num)
          have hb : (phi3 t).factorization 13 < 15 := exp_lt_of_pow (c := 13) (by norm_num) hpos
            ⟨61 ^ (phi3 t).factorization 61, by rw [mul_comm]; exact hrep⟩ hlt (by norm_num)
          have hmem := mem_of_rootIn (box_61_13 _ ha _ hb (by rw [← hrep]; exact hlt)) hrep
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with e | e
          · exact absurd (e ▸ htp) (by norm_num)
          · exact t3 e)
    have hS1 : ∑ t ∈ O, (fv t - 1) ≤ 121 / 100 * (1 / ((X : ℚ) + 1)) := by
      rcases O.eq_empty_or_nonempty with he | ⟨y, hy⟩
      · rw [he, Finset.sum_empty]; positivity
      · have hOy : O = {y} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hy, fun z hz => hOone hz hy⟩
        rw [hOy, Finset.sum_singleton]
        have hXy := hOX y hy
        refine (fv_sub_le (by omega)).trans ?_
        have : (X : ℚ) ≤ y := by exact_mod_cast hXy
        gcongr
    have hsplit : ∑ t ∈ O, (fv t - 1) + ∑ t ∈ O2, (fv t - 1) = ∑ t ∈ T, (fv t - 1) :=
      Finset.sum_filter_add_sum_filter_not T _ _
    set c : ℕ → ℚ := fun p => if p = 3 then 13 / 9 else if p = 13 then 183 / 169 else
      if p = 61 then 61 / 60 else (Q : ℚ) / ((Q : ℚ) - 1) with hc
    have eq : c q = (Q : ℚ) / ((Q : ℚ) - 1) := by simp [hc, q3, q13, q61]
    refine abundancy_close h K hKsub c ?_ _ (fun t ht => key2 ht)
      (hsplit.symm.trans_le (add_le_add hS1 hS2)) ?_
    · intro p hp
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | hpq
      · rw [h3, abundancy_sq Nat.prime_three]; norm_num [hc, fv]
      · rw [h13, abundancy_sq (by norm_num)]; norm_num [hc, fv]
      · refine (abundancy_prime_pow_lt (by norm_num) _).le.trans (le_of_eq ?_)
        norm_num [hc]
      · rw [hpq, eq]
        refine (abundancy_prime_pow_lt hq _).le.trans ?_
        have hQ' : (2 : ℚ) ≤ Q := by exact_mod_cast hQ2
        have hQq' : (Q : ℚ) ≤ q := by exact_mod_cast hQq
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
    · rw [hK, Finset.prod_insert (by simp [Ne.symm q3]), Finset.prod_insert
        (by simp [Ne.symm q13]), Finset.prod_pair (Ne.symm q61), eq]
      have e3 : c 3 = 13 / 9 := by simp [hc]
      have e13 : c 13 = 183 / 169 := by simp [hc]
      have e61 : c 61 = 61 / 60 := by simp [hc]
      rw [e3, e13, e61]
      exact hnum
  -- dispatch on `q`
  have hq157 : 157 ≤ q := by
    by_contra hlt
    rw [not_le] at hlt
    have := (List.all_eq_true.mp cert_small) q (List.mem_range.mpr hlt)
    rw [not_qSmall hq hq12 hexc] at this
    exact absurd this (by decide)
  rcases Nat.lt_or_ge q 9277 with h1 | h1
  · exact core 157 8836 12 94 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq157
      (by norm_num) (by norm_num) (by norm_num)
      (slotX 8836 (slotOK_of_qOK (by
        rcases Nat.lt_or_ge q 2437 with c1 | c1
        · exact qOK_of cert_band1_0 hq157 (by omega)
        rcases Nat.lt_or_ge q 4717 with c2 | c2
        · exact qOK_of cert_band1_1 c1 (by omega)
        rcases Nat.lt_or_ge q 6997 with c3 | c3
        · exact qOK_of cert_band1_2 c2 (by omega)
        · exact qOK_of cert_band1_3 c3 (by omega)) hq hq12 hexc))
      (by norm_num)
  rcases Nat.lt_or_ge q 9465 with h2 | h2
  · exact core 9277 169 96 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1
      (by norm_num) (by norm_num) (by norm_num)
      (slotX 169 (slotOK_of_qOK (qOK_of cert_band2 h1 (by omega)) hq hq12 hexc))
      (by norm_num)
  refine core 9465 169 97 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h2
    (by norm_num) (by norm_num) (by norm_num) (fun x hx => ?_) (by norm_num)
  obtain ⟨hxT, hx3⟩ := memO.mp hx
  obtain ⟨hxp, -, -, h13', h61', hq'⟩ := hTmem hxT
  obtain ⟨he, -⟩ := phi3_div_three hx3
  by_cases hqd : q ∣ phi3 x
  · have hcop : q.Coprime 3 := (Nat.coprime_primes hq Nat.prime_three).mpr q3
    have hqm : q ∣ phi3 x / 3 := hcop.dvd_of_dvd_mul_left (he ▸ hqd)
    have hm0 : phi3 x / 3 ≠ 0 := by intro h0; rw [h0] at he; unfold phi3 at he; omega
    have hle : q ≤ phi3 x / 3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hqm
    by_contra hlt
    rw [not_le] at hlt
    have : phi3 x ≤ phi3 168 := phi3_strictMono.monotone (by omega)
    have h168 : phi3 168 = 28393 := by norm_num [phi3]
    omega
  · have hz : (phi3 x / 3).factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hqd (hd.trans (Dvd.intro_left 3 he.symm)))
    have hrep := slotRep x hx
    rw [hz, pow_zero] at hrep
    by_contra hlt
    rw [not_le] at hlt
    have := slot_ge (q := 1000000) (d := (phi3 x / 3).factorization 13)
      (a := (phi3 x / 3).factorization 61) (b := 0) (by norm_num) cert_free hxp hx3 h13' h61'
      (by omega) (by rw [pow_zero]; exact hrep)
    omega

/-! ## Sharpened case theorem -/

/-- **Restrained odd perfect numbers, sharpened again.** With the hypotheses of
`three_dvd_of_one_exception`, either the exceptional prime is `3` (with `v_3(N)` even, at least
`4`, `q ≡ 1 (mod 3)`, `5 ∤ N` and `7 ∤ N`), or `3^2 ∥ N` and `r = 13`. -/
theorem restrained_cases_four {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (r = 3 ∧ 4 ≤ N.factorization 3 ∧ Even (N.factorization 3) ∧ q % 3 = 1 ∧ ¬ 5 ∣ N ∧
      ¬ 7 ∣ N) ∨
    (N.factorization 3 = 2 ∧ r = 13) := by
  rcases restrained_cases_three h hq hodd hr hrq hsq with h1 | ⟨h3, h2 | h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h3, h2⟩
  · exact absurd h2 (restrained_not_sixty_one h hq hodd hrq hsq h3)

end OddPerfect

#print axioms OddPerfect.RestrainedFour.rankin_tail
#print axioms OddPerfect.RestrainedFour.abundancy_close
#print axioms OddPerfect.restrained_not_sixty_one
#print axioms OddPerfect.restrained_cases_four
