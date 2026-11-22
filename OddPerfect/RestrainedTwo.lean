import OddPerfect.Restrained

/-!
# Restrained odd perfect numbers divisible by 3: two more leaves

Setting of `restrained_three_sq_cases`: `N` is an odd perfect number with special prime `q`,
`r ≠ q` is a further prime, every other prime factor has exponent exactly 2, and `3^2 ∥ N`.

## The leaf `r = 97` (with `13^2, 61^2 ∥ N`) is impossible

`σ(13^2) = 3 · 61` and `σ(61^2) = 3 · 13 · 97` spend the `3`-adic budget. Hence `q ≡ 1 (mod 3)`
(otherwise `3 ∣ q + 1 ∣ σ(q^e)`), and every other prime factor `t` is an exact square with
`t ≡ 2 (mod 3)`. The prime factors of `σ(t^2)` lie in `{61, 97, q}`: the factor `13` is spent
by `σ(3^2)` and `σ(61^2)`, and at most one factor `61` is left after `σ(13^2)`.

* `q < 100`: then `q ∈ {37, 73}`, and `19 ∣ σ(37^e)`, `37 ∣ σ(73^e)` overflow the budget.
* `q ≥ 100`: write `σ(t^2) = 61^a 97^b q^c` with `a ≤ 1`. If `c = 0`, an exact kernel check of
  the twelve values `61^a 97^b` with `b < 6` shows `b ≥ 6`. Since `σ(t^2) < (t + 1)^2`,
  `1/(t+1) ≤ (13/100)^a (11/100)^b (1/10)^c`, and `t ↦ (a, b, c)` is injective. Summing these
  weights, `∑ (σ(t^2)/t^2 - 1) ≤ 0.171`, while the other components give at most
  `13/9 · 183/169 · 3783/3721 · 97/96 · 100/99 < 1.623`, so the abundancy stays below `2`.

## The leaf `r = 61` (with `13^2 ∥ N`) forces `q ≡ 1 (mod 3)`

If `q ≡ 2 (mod 3)`, then `σ(13^2)` and `σ(q^e)` spend the `3`-adic budget and `q` divides no
`σ(t^2)`, so every other prime factor `t` has `σ(t^2)` supported on `{13, 61}` with at most one
factor `13`. The exact check of `13^a 61^b` with `b < 4` leaves only `t = 3`, and the same
Rankin bound gives abundancy at most `13/9 · 183/169 · 61/60 · 5/4 / (1 - 0.0006) < 2`.

The main results are `restrained_not_97`, `restrained_sixty_one_mod_three`,
`restrained_three_sq_cases_two` and `restrained_cases_two`. The configurations they leave are
closed in `OddPerfect.RestrainedThree` (`q = 13, r = 7`), `OddPerfect.RestrainedFour` (`r = 61`)
and `OddPerfect.RestrainedFive` (`r = 13`).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace RestrainedTwo

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

/-- `∏ (1 + x_i) · (1 - ∑ x_i) ≤ 1` for nonnegative `x_i`. -/
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

/-! ## Rankin weights with exponent `1/2` -/

/-- If `a^i b^j c^k < (t + 1)^2` and the weights satisfy `α^2 a ≥ 1`, `β^2 b ≥ 1` and
`(γ^2 c)^k ≥ 1`, then `1/(t + 1) ≤ α^i β^j γ^k`. -/
private theorem inv_succ_le {t a b c i j k : ℕ} {α β γ : ℚ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (ga : 1 ≤ α ^ 2 * a) (gb : 1 ≤ β ^ 2 * b) (gc : 1 ≤ (γ ^ 2 * c) ^ k)
    (hlt : a ^ i * b ^ j * c ^ k < (t + 1) ^ 2) :
    1 / ((t : ℚ) + 1) ≤ α ^ i * β ^ j * γ ^ k := by
  set P := α ^ i * β ^ j * γ ^ k with hP
  have hP0 : 0 ≤ P := by positivity
  have hPV : 1 ≤ P ^ 2 * ((a ^ i * b ^ j * c ^ k : ℕ) : ℚ) := by
    have e : P ^ 2 * ((a ^ i * b ^ j * c ^ k : ℕ) : ℚ) =
        (α ^ 2 * a) ^ i * (β ^ 2 * b) ^ j * (γ ^ 2 * c) ^ k := by
      simp only [hP]; push_cast; ring
    rw [e]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ ga) (one_le_pow₀ gb)) gc
  have hVt : ((a ^ i * b ^ j * c ^ k : ℕ) : ℚ) < ((t : ℚ) + 1) ^ 2 := by exact_mod_cast hlt
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

/-- A positive integer whose prime factors lie in `{a, b, c}` is the product of the
corresponding prime powers. -/
private theorem eq_three_pow {V a b c : ℕ} (hV : V ≠ 0) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hsub : V.primeFactors ⊆ {a, b, c}) :
    V = a ^ V.factorization a * b ^ V.factorization b * c ^ V.factorization c := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hV]
  rw [Finsupp.prod_of_support_subset _ (s := {a, b, c}) (by rwa [Nat.support_factorization])
    _ (fun _ _ => pow_zero _)]
  rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc]
  ring

private theorem sum_pair_mul {γ : Type*} (s : Finset ℕ) (t : Finset γ) (f : ℕ → ℚ)
    (g : γ → ℚ) : ∑ u ∈ s ×ˢ t, f u.1 * g u.2 = (∑ i ∈ s, f i) * ∑ v ∈ t, g v := by
  rw [Finset.sum_product, Finset.sum_mul_sum]

/-- Summing the weights over an injective image in `{0, 1} × ℕ × ℕ`. -/
private theorem sum_weights_le (T : Finset ℕ) (π : ℕ → ℕ × ℕ × ℕ) (hinj : Set.InjOn π T)
    (h1 : ∀ t ∈ T, (π t).1 < 2) {α β γ : ℚ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hβ1 : β < 1) (hγ1 : γ < 1) :
    ∑ t ∈ T, α ^ (π t).1 * (β ^ (π t).2.1 * γ ^ (π t).2.2) ≤
      (1 + α) * (1 / (1 - β) * (1 / (1 - γ))) := by
  set F : ℕ × ℕ × ℕ → ℚ := fun u => α ^ u.1 * (β ^ u.2.1 * γ ^ u.2.2) with hF
  set K := (T.image π).sup (fun u => max u.2.1 u.2.2) + 1 with hK
  set box := Finset.range 2 ×ˢ Finset.range K ×ˢ Finset.range K with hbox
  have hsub : T.image π ⊆ box := by
    intro u hu
    have hle := Finset.le_sup (f := fun u : ℕ × ℕ × ℕ => max u.2.1 u.2.2) hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    have := h1 t ht
    simp only [hbox, Finset.mem_product, Finset.mem_range]
    omega
  have hF0 : ∀ u, 0 ≤ F u := fun u => by positivity
  have hsum : ∑ u ∈ box, F u = (∑ i ∈ Finset.range 2, α ^ i) *
      ((∑ i ∈ Finset.range K, β ^ i) * (∑ i ∈ Finset.range K, γ ^ i)) := by
    rw [hbox, sum_pair_mul _ _ (fun i => α ^ i) (fun v : ℕ × ℕ => β ^ v.1 * γ ^ v.2),
      sum_pair_mul _ _ (fun i => β ^ i) (fun i => γ ^ i)]
  have e2 : ∑ i ∈ Finset.range 2, α ^ i = 1 + α := by simp [Finset.sum_range_succ]
  have g1 := geom_partial_le hβ hβ1 K
  have g2 := geom_partial_le hγ hγ1 K
  have p1 : 0 ≤ ∑ i ∈ Finset.range K, β ^ i := Finset.sum_nonneg fun i _ => pow_nonneg hβ i
  have p2 : 0 ≤ ∑ i ∈ Finset.range K, γ ^ i := Finset.sum_nonneg fun i _ => pow_nonneg hγ i
  calc ∑ t ∈ T, α ^ (π t).1 * (β ^ (π t).2.1 * γ ^ (π t).2.2) = ∑ u ∈ T.image π, F u := by
        rw [Finset.sum_image fun x hx y hy h => hinj hx hy h]
    _ ≤ ∑ u ∈ box, F u := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hF0 u)
    _ ≤ _ := by
        rw [hsum, e2]
        have hα1 : 0 ≤ 1 + α := by linarith
        gcongr

/-- Rankin bound for the exact square components of a leaf. Every `t ∈ T` has `t ≥ 10` and
`σ(t^2) = g₁^a g₂^b g₃^c` with `a ≤ 1`; if `c = 0` then `b ≥ n`; if `c ≥ 1` the weight of
`g₃` is admissible. -/
private theorem tail_le (T : Finset ℕ) {g₁ g₂ g₃ n : ℕ} {α₁ α₂ α₃ : ℚ} (p3 : g₃.Prime)
    (h12 : g₁ ≠ g₂) (h13 : g₁ ≠ g₃) (h23 : g₂ ≠ g₃)
    (a1 : 0 ≤ α₁) (a2 : 0 ≤ α₂) (a3 : 0 ≤ α₃) (l2 : α₂ < 1) (l3 : α₃ < 1)
    (w1 : 1 ≤ α₁ ^ 2 * g₁) (w2 : 1 ≤ α₂ ^ 2 * g₂)
    (hT : ∀ t ∈ T, 10 ≤ t ∧ (phi3 t).primeFactors ⊆ {g₁, g₂, g₃} ∧
      (phi3 t).factorization g₁ ≤ 1 ∧ (¬ g₃ ∣ phi3 t → n ≤ (phi3 t).factorization g₂) ∧
      (g₃ ∣ phi3 t → 1 ≤ α₃ ^ 2 * g₃)) :
    ∑ t ∈ T, (fv t - 1) ≤
      121 / 100 * ((α₂ ^ n + α₃) * ((1 + α₁) * (1 / (1 - α₂) * (1 / (1 - α₃))))) := by
  set G := (1 + α₁) * (1 / (1 - α₂) * (1 / (1 - α₃))) with hG
  have hV0 : ∀ t, phi3 t ≠ 0 := fun t => by unfold phi3; omega
  have hrep : ∀ t ∈ T, phi3 t = g₁ ^ (phi3 t).factorization g₁ *
      g₂ ^ (phi3 t).factorization g₂ * g₃ ^ (phi3 t).factorization g₃ := fun t ht =>
    eq_three_pow (hV0 t) h12 h13 h23 (hT t ht).2.1
  have hw : ∀ t ∈ T, 1 / ((t : ℚ) + 1) ≤ α₁ ^ (phi3 t).factorization g₁ *
      α₂ ^ (phi3 t).factorization g₂ * α₃ ^ (phi3 t).factorization g₃ := by
    intro t ht
    have h3 : 1 ≤ (α₃ ^ 2 * g₃) ^ (phi3 t).factorization g₃ := by
      by_cases hd : g₃ ∣ phi3 t
      · exact one_le_pow₀ ((hT t ht).2.2.2.2 hd)
      · rw [Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
    have hlt : phi3 t < (t + 1) ^ 2 := phi3_lt_succ_sq (by have := (hT t ht).1; omega)
    rw [hrep t ht] at hlt
    exact inv_succ_le a1 a2 a3 w1 w2 h3 hlt
  have hfv : ∀ t ∈ T, fv t - 1 ≤ 121 / 100 * (1 / ((t : ℚ) + 1)) := fun t ht =>
    fv_sub_le (hT t ht).1
  set T1 := T.filter (fun t => g₃ ∣ phi3 t) with hT1
  set T0 := T.filter (fun t => ¬ g₃ ∣ phi3 t) with hT0
  set π0 : ℕ → ℕ × ℕ × ℕ := fun t =>
    ((phi3 t).factorization g₁, (phi3 t).factorization g₂ - n, 0) with hπ0
  set π1 : ℕ → ℕ × ℕ × ℕ := fun t =>
    ((phi3 t).factorization g₁, (phi3 t).factorization g₂, (phi3 t).factorization g₃ - 1)
    with hπ1
  have hc0 : ∀ t ∈ T0, (phi3 t).factorization g₃ = 0 := fun t ht =>
    Nat.factorization_eq_zero_of_not_dvd (Finset.mem_filter.mp ht).2
  have hn0 : ∀ t ∈ T0, n ≤ (phi3 t).factorization g₂ := fun t ht =>
    (hT t (Finset.mem_filter.mp ht).1).2.2.2.1 (Finset.mem_filter.mp ht).2
  have hc1 : ∀ t ∈ T1, 1 ≤ (phi3 t).factorization g₃ := fun t ht =>
    (p3.dvd_iff_one_le_factorization (hV0 t)).mp (Finset.mem_filter.mp ht).2
  have hinj0 : Set.InjOn π0 T0 := by
    intro x hx y hy hxy
    have hx' := Finset.mem_coe.mp hx
    have hy' := Finset.mem_coe.mp hy
    simp only [hπ0, Prod.mk.injEq] at hxy
    have hb : (phi3 x).factorization g₂ = (phi3 y).factorization g₂ := by
      have := hn0 x hx'; have := hn0 y hy'; omega
    have : phi3 x = phi3 y := by
      rw [hrep x (Finset.mem_filter.mp hx').1, hrep y (Finset.mem_filter.mp hy').1, hxy.1, hb,
        hc0 x hx', hc0 y hy']
    exact phi3_strictMono.injective this
  have hinj1 : Set.InjOn π1 T1 := by
    intro x hx y hy hxy
    have hx' := Finset.mem_coe.mp hx
    have hy' := Finset.mem_coe.mp hy
    simp only [hπ1, Prod.mk.injEq] at hxy
    have hc : (phi3 x).factorization g₃ = (phi3 y).factorization g₃ := by
      have := hc1 x hx'; have := hc1 y hy'; omega
    have : phi3 x = phi3 y := by
      rw [hrep x (Finset.mem_filter.mp hx').1, hrep y (Finset.mem_filter.mp hy').1, hxy.1,
        hxy.2.1, hc]
    exact phi3_strictMono.injective this
  have hS0 : ∑ t ∈ T0, 1 / ((t : ℚ) + 1) ≤ α₂ ^ n * G := by
    calc ∑ t ∈ T0, 1 / ((t : ℚ) + 1) ≤
          ∑ t ∈ T0, α₂ ^ n * (α₁ ^ (π0 t).1 * (α₂ ^ (π0 t).2.1 * α₃ ^ (π0 t).2.2)) := by
          refine Finset.sum_le_sum fun t ht => (hw t (Finset.mem_filter.mp ht).1).trans_eq ?_
          simp only [hπ0]
          obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hn0 t ht)
          rw [hc0 t ht, hm, Nat.add_sub_cancel_left, pow_add]
          ring
      _ = α₂ ^ n * ∑ t ∈ T0, α₁ ^ (π0 t).1 * (α₂ ^ (π0 t).2.1 * α₃ ^ (π0 t).2.2) := by
          rw [Finset.mul_sum]
      _ ≤ α₂ ^ n * G := by
          have := sum_weights_le T0 π0 hinj0 (fun t ht => by
            simp only [hπ0]; have := (hT t (Finset.mem_filter.mp ht).1).2.2.1; omega)
            a1 a2 a3 l2 l3
          exact mul_le_mul_of_nonneg_left this (pow_nonneg a2 n)
  have hS1 : ∑ t ∈ T1, 1 / ((t : ℚ) + 1) ≤ α₃ * G := by
    calc ∑ t ∈ T1, 1 / ((t : ℚ) + 1) ≤
          ∑ t ∈ T1, α₃ * (α₁ ^ (π1 t).1 * (α₂ ^ (π1 t).2.1 * α₃ ^ (π1 t).2.2)) := by
          refine Finset.sum_le_sum fun t ht => (hw t (Finset.mem_filter.mp ht).1).trans_eq ?_
          simp only [hπ1]
          obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hc1 t ht)
          rw [hm, Nat.add_sub_cancel_left, pow_add]
          ring
      _ = α₃ * ∑ t ∈ T1, α₁ ^ (π1 t).1 * (α₂ ^ (π1 t).2.1 * α₃ ^ (π1 t).2.2) := by
          rw [Finset.mul_sum]
      _ ≤ α₃ * G := by
          have := sum_weights_le T1 π1 hinj1 (fun t ht => by
            simp only [hπ1]; have := (hT t (Finset.mem_filter.mp ht).1).2.2.1; omega)
            a1 a2 a3 l2 l3
          exact mul_le_mul_of_nonneg_left this a3
  have hsplit : ∑ t ∈ T1, (fv t - 1) + ∑ t ∈ T0, (fv t - 1) = ∑ t ∈ T, (fv t - 1) :=
    Finset.sum_filter_add_sum_filter_not T _ _
  have hle1 : ∑ t ∈ T1, (fv t - 1) ≤ ∑ t ∈ T1, 121 / 100 * (1 / ((t : ℚ) + 1)) :=
    Finset.sum_le_sum fun t ht => hfv t (Finset.mem_filter.mp ht).1
  have hle0 : ∑ t ∈ T0, (fv t - 1) ≤ ∑ t ∈ T0, 121 / 100 * (1 / ((t : ℚ) + 1)) :=
    Finset.sum_le_sum fun t ht => hfv t (Finset.mem_filter.mp ht).1
  rw [← Finset.mul_sum] at hle1 hle0
  calc ∑ t ∈ T, (fv t - 1) = ∑ t ∈ T1, (fv t - 1) + ∑ t ∈ T0, (fv t - 1) := hsplit.symm
    _ ≤ 121 / 100 * (α₃ * G) + 121 / 100 * (α₂ ^ n * G) :=
        add_le_add (hle1.trans (mul_le_mul_of_nonneg_left hS1 (by norm_num)))
          (hle0.trans (mul_le_mul_of_nonneg_left hS0 (by norm_num)))
    _ = _ := by ring

/-! ## Closing a leaf by abundancy -/

/-- A leaf closes when the components over `K` have abundancy at most `∏ c`, every other prime
factor is an exact square, and `∑ (σ(t^2)/t^2 - 1) ≤ S` over the other prime factors with
`∏ c < 2 (1 - S)`. -/
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

/-! ## Exact check that small smooth values are not values of `phi3` -/

/-- Bisection with fuel for the largest `m` with `phi3 m ≤ V`; soundness below only uses
the monotonicity of `phi3`, so any output is acceptable. -/
private def lowRoot (V : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if phi3 ((lo + hi) / 2) ≤ V then lowRoot V f ((lo + hi) / 2) hi
    else lowRoot V f lo ((lo + hi) / 2)

/-- `V` lies strictly between `phi3 m` and `phi3 (m + 1)` for the bisection candidate `m`. -/
private def noRoot (V : ℕ) : Bool :=
  decide (phi3 (lowRoot V 48 0 (2 ^ 40)) < V) &&
    decide (V < phi3 (lowRoot V 48 0 (2 ^ 40) + 1))

private theorem ne_of_noRoot {V t : ℕ} (hV : noRoot V = true) : phi3 t ≠ V := by
  intro ht
  unfold noRoot at hV
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hV
  rw [← ht] at hV
  have h1 := phi3_strictMono.lt_iff_lt.mp hV.1
  have h2 := phi3_strictMono.lt_iff_lt.mp hV.2
  omega

private theorem box_61_97 : ∀ a < 2, ∀ b < 6, a + b ≠ 0 → noRoot (61 ^ a * 97 ^ b) = true := by
  decide +kernel

private theorem box_13_61 : ∀ a < 2, ∀ b < 4, a + b ≠ 0 → (a, b) ≠ (1, 0) →
    noRoot (13 ^ a * 61 ^ b) = true := by
  decide +kernel

/-! ## Small helpers -/

private theorem one_le_pv {x n : ℕ} (hx : x.Prime) (hn : n ≠ 0) (hd : x ∣ n) :
    1 ≤ padicValNat x n := by
  have := Fact.mk hx
  exact one_le_padicValNat_of_dvd hn hd

private theorem sigma_ne_zero' {p e : ℕ} (hp : p.Prime) : σ 1 (p ^ e) ≠ 0 :=
  (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'

private theorem small_cases {t : ℕ} (h1 : t < 10) (h2 : t % 3 = 2) :
    t = 2 ∨ t = 5 ∨ t = 8 := by
  omega

private theorem phi3_eq_one {t : ℕ} (h : phi3 t = 1) : t = 0 := by
  by_contra hc
  have := phi3_strictMono (show 0 < t by omega)
  rw [h] at this
  exact absurd this (by norm_num [phi3])

end RestrainedTwo

open RestrainedTwo

/-! ## The leaf `r = 97` -/

/-- **Restrained, leaf `r = 97`.** Under the hypotheses of `restrained_three_sq_cases`, the
configuration `r = 97` with `13^2 ∥ N` and `61^2 ∥ N` is impossible. -/
theorem restrained_not_97 {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (h3 : N.factorization 3 = 2) (h13 : N.factorization 13 = 2)
    (h61 : N.factorization 61 = 2) : r ≠ 97 := by
  rintro rfl
  have hq4 := (special_mod_four h hq hodd).1
  have hq13 : q ≠ 13 := by rintro rfl; rw [h13] at hodd; exact absurd hodd (by decide)
  have hq61 : q ≠ 61 := by rintro rfl; rw [h61] at hodd; exact absurd hodd (by decide)
  have hq3 : q ≠ 3 := by rintro rfl; norm_num at hq4
  have hq97 : q ≠ 97 := fun e => hrq e.symm
  have hN0 := h.ne_zero
  have mem : ∀ {p}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN0⟩
  have ord : ∀ {p}, p.Prime → p ∣ N → p ≠ q → p ≠ 97 → N.factorization p = 2 :=
    fun hp hd h1 h2 => hsq _ (mem hp hd) h1 h2
  have s3 : σ 1 (3 ^ N.factorization 3) = 13 := by
    rw [h3, sigma_prime_sq Nat.prime_three]; norm_num [phi3]
  have s13 : σ 1 (13 ^ N.factorization 13) = 183 := by
    rw [h13, sigma_prime_sq (by norm_num)]; norm_num [phi3]
  have s61 : σ 1 (61 ^ N.factorization 61) = 3783 := by
    rw [h61, sigma_prime_sq (by norm_num)]; norm_num [phi3]
  -- the `3`-adic budget is spent by `σ(13^2)` and `σ(61^2)`
  have ov3 : ∀ s, s.Prime → s ≠ 13 → s ≠ 61 → 3 ∣ σ 1 (s ^ N.factorization s) → False := by
    intro s hs hs13 hs61 hd
    have hle := sum_padicValNat_sigma_le_factorization h.perfect Nat.prime_three (by norm_num)
      {13, 61, s}
    rw [Finset.sum_insert (by simp [Ne.symm hs13]), Finset.sum_pair (Ne.symm hs61), h3, s13,
      s61] at hle
    have e1 := one_le_pv Nat.prime_three (by norm_num) (by norm_num : 3 ∣ 183)
    have e2 := one_le_pv Nat.prime_three (by norm_num) (by norm_num : 3 ∣ 3783)
    have e3 := one_le_pv Nat.prime_three (sigma_ne_zero' hs) hd
    omega
  -- the `13`-adic budget is spent by `σ(3^2)` and `σ(61^2)`
  have cap13 : ∀ t, t.Prime → t ≠ 3 → t ≠ 61 → 13 ∣ σ 1 (t ^ N.factorization t) → False := by
    intro t ht ht3 ht61 hd
    have hle := sum_padicValNat_sigma_le_factorization h.perfect (by norm_num : Nat.Prime 13)
      (by norm_num) {3, 61, t}
    rw [Finset.sum_insert (by simp [Ne.symm ht3]), Finset.sum_pair (Ne.symm ht61), h13, s3,
      s61] at hle
    have e1 := one_le_pv (by norm_num : Nat.Prime 13) (by norm_num) (by norm_num : 13 ∣ 13)
    have e2 := one_le_pv (by norm_num : Nat.Prime 13) (by norm_num) (by norm_num : 13 ∣ 3783)
    have e3 := one_le_pv (by norm_num : Nat.Prime 13) (sigma_ne_zero' ht) hd
    omega
  -- one factor `61` is spent by `σ(13^2)`
  have cap61 : ∀ t, t ≠ 13 → padicValNat 61 (σ 1 (t ^ N.factorization t)) ≤ 1 := by
    intro t ht13
    have hle := sum_padicValNat_sigma_le_factorization h.perfect (by norm_num : Nat.Prime 61)
      (by norm_num) {13, t}
    rw [Finset.sum_pair (Ne.symm ht13), h61, s13] at hle
    have e1 := one_le_pv (by norm_num : Nat.Prime 61) (by norm_num) (by norm_num : 61 ∣ 183)
    omega
  have d3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have d13 : 13 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have d61 : 61 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have d97 : 97 ∣ N := OPNStarter.force_prime h.perfect (by norm_num : Nat.Prime 61) rfl
    (by norm_num) (by norm_num) (by rw [s61]; norm_num)
  have dq : q ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have hqmod : q % 3 = 1 := by
    have h0 : q % 3 ≠ 0 := fun h0 => hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
    by_contra hc
    exact ov3 q hq hq13 hq61 ((Nat.dvd_of_mod_eq_zero (by omega : (q + 1) % 3 = 0)).trans
      (succ_dvd_sigma_special hq hodd))
  by_cases hq100 : q < 100
  · obtain ⟨k, rfl⟩ : ∃ k, q = 12 * k + 1 := ⟨q / 12, by omega⟩
    have hk9 : k < 9 := by omega
    interval_cases k
    · exact absurd hq (by norm_num)
    · exact hq13 rfl
    · exact absurd hq (by norm_num)
    · have d19 : 19 ∣ N := OPNStarter.force_prime h.perfect hq rfl (by norm_num) (by norm_num)
        ((by norm_num : 19 ∣ 12 * 3 + 1 + 1).trans (succ_dvd_sigma_special hq hodd))
      have e19 := ord (by norm_num) d19 (by norm_num) (by norm_num)
      exact ov3 19 (by norm_num) (by norm_num) (by norm_num)
        (by rw [e19, sigma_prime_sq (by norm_num)]; norm_num [phi3])
    · exact absurd hq (by norm_num)
    · exact hq61 rfl
    · have d37 : 37 ∣ N := OPNStarter.force_prime h.perfect hq rfl (by norm_num) (by norm_num)
        ((by norm_num : 37 ∣ 12 * 6 + 1 + 1).trans (succ_dvd_sigma_special hq hodd))
      have e37 := ord (by norm_num) d37 (by norm_num) (by norm_num)
      exact ov3 37 (by norm_num) (by norm_num) (by norm_num)
        (by rw [e37, sigma_prime_sq (by norm_num)]; norm_num [phi3])
    · exact absurd hq (by norm_num)
    · exact hq97 rfl
  rw [not_lt] at hq100
  set K : Finset ℕ := {3, 13, 61, 97, q} with hK
  have hKsub : K ⊆ N.primeFactors := by
    intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact mem Nat.prime_three d3
    · exact mem (by norm_num) d13
    · exact mem (by norm_num) d61
    · exact mem (by norm_num) d97
    · exact mem hq dq
  have hTmem : ∀ {t}, t ∈ N.primeFactors \ K → t.Prime ∧ t ∣ N ∧ t ≠ 3 ∧ t ≠ 13 ∧ t ≠ 61 ∧
      t ≠ 97 ∧ t ≠ q := by
    intro t ht
    obtain ⟨htN, htK⟩ := Finset.mem_sdiff.mp ht
    simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or] at htK
    exact ⟨Nat.prime_of_mem_primeFactors htN, Nat.dvd_of_mem_primeFactors htN, htK.1,
      htK.2.1, htK.2.2.1, htK.2.2.2.1, htK.2.2.2.2⟩
  have key2 : ∀ {t}, t ∈ N.primeFactors \ K → N.factorization t = 2 := fun ht => by
    obtain ⟨htp, htd, -, -, -, t97, tq⟩ := hTmem ht
    exact ord htp htd tq t97
  have mod2 : ∀ {t}, t ∈ N.primeFactors \ K → t % 3 = 2 := by
    intro t ht
    obtain ⟨htp, -, t3, t13, t61, -, -⟩ := hTmem ht
    have h0 : t % 3 ≠ 0 := fun h0 => t3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three htp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
    by_contra hc
    exact ov3 t htp t13 t61
      (by rw [key2 ht, sigma_prime_sq htp]; exact (three_dvd_phi3_iff t).2 (by omega))
  have supp : ∀ {t}, t ∈ N.primeFactors \ K → (phi3 t).primeFactors ⊆ {61, 97, q} := by
    intro t ht d hd
    obtain ⟨htp, -, t3, -, t61, -, -⟩ := hTmem ht
    have hdp := Nat.prime_of_mem_primeFactors hd
    have hdd := Nat.dvd_of_mem_primeFactors hd
    have ht2 := mod2 ht
    have hd3 : d ≠ 3 := by rintro rfl; have := (three_dvd_phi3_iff t).1 hdd; omega
    have hd2 : d ≠ 2 := by rintro rfl; have := Nat.odd_iff.mp (phi3_odd t); omega
    have hdN : d ∣ N := OPNStarter.force_prime h.perfect htp (key2 ht) hdp hd2
      (by rw [sigma_prime_sq htp]; exact hdd)
    have hd13 : d ≠ 13 := by
      rintro rfl
      exact cap13 t htp t3 t61 (by rw [key2 ht, sigma_prime_sq htp]; exact hdd)
    have hd1 := prime_dvd_phi3_mod_three hdp hd3 hdd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hc
    simp only [not_or] at hc
    have hdT : d ∈ N.primeFactors \ K := Finset.mem_sdiff.mpr ⟨mem hdp hdN, by
      simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hd3, hd13, hc.1, hc.2.1, hc.2.2⟩⟩
    have := mod2 hdT
    omega
  have hS := tail_le (N.primeFactors \ K) (g₁ := 61) (g₂ := 97) (g₃ := q) (n := 6)
    (α₁ := 13 / 100) (α₂ := 11 / 100) (α₃ := 1 / 10) hq (by norm_num) (by omega) (by omega)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by
      intro t ht
      obtain ⟨htp, -, t3, t13, -, -, tq⟩ := hTmem ht
      have ht2 := key2 ht
      have hcap : (phi3 t).factorization 61 ≤ 1 := by
        have := cap61 t t13
        rwa [ht2, sigma_prime_sq htp, ← Nat.factorization_def (phi3 t) (p := 61) (by norm_num)]
          at this
      refine ⟨?_, supp ht, hcap, ?_, fun _ => ?_⟩
      · by_contra hlt
        rw [not_le] at hlt
        have hm := mod2 ht
        have hN2 := h.not_two_dvd
        have hdvd := Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp ht).1
        rcases small_cases hlt hm with e | e | e
        · exact hN2 (e ▸ hdvd)
        · have h31 : 31 ∈ (phi3 t).primeFactors := by
            rw [e]
            exact Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num [phi3], by norm_num [phi3]⟩
          have h' : (31 : ℕ) ∈ ({61, 97, q} : Finset ℕ) := Finset.mem_of_subset (supp ht) h31
          simp only [Finset.mem_insert, Finset.mem_singleton] at h'
          rcases h' with h' | h' | h'
          · norm_num at h'
          · norm_num at h'
          · rw [← h'] at hq100; norm_num at hq100
        · exact absurd (e ▸ htp) (by norm_num)
      · intro hnd
        by_contra hb
        rw [not_le] at hb
        have hrep := eq_three_pow (V := phi3 t) (by unfold phi3; omega)
          (by norm_num : (61 : ℕ) ≠ 97) (by omega : (61 : ℕ) ≠ q) (by omega : (97 : ℕ) ≠ q)
          (supp ht)
        rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero, mul_one] at hrep
        by_cases h0 : (phi3 t).factorization 61 + (phi3 t).factorization 97 = 0
        · have ha : (phi3 t).factorization 61 = 0 := by omega
          have hb' : (phi3 t).factorization 97 = 0 := by omega
          rw [ha, hb'] at hrep
          have := phi3_eq_one hrep
          subst this
          exact absurd htp (by norm_num)
        · exact ne_of_noRoot (box_61_97 _ (by omega) _ hb h0) hrep
      · have : (100 : ℚ) ≤ q := by exact_mod_cast hq100
        rw [show ((1 : ℚ) / 10) ^ 2 = 1 / 100 by norm_num]
        linarith)
  set c : ℕ → ℚ := fun p => if p = 3 then 13 / 9 else if p = 13 then 183 / 169 else
    if p = 61 then 3783 / 3721 else if p = 97 then 97 / 96 else 100 / 99 with hc
  refine close h K hKsub c ?_ _ (fun t ht => key2 ht) hS ?_
  · intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | hpq
    · rw [h3, abundancy_sq Nat.prime_three]; norm_num [hc, fv]
    · rw [h13, abundancy_sq (by norm_num)]; norm_num [hc, fv]
    · rw [h61, abundancy_sq (by norm_num)]; norm_num [hc, fv]
    · refine (abundancy_prime_pow_lt (by norm_num) _).le.trans (le_of_eq ?_)
      norm_num [hc]
    · rw [hpq]
      refine (abundancy_prime_pow_lt hq _).le.trans ?_
      have hcq : c q = 100 / 99 := by simp [hc, hq3, hq13, hq61, hq97]
      rw [hcq]
      have hq' : (100 : ℚ) ≤ q := by exact_mod_cast hq100
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
  · have hcq : c q = 100 / 99 := by simp [hc, hq3, hq13, hq61, hq97]
    rw [hK, Finset.prod_insert (by simp [Ne.symm hq3]), Finset.prod_insert (by simp [Ne.symm hq13]),
      Finset.prod_insert (by simp [Ne.symm hq61]),
      Finset.prod_insert (by simp [Ne.symm hq97]), Finset.prod_singleton, hcq]
    norm_num [hc]

/-! ## The leaf `r = 61`: the special prime is `1 (mod 3)` -/

/-- **Restrained, leaf `r = 61`.** Under the hypotheses of `restrained_three_sq_cases`, if
`r = 61` and `13^2 ∥ N`, then `q ≡ 1 (mod 3)`. -/
theorem restrained_sixty_one_mod_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (h3 : N.factorization 3 = 2) (hr : r = 61) (h13 : N.factorization 13 = 2) :
    q % 3 = 1 := by
  subst hr
  have hq4 := (special_mod_four h hq hodd).1
  have hq3 : q ≠ 3 := by rintro rfl; norm_num at hq4
  have h0 : q % 3 ≠ 0 := fun h0 => hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
    (Nat.dvd_of_mod_eq_zero h0)).symm
  by_contra hc
  have hq2 : q % 3 = 2 := by omega
  have hq13 : q ≠ 13 := by rintro rfl; norm_num at hq2
  have hq61 : q ≠ 61 := fun e => hrq e.symm
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hN0 := h.ne_zero
  have mem : ∀ {p}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN0⟩
  have ord : ∀ {p}, p.Prime → p ∣ N → p ≠ q → p ≠ 61 → N.factorization p = 2 :=
    fun hp hd h1 h2 => hsq _ (mem hp hd) h1 h2
  have s3 : σ 1 (3 ^ N.factorization 3) = 13 := by
    rw [h3, sigma_prime_sq Nat.prime_three]; norm_num [phi3]
  have s13 : σ 1 (13 ^ N.factorization 13) = 183 := by
    rw [h13, sigma_prime_sq (by norm_num)]; norm_num [phi3]
  have sq3 : 3 ∣ σ 1 (q ^ N.factorization q) :=
    (Nat.dvd_of_mod_eq_zero (by omega : (q + 1) % 3 = 0)).trans (succ_dvd_sigma_special hq hodd)
  -- the `3`-adic budget is spent by `σ(13^2)` and `σ(q^e)`
  have ov3 : ∀ s, s.Prime → s ≠ 13 → s ≠ q → 3 ∣ σ 1 (s ^ N.factorization s) → False := by
    intro s hs hs13 hsq' hd
    have hle := sum_padicValNat_sigma_le_factorization h.perfect Nat.prime_three (by norm_num)
      {13, q, s}
    rw [Finset.sum_insert (by simp [Ne.symm hs13, Ne.symm hq13]), Finset.sum_pair (Ne.symm hsq'),
      h3, s13] at hle
    have e1 := one_le_pv Nat.prime_three (by norm_num) (by norm_num : 3 ∣ 183)
    have e2 := one_le_pv Nat.prime_three (sigma_ne_zero' hq) sq3
    have e3 := one_le_pv Nat.prime_three (sigma_ne_zero' hs) hd
    omega
  -- one factor `13` is spent by `σ(3^2)`
  have cap13 : ∀ t, t ≠ 3 → padicValNat 13 (σ 1 (t ^ N.factorization t)) ≤ 1 := by
    intro t ht3
    have hle := sum_padicValNat_sigma_le_factorization h.perfect (by norm_num : Nat.Prime 13)
      (by norm_num) {3, t}
    rw [Finset.sum_pair (Ne.symm ht3), h13, s3] at hle
    have e1 := one_le_pv (by norm_num : Nat.Prime 13) (by norm_num) (by norm_num : 13 ∣ 13)
    omega
  have d3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have d13 : 13 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have d61 : 61 ∣ N := OPNStarter.force_prime h.perfect (by norm_num : Nat.Prime 13) rfl
    (by norm_num) (by norm_num) (by rw [s13]; norm_num)
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
  have hTmem : ∀ {t}, t ∈ N.primeFactors \ K → t.Prime ∧ t ∣ N ∧ t ≠ 3 ∧ t ≠ 13 ∧ t ≠ 61 ∧
      t ≠ q := by
    intro t ht
    obtain ⟨htN, htK⟩ := Finset.mem_sdiff.mp ht
    simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or] at htK
    exact ⟨Nat.prime_of_mem_primeFactors htN, Nat.dvd_of_mem_primeFactors htN, htK.1,
      htK.2.1, htK.2.2.1, htK.2.2.2⟩
  have key2 : ∀ {t}, t ∈ N.primeFactors \ K → N.factorization t = 2 := fun ht => by
    obtain ⟨htp, htd, -, -, t61, tq⟩ := hTmem ht
    exact ord htp htd tq t61
  have mod2 : ∀ {t}, t ∈ N.primeFactors \ K → t % 3 = 2 := by
    intro t ht
    obtain ⟨htp, -, t3, t13, -, tq⟩ := hTmem ht
    have h0 : t % 3 ≠ 0 := fun h0 => t3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three htp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
    by_contra hc
    exact ov3 t htp t13 tq
      (by rw [key2 ht, sigma_prime_sq htp]; exact (three_dvd_phi3_iff t).2 (by omega))
  have supp : ∀ {t}, t ∈ N.primeFactors \ K → (phi3 t).primeFactors ⊆ {13, 61, q} := by
    intro t ht d hd
    obtain ⟨htp, -, -, -, -, -⟩ := hTmem ht
    have hdp := Nat.prime_of_mem_primeFactors hd
    have hdd := Nat.dvd_of_mem_primeFactors hd
    have ht2 := mod2 ht
    have hd3 : d ≠ 3 := by rintro rfl; have := (three_dvd_phi3_iff t).1 hdd; omega
    have hd2 : d ≠ 2 := by rintro rfl; have := Nat.odd_iff.mp (phi3_odd t); omega
    have hdN : d ∣ N := OPNStarter.force_prime h.perfect htp (key2 ht) hdp hd2
      (by rw [sigma_prime_sq htp]; exact hdd)
    have hd1 := prime_dvd_phi3_mod_three hdp hd3 hdd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hc
    simp only [not_or] at hc
    have hdT : d ∈ N.primeFactors \ K := Finset.mem_sdiff.mpr ⟨mem hdp hdN, by
      simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hd3, hc.1, hc.2.1, hc.2.2⟩⟩
    have := mod2 hdT
    omega
  have qnd : ∀ t, ¬ q ∣ phi3 t := fun t hd => by
    have := prime_dvd_phi3_mod_three hq hq3 hd
    omega
  have hS := tail_le (N.primeFactors \ K) (g₁ := 13) (g₂ := 61) (g₃ := q) (n := 4)
    (α₁ := 3 / 10) (α₂ := 13 / 100) (α₃ := 0) hq (by norm_num) hq13.symm hq61.symm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by
      intro t ht
      obtain ⟨htp, -, t3, -, -, -⟩ := hTmem ht
      have ht2 := key2 ht
      have hcap : (phi3 t).factorization 13 ≤ 1 := by
        have := cap13 t t3
        rwa [ht2, sigma_prime_sq htp, ← Nat.factorization_def (phi3 t) (p := 13) (by norm_num)]
          at this
      refine ⟨?_, supp ht, hcap, ?_, fun hd => absurd hd (qnd t)⟩
      · by_contra hlt
        rw [not_le] at hlt
        have hm := mod2 ht
        have hN2 := h.not_two_dvd
        have hdvd := Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp ht).1
        rcases small_cases hlt hm with e | e | e
        · exact hN2 (e ▸ hdvd)
        · have h31 : 31 ∈ (phi3 t).primeFactors := by
            rw [e]
            exact Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num [phi3], by norm_num [phi3]⟩
          have h' : (31 : ℕ) ∈ ({13, 61, q} : Finset ℕ) := Finset.mem_of_subset (supp ht) h31
          simp only [Finset.mem_insert, Finset.mem_singleton] at h'
          rcases h' with h' | h' | h'
          · norm_num at h'
          · norm_num at h'
          · rw [← h'] at hq2; norm_num at hq2
        · exact absurd (e ▸ htp) (by norm_num)
      · intro hnd
        by_contra hb
        rw [not_le] at hb
        have hrep := eq_three_pow (V := phi3 t) (by unfold phi3; omega)
          (by norm_num : (13 : ℕ) ≠ 61) hq13.symm hq61.symm (supp ht)
        rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero, mul_one] at hrep
        by_cases h0 : (phi3 t).factorization 13 + (phi3 t).factorization 61 = 0
        · have ha : (phi3 t).factorization 13 = 0 := by omega
          have hb' : (phi3 t).factorization 61 = 0 := by omega
          rw [ha, hb'] at hrep
          have := phi3_eq_one hrep
          subst this
          exact absurd htp (by norm_num)
        by_cases h1 : (phi3 t).factorization 13 = 1 ∧ (phi3 t).factorization 61 = 0
        · rw [h1.1, h1.2] at hrep
          have : phi3 t = phi3 3 := by rw [hrep]; norm_num [phi3]
          exact t3 (phi3_strictMono.injective this)
        · exact ne_of_noRoot (box_13_61 _ (by omega) _ hb h0
            (by simp only [ne_eq, Prod.mk.injEq]; omega)) hrep)
  set c : ℕ → ℚ := fun p => if p = 3 then 13 / 9 else if p = 13 then 183 / 169 else
    if p = 61 then 61 / 60 else 5 / 4 with hc
  refine close h K hKsub c ?_ _ (fun t ht => key2 ht) hS ?_
  · intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | hpq
    · rw [h3, abundancy_sq Nat.prime_three]; norm_num [hc, fv]
    · rw [h13, abundancy_sq (by norm_num)]; norm_num [hc, fv]
    · refine (abundancy_prime_pow_lt (by norm_num) _).le.trans (le_of_eq ?_)
      norm_num [hc]
    · rw [hpq]
      refine (abundancy_prime_pow_lt hq _).le.trans ?_
      have hcq : c q = 5 / 4 := by simp [hc, hq3, hq13, hq61]
      rw [hcq]
      have hq' : (5 : ℚ) ≤ q := by exact_mod_cast hq5
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
  · have hcq : c q = 5 / 4 := by simp [hc, hq3, hq13, hq61]
    rw [hK, Finset.prod_insert (by simp [Ne.symm hq3]),
      Finset.prod_insert (by simp [Ne.symm hq13]),
      Finset.prod_insert (by simp [Ne.symm hq61]), Finset.prod_singleton, hcq]
    norm_num [hc]

/-! ## Sharpened case theorems -/

/-- **Restrained, `3` ordinary, sharpened.** With the hypotheses of
`restrained_three_sq_cases`, the pair `(q, r)` is one of three configurations, and in the
configuration `r = 61` the special prime is `1 (mod 3)`. -/
theorem restrained_three_sq_cases_two {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (h3 : N.factorization 3 = 2) :
    r = 13 ∨ (q = 13 ∧ r = 7) ∨ (r = 61 ∧ N.factorization 13 = 2 ∧ q % 3 = 1) := by
  rcases restrained_three_sq_cases h hq hodd hr hrq hsq h3 with
    h1 | h2 | ⟨hr61, h13⟩ | ⟨hr97, h13, h61⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨hr61, h13,
      restrained_sixty_one_mod_three h hq hodd hrq hsq h3 hr61 h13⟩)
  · exact absurd hr97 (restrained_not_97 h hq hodd hrq hsq h3 h13 h61)

/-- **Restrained odd perfect numbers, sharpened.** With the hypotheses of
`three_dvd_of_one_exception`, either the exceptional prime is `3` (with `v_3(N)` even, at least
`4`, `q ≡ 1 (mod 3)`, `5 ∤ N` and `7 ∤ N`), or `3^2 ∥ N` and `(q, r)` is one of the three
configurations of `restrained_three_sq_cases_two`. -/
theorem restrained_cases_two {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (r = 3 ∧ 4 ≤ N.factorization 3 ∧ Even (N.factorization 3) ∧ q % 3 = 1 ∧ ¬ 5 ∣ N ∧
      ¬ 7 ∣ N) ∨
    (N.factorization 3 = 2 ∧ (r = 13 ∨ (q = 13 ∧ r = 7) ∨
      (r = 61 ∧ N.factorization 13 = 2 ∧ q % 3 = 1))) := by
  rcases restrained_cases h hq hodd hr hrq hsq with h1 | ⟨h3, -⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h3, restrained_three_sq_cases_two h hq hodd hr hrq hsq h3⟩

end OddPerfect

#print axioms OddPerfect.restrained_not_97
#print axioms OddPerfect.restrained_sixty_one_mod_three
#print axioms OddPerfect.restrained_three_sq_cases_two
#print axioms OddPerfect.restrained_cases_two
