import OddPerfect.RestrainedFour
import OddPerfect.Pratt

/-!
# Restrained odd perfect numbers divisible by 3: the leaf `r = 13`

Setting of `restrained_three_sq_cases`: `N` is an odd perfect number with special prime `q`,
`r ≠ q` is a further prime, every other prime factor has exponent exactly 2, and `3^2 ∥ N`.
This file shows that `r = 13` is impossible, which leaves only the exceptional prime `r = 3`.

Here `13 ∣ N` (from `σ(3^2) = 13`) with a free exponent. Let `K = {3, 13, q}` and let `T` be
the other prime factors, all exact squares, split into the slots `O` (primes `≡ 1 (mod 3)`)
and the rest. The 3-adic ledger over `{q} ∪ O` gives `|O| ≤ 2`, and `|O| ≤ 1` when
`q ≡ 2 (mod 3)`.

* `q ≡ 2 (mod 3)`: `q` divides no `σ(t^2)`, so a slot `x` has `σ(x^2) = 3 · 13^a`; a kernel
  check gives `x ≥ 10^6`, and `rankin_tail3` closes the abundancy bound.
* `q ≡ 1 (mod 12)`: forcing kill trees (`check`, sound by `check_sound`) refute every prime
  `q < 337` and, for `q ≥ 337`, every slot below `1225`. The forced primes are certified by
  a Pratt certificate. Then `rankin_tail3` with the generators `13, q` and the two slots
  closes the bound.

The exponents of `13` and `q` enter only through the bound `p/(p - 1)`.

Main results: `restrained_not_thirteen` and `restrained_exception_eq_three`.

The conclusion `r = 3` is the first half of Theorem 1 of Ochem and Zelinsky (arXiv 2607.19746,
2026), whose second half is `v_3(N) ≥ 2.3 · 10^10`. The proof here uses neither Nielsen's bound
`ω(N) ≥ 10` nor results on the Nagell-Ljunggren equation, which their proof uses.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open RestrainedFour (fv abundancy_close)

namespace RestrainedFive

private theorem abundancy_sq {p : ℕ} (hp : p.Prime) : abundancy (p ^ 2) = fv p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [abundancy_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fv]
  field_simp
  ring


private theorem fv_sub_le {s : ℕ} (hs : 10 ≤ s) :
    fv s - 1 ≤ 121 / 100 * (1 / ((s : ℚ) + 1)) := by
  have hs' : (10 : ℚ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℚ) < s := by linarith
  unfold fv
  rw [div_sub_one (pow_pos hs0 2).ne', mul_one_div,
    div_le_div_iff₀ (pow_pos hs0 2) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs') (by positivity : (0 : ℚ) ≤ 21 * s + 10)]


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

/-! ## Rankin bound with one floor generator -/

/-- Rankin bound for a set of exact squares `t ≡ 2 (mod 3)` with one floor generator:
`σ(t^2)` is supported on `{g₁, g₂, g₃, g₄}`, and when none of the primes `g₂, g₃, g₄`
divides it, `σ(t^2) ≥ B`. -/
theorem rankin_tail3 (T : Finset ℕ) {g₁ g₂ g₃ g₄ B : ℕ} {α₁ α₂ α₃ α₄ β₁ β : ℚ}
    (p2 : g₂.Prime) (p3 : g₃.Prime) (p4 : g₄.Prime)
    (h12 : g₁ ≠ g₂) (h13 : g₁ ≠ g₃) (h14 : g₁ ≠ g₄) (h23 : g₂ ≠ g₃) (h24 : g₂ ≠ g₄)
    (h34 : g₃ ≠ g₄)
    (a1 : 0 ≤ α₁) (a2 : 0 ≤ α₂) (a3 : 0 ≤ α₃) (a4 : 0 ≤ α₄)
    (l1 : α₁ < 1) (l2 : α₂ < 1) (l3 : α₃ < 1) (l4 : α₄ < 1)
    (w1 : 1 ≤ α₁ ^ 2 * g₁) (w2 : 1 ≤ α₂ ^ 2 * g₂) (w3 : 1 ≤ α₃ ^ 2 * g₃) (w4 : 1 ≤ α₄ ^ 2 * g₄)
    (b1 : 0 ≤ β₁) (bβ : 0 ≤ β) (m1 : β₁ < 1) (v1 : 1 ≤ β₁ ^ 4 * g₁) (vB : 1 ≤ β ^ 4 * B)
    (hT : ∀ t ∈ T, 10 ≤ t ∧ (phi3 t).primeFactors ⊆ {g₁, g₂, g₃, g₄} ∧
      (¬ g₂ ∣ phi3 t → ¬ g₃ ∣ phi3 t → ¬ g₄ ∣ phi3 t → B ≤ phi3 t)) :
    ∑ t ∈ T, (fv t - 1) ≤ 121 / 100 * (β * (1 / (1 - β₁) * (1 * (1 * 1))) +
      (α₂ + α₃ + α₄) * (1 / (1 - α₁) * (1 / (1 - α₂) * (1 / (1 - α₃) * (1 / (1 - α₄)))))) := by
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
  set Ta := T.filter (fun t => g₂ ∣ phi3 t) with hTa
  set Tr := T.filter (fun t => ¬ g₂ ∣ phi3 t) with hTr
  set Tb := Tr.filter (fun t => g₃ ∣ phi3 t) with hTb
  set Ts := Tr.filter (fun t => ¬ g₃ ∣ phi3 t) with hTs
  set Tc := Ts.filter (fun t => g₄ ∣ phi3 t) with hTc
  set T0 := Ts.filter (fun t => ¬ g₄ ∣ phi3 t) with hT0
  have memTa : ∀ {t}, t ∈ Ta → t ∈ T ∧ 1 ≤ (phi3 t).factorization g₂ := fun ht =>
    ⟨(Finset.mem_filter.mp ht).1,
      (p2.dvd_iff_one_le_factorization (hV0 _)).mp (Finset.mem_filter.mp ht).2⟩
  have memTb : ∀ {t}, t ∈ Tb → t ∈ T ∧ (phi3 t).factorization g₂ = 0 ∧
      1 ≤ (phi3 t).factorization g₃ := fun ht => by
    obtain ⟨htr, h3⟩ := Finset.mem_filter.mp ht
    obtain ⟨htT, h2⟩ := Finset.mem_filter.mp htr
    exact ⟨htT, Nat.factorization_eq_zero_of_not_dvd h2,
      (p3.dvd_iff_one_le_factorization (hV0 _)).mp h3⟩
  have memTc : ∀ {t}, t ∈ Tc → t ∈ T ∧ (phi3 t).factorization g₂ = 0 ∧
      (phi3 t).factorization g₃ = 0 ∧ 1 ≤ (phi3 t).factorization g₄ := fun ht => by
    obtain ⟨hts, h4⟩ := Finset.mem_filter.mp ht
    obtain ⟨htr, h3⟩ := Finset.mem_filter.mp hts
    obtain ⟨htT, h2⟩ := Finset.mem_filter.mp htr
    exact ⟨htT, Nat.factorization_eq_zero_of_not_dvd h2,
      Nat.factorization_eq_zero_of_not_dvd h3, (p4.dvd_iff_one_le_factorization (hV0 _)).mp h4⟩
  have memT0 : ∀ {t}, t ∈ T0 → t ∈ T ∧ (phi3 t).factorization g₂ = 0 ∧
      (phi3 t).factorization g₃ = 0 ∧ (phi3 t).factorization g₄ = 0 ∧ B ≤ phi3 t :=
    fun ht => by
    obtain ⟨hts, h4⟩ := Finset.mem_filter.mp ht
    obtain ⟨htr, h3⟩ := Finset.mem_filter.mp hts
    obtain ⟨htT, h2⟩ := Finset.mem_filter.mp htr
    exact ⟨htT, Nat.factorization_eq_zero_of_not_dvd h2,
      Nat.factorization_eq_zero_of_not_dvd h3, Nat.factorization_eq_zero_of_not_dvd h4,
      (hT _ htT).2.2 h2 h3 h4⟩
  set πa : ℕ → ℕ × ℕ × ℕ × ℕ := fun t => ((phi3 t).factorization g₁,
    (phi3 t).factorization g₂ - 1, (phi3 t).factorization g₃, (phi3 t).factorization g₄)
    with hπa
  set πb : ℕ → ℕ × ℕ × ℕ × ℕ := fun t => ((phi3 t).factorization g₁, 0,
    (phi3 t).factorization g₃ - 1, (phi3 t).factorization g₄) with hπb
  set πc : ℕ → ℕ × ℕ × ℕ × ℕ := fun t => ((phi3 t).factorization g₁, 0, 0,
    (phi3 t).factorization g₄ - 1) with hπc
  set π0 : ℕ → ℕ × ℕ × ℕ × ℕ := fun t => ((phi3 t).factorization g₁, 0, 0, 0) with hπ0
  have ia : Set.InjOn πa Ta := by
    intro x hx y hy hxy
    obtain ⟨hxT, hx2⟩ := memTa (Finset.mem_coe.mp hx)
    obtain ⟨hyT, hy2⟩ := memTa (Finset.mem_coe.mp hy)
    simp only [hπa, Prod.mk.injEq] at hxy
    exact inj4 x hxT y hyT hxy.1 (by omega) hxy.2.2.1 hxy.2.2.2
  have ib : Set.InjOn πb Tb := by
    intro x hx y hy hxy
    obtain ⟨hxT, hx2, hx3⟩ := memTb (Finset.mem_coe.mp hx)
    obtain ⟨hyT, hy2, hy3⟩ := memTb (Finset.mem_coe.mp hy)
    simp only [hπb, Prod.mk.injEq] at hxy
    exact inj4 x hxT y hyT hxy.1 (by omega) (by omega) hxy.2.2.2
  have ic : Set.InjOn πc Tc := by
    intro x hx y hy hxy
    obtain ⟨hxT, hx2, hx3, hx4⟩ := memTc (Finset.mem_coe.mp hx)
    obtain ⟨hyT, hy2, hy3, hy4⟩ := memTc (Finset.mem_coe.mp hy)
    simp only [hπc, Prod.mk.injEq] at hxy
    exact inj4 x hxT y hyT hxy.1 (by omega) (by omega) (by omega)
  have i0 : Set.InjOn π0 T0 := by
    intro x hx y hy hxy
    obtain ⟨hxT, hx2, hx3, hx4, -⟩ := memT0 (Finset.mem_coe.mp hx)
    obtain ⟨hyT, hy2, hy3, hy4, -⟩ := memT0 (Finset.mem_coe.mp hy)
    simp only [hπ0, Prod.mk.injEq] at hxy
    exact inj4 x hxT y hyT hxy.1 (by omega) (by omega) (by omega)
  have sa : ∑ t ∈ Ta, 1 / ((t : ℚ) + 1) ≤ α₂ * G := by
    calc ∑ t ∈ Ta, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ Ta, α₂ * (α₁ ^ (πa t).1 * (α₂ ^ (πa t).2.1 *
          (α₃ ^ (πa t).2.2.1 * α₄ ^ (πa t).2.2.2))) := by
          refine Finset.sum_le_sum fun t ht => (hw t (memTa ht).1).trans_eq ?_
          simp only [hπa]
          obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (memTa ht).2
          rw [hm, Nat.add_sub_cancel_left, pow_add]
          ring
      _ = α₂ * ∑ t ∈ Ta, α₁ ^ (πa t).1 * (α₂ ^ (πa t).2.1 *
          (α₃ ^ (πa t).2.2.1 * α₄ ^ (πa t).2.2.2)) := by rw [Finset.mul_sum]
      _ ≤ α₂ * G := mul_le_mul_of_nonneg_left
          (sum_weights_le Ta πa ia a1 a2 a3 a4 l1 l2 l3 l4) a2
  have sb : ∑ t ∈ Tb, 1 / ((t : ℚ) + 1) ≤ α₃ * G := by
    calc ∑ t ∈ Tb, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ Tb, α₃ * (α₁ ^ (πb t).1 * (α₂ ^ (πb t).2.1 *
          (α₃ ^ (πb t).2.2.1 * α₄ ^ (πb t).2.2.2))) := by
          refine Finset.sum_le_sum fun t ht => (hw t (memTb ht).1).trans_eq ?_
          simp only [hπb]
          obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (memTb ht).2.2
          rw [(memTb ht).2.1, hm, Nat.add_sub_cancel_left, pow_add]
          ring
      _ = α₃ * ∑ t ∈ Tb, α₁ ^ (πb t).1 * (α₂ ^ (πb t).2.1 *
          (α₃ ^ (πb t).2.2.1 * α₄ ^ (πb t).2.2.2)) := by rw [Finset.mul_sum]
      _ ≤ α₃ * G := mul_le_mul_of_nonneg_left
          (sum_weights_le Tb πb ib a1 a2 a3 a4 l1 l2 l3 l4) a3
  have sc : ∑ t ∈ Tc, 1 / ((t : ℚ) + 1) ≤ α₄ * G := by
    calc ∑ t ∈ Tc, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ Tc, α₄ * (α₁ ^ (πc t).1 * (α₂ ^ (πc t).2.1 *
          (α₃ ^ (πc t).2.2.1 * α₄ ^ (πc t).2.2.2))) := by
          refine Finset.sum_le_sum fun t ht => (hw t (memTc ht).1).trans_eq ?_
          simp only [hπc]
          obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (memTc ht).2.2.2
          rw [(memTc ht).2.1, (memTc ht).2.2.1, hm, Nat.add_sub_cancel_left, pow_add]
          ring
      _ = α₄ * ∑ t ∈ Tc, α₁ ^ (πc t).1 * (α₂ ^ (πc t).2.1 *
          (α₃ ^ (πc t).2.2.1 * α₄ ^ (πc t).2.2.2)) := by rw [Finset.mul_sum]
      _ ≤ α₄ * G := mul_le_mul_of_nonneg_left
          (sum_weights_le Tc πc ic a1 a2 a3 a4 l1 l2 l3 l4) a4
  have s0 : ∑ t ∈ T0, 1 / ((t : ℚ) + 1) ≤ β * (1 / (1 - β₁) * (1 * (1 * 1))) := by
    calc ∑ t ∈ T0, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ T0, β * (β₁ ^ (π0 t).1 *
          ((0 : ℚ) ^ (π0 t).2.1 * ((0 : ℚ) ^ (π0 t).2.2.1 * (0 : ℚ) ^ (π0 t).2.2.2))) := by
          refine Finset.sum_le_sum fun t ht => ?_
          obtain ⟨htT, h2, h3, h4, hB⟩ := memT0 ht
          have h := hlt t htT
          have hr := hrep t htT
          rw [h2, h3, h4, pow_zero, pow_zero, pow_zero, mul_one, mul_one, mul_one] at hr
          have hB' : B ≤ g₁ ^ (phi3 t).factorization g₁ * g₁ ^ 0 := by
            rw [pow_zero, mul_one, ← hr]; exact hB
          have h' : g₁ ^ (phi3 t).factorization g₁ * g₁ ^ 0 < (t + 1) ^ 2 := by
            rw [pow_zero, mul_one, ← hr]; exact h
          refine (inv_succ_le_floor b1 b1 bβ v1 v1 vB hB' h').trans_eq ?_
          simp only [hπ0, pow_zero, mul_one]
      _ = β * ∑ t ∈ T0, β₁ ^ (π0 t).1 *
          ((0 : ℚ) ^ (π0 t).2.1 * ((0 : ℚ) ^ (π0 t).2.2.1 * (0 : ℚ) ^ (π0 t).2.2.2)) := by
          rw [Finset.mul_sum]
      _ ≤ β * (1 / (1 - β₁) * (1 / (1 - 0) * (1 / (1 - 0) * (1 / (1 - 0))))) :=
          mul_le_mul_of_nonneg_left (sum_weights_le T0 π0 i0 b1 le_rfl le_rfl le_rfl m1
            (by norm_num) (by norm_num) (by norm_num)) bβ
      _ = β * (1 / (1 - β₁) * (1 * (1 * 1))) := by norm_num
  have split1 : ∑ t ∈ Ta, (fv t - 1) + ∑ t ∈ Tr, (fv t - 1) = ∑ t ∈ T, (fv t - 1) :=
    Finset.sum_filter_add_sum_filter_not T _ _
  have split2 : ∑ t ∈ Tb, (fv t - 1) + ∑ t ∈ Ts, (fv t - 1) = ∑ t ∈ Tr, (fv t - 1) :=
    Finset.sum_filter_add_sum_filter_not Tr _ _
  have split3 : ∑ t ∈ Tc, (fv t - 1) + ∑ t ∈ T0, (fv t - 1) = ∑ t ∈ Ts, (fv t - 1) :=
    Finset.sum_filter_add_sum_filter_not Ts _ _
  have ea : ∑ t ∈ Ta, (fv t - 1) ≤ 121 / 100 * ∑ t ∈ Ta, 1 / ((t : ℚ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t ht => hfv t (memTa ht).1
  have eb : ∑ t ∈ Tb, (fv t - 1) ≤ 121 / 100 * ∑ t ∈ Tb, 1 / ((t : ℚ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t ht => hfv t (memTb ht).1
  have ec : ∑ t ∈ Tc, (fv t - 1) ≤ 121 / 100 * ∑ t ∈ Tc, 1 / ((t : ℚ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t ht => hfv t (memTc ht).1
  have e0 : ∑ t ∈ T0, (fv t - 1) ≤ 121 / 100 * ∑ t ∈ T0, 1 / ((t : ℚ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun t ht => hfv t (memT0 ht).1
  have k1 := mul_le_mul_of_nonneg_left sa (by norm_num : (0 : ℚ) ≤ 121 / 100)
  have k2 := mul_le_mul_of_nonneg_left sb (by norm_num : (0 : ℚ) ≤ 121 / 100)
  have k3 := mul_le_mul_of_nonneg_left sc (by norm_num : (0 : ℚ) ≤ 121 / 100)
  have k4 := mul_le_mul_of_nonneg_left s0 (by norm_num : (0 : ℚ) ≤ 121 / 100)
  rw [← split1, ← split2, ← split3]
  linarith

/-! ## Forcing kill trees -/

/-- A forcing kill tree. In `step p d cs co cq` the prime `d` divides the source, which is
`phi3 p` for a listed prime `p`, or `q + 1` when `p = 0`; the subtrees treat `d` as a new
slot, as a new prime `≡ 2 (mod 3)`, or as `q`. -/
private inductive KT where
  | dead : KT
  | step (p d : ℕ) (cs co cq : KT) : KT

private def isPr (P : List ℕ) (d : ℕ) : Bool :=
  (decide (d < 100) && Pratt.trialPrime d) || P.contains d

private def srcVal (qk p : ℕ) : ℕ := if p = 0 then qk + 1 else phi3 p

private def srcOK (qk p : ℕ) (sl o2 : List ℕ) : Bool :=
  if p = 0 then decide (qk ≠ 0) else (sl.contains p || o2.contains p)

/-- The state is the known special prime `qk` (`0` if unknown), the listed slots `sl` and the
listed primes `o2 ≡ 2 (mod 3)`. Every possible role of the forced prime must die. -/
private def check (P : List ℕ) (Q0 : ℕ) : ℕ → List ℕ → List ℕ → KT → Bool
  | _, _, _, .dead => false
  | qk, sl, o2, .step p d cs co cq =>
    srcOK qk p sl o2 && isPr P d && srcVal qk p % d == 0 && d != 2 && d != 3 && d != 13 &&
      d != qk && !sl.contains d && !o2.contains d &&
      (!(d % 3 == 1 && decide (sl.length < 2) && srcVal qk p % d ^ 3 != 0) ||
        check P Q0 qk (d :: sl) o2 cs) &&
      (!(d % 3 == 2 && srcVal qk p % d ^ 3 != 0) || check P Q0 qk sl (d :: o2) co) &&
      (!(qk == 0 && d % 12 == 1 && decide (Q0 ≤ d)) || check P Q0 d sl o2 cq)

private theorem check_sound {P : List ℕ} (hP : ∀ p ∈ P, p.Prime) {Q0 q : ℕ}
    {inO inT : ℕ → Prop} (hq12 : q % 12 = 1)
    (F1 : ∀ p, (inO p ∨ inT p) → ∀ d, d.Prime → d ∣ phi3 p →
      d = 2 ∨ d = 3 ∨ d = 13 ∨ d = q ∨ inO d ∨ inT d)
    (F2 : ∀ d, d.Prime → d ∣ q + 1 → d = 2 ∨ d = 3 ∨ d = 13 ∨ d = q ∨ inO d ∨ inT d)
    (F3 : ∀ d, inO d → d % 3 = 1) (F3' : ∀ d, inT d → d % 3 = 2)
    (F4 : ∀ a b c, inO a → inO b → inO c → a ≠ b → a ≠ c → b ≠ c → False)
    (F5 : ∀ p, (inO p ∨ inT p) → ∀ d, (inO d ∨ inT d) → ¬ d ^ 3 ∣ phi3 p)
    (F5' : ∀ d, (inO d ∨ inT d) → ¬ d ^ 3 ∣ q + 1) :
    ∀ (t : KT) (qk : ℕ) (sl o2 : List ℕ), check P Q0 qk sl o2 t = true →
      (qk ≠ 0 → qk = q) → (qk = 0 → Q0 ≤ q) → (∀ x ∈ sl, inO x) → sl.Nodup →
      (∀ x ∈ o2, inT x) → False := by
  have imp : ∀ {c x : Bool}, (!c || x) = true → c = true → x = true := by decide
  intro t
  induction t with
  | dead => intro qk sl o2 h; simp [check] at h
  | step p d cs co cq ihs iho ihq =>
    intro qk sl o2 h hqk hq0 hsl hnd ho2
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsrc, hpr⟩, hdvd⟩, h2⟩, h3⟩, h13⟩, hdq⟩, hdsl⟩, hdo2⟩, hS⟩, hO⟩, hQ⟩ := h
    have hd : d.Prime := by
      simp only [isPr, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpr
      rcases hpr with ⟨-, h⟩ | h
      · exact Pratt.trialPrime_sound h
      · exact hP d (List.contains_iff_mem.mp h)
    have hd2 : d ≠ 2 := by simpa using h2
    have hd3 : d ≠ 3 := by simpa using h3
    have hd13 : d ≠ 13 := by simpa using h13
    have hdqk : d ≠ qk := by simpa using hdq
    have hdsl' : d ∉ sl := by
      intro hm; rw [List.contains_iff_mem.mpr hm] at hdsl; simp at hdsl
    have hdo2' : d ∉ o2 := by
      intro hm; rw [List.contains_iff_mem.mpr hm] at hdo2; simp at hdo2
    have hn : d ∣ srcVal qk p := Nat.dvd_of_mod_eq_zero (by simpa using hdvd)
    have hsrcF : (p = 0 ∧ qk = q) ∨ (p ≠ 0 ∧ (inO p ∨ inT p)) := by
      unfold srcOK at hsrc
      split_ifs at hsrc with hp0
      · exact Or.inl ⟨hp0, hqk (by simpa using hsrc)⟩
      · right
        refine ⟨hp0, ?_⟩
        simp only [Bool.or_eq_true, List.contains_iff_mem] at hsrc
        rcases hsrc with hm | hm
        · exact Or.inl (hsl p hm)
        · exact Or.inr (ho2 p hm)
    have hcls : d = q ∨ inO d ∨ inT d := by
      have key : d = 2 ∨ d = 3 ∨ d = 13 ∨ d = q ∨ inO d ∨ inT d := by
        rcases hsrcF with ⟨hp0, hqq⟩ | ⟨hp0, hpT⟩
        · simp only [srcVal, if_pos hp0, hqq] at hn
          exact F2 d hd hn
        · simp only [srcVal, if_neg hp0] at hn
          exact F1 p hpT d hd hn
      rcases key with e | e | e | e
      · exact absurd e hd2
      · exact absurd e hd3
      · exact absurd e hd13
      · exact e
    have hcap : (inO d ∨ inT d) → srcVal qk p % d ^ 3 ≠ 0 := by
      intro hT hz
      have hdv := Nat.dvd_of_mod_eq_zero hz
      rcases hsrcF with ⟨hp0, hqq⟩ | ⟨hp0, hpT⟩
      · simp only [srcVal, if_pos hp0, hqq] at hdv
        exact F5' d hT hdv
      · simp only [srcVal, if_neg hp0] at hdv
        exact F5 p hpT d hT hdv
    rcases hcls with hdq' | hdO | hdT
    · by_cases hqk0 : qk = 0
      · have hc : (qk == 0 && d % 12 == 1 && decide (Q0 ≤ d)) = true := by
          simp [hqk0, hdq', hq12, hq0 hqk0]
        exact ihq d sl o2 (imp hQ hc) (fun _ => hdq') (fun h0 => absurd h0 hd.ne_zero) hsl
          hnd ho2
      · exact hdqk (hdq'.trans (hqk hqk0).symm)
    · have h31 := F3 d hdO
      rcases Nat.lt_or_ge sl.length 2 with hlen | hlen
      · have hc : (d % 3 == 1 && decide (sl.length < 2) && srcVal qk p % d ^ 3 != 0) =
            true := by
          simp [h31, hlen, hcap (Or.inl hdO)]
        refine ihs qk (d :: sl) o2 (imp hS hc) hqk hq0 ?_ (List.nodup_cons.mpr ⟨hdsl', hnd⟩)
          ho2
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdO
        · exact hsl x hx
      · rcases sl with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · simp at hlen
        · simp at hlen
        · have hab : a ≠ b := by
            intro e
            exact (List.nodup_cons.mp hnd).1 (e ▸ List.mem_cons_self ..)
          exact F4 a b d (hsl a (by simp)) (hsl b (by simp)) hdO hab
            (fun e => hdsl' (by simp [e])) (fun e => hdsl' (by simp [e]))
    · have h32 := F3' d hdT
      have hc : (d % 3 == 2 && srcVal qk p % d ^ 3 != 0) = true := by
        simp [h32, hcap (Or.inr hdT)]
      refine iho qk sl (d :: o2) (imp hO hc) hqk hq0 hsl hnd ?_
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hdT
      · exact ho2 x hx

/-! ## Certificates -/

private def prattCert : List (ℕ × ℕ × List ℕ) :=
  [(109, 6, [2, 2, 3, 3, 3]),
   (127, 3, [2, 3, 3, 7]),
   (139, 2, [2, 3, 23]),
   (157, 5, [2, 2, 3, 13]),
   (163, 2, [2, 3, 3, 3, 3]),
   (181, 2, [2, 2, 3, 3, 5]),
   (211, 2, [2, 3, 5, 7]),
   (307, 5, [2, 3, 3, 17]),
   (331, 3, [2, 3, 5, 11]),
   (367, 6, [2, 3, 61]),
   (421, 2, [2, 2, 3, 5, 7]),
   (457, 13, [2, 2, 2, 3, 19]),
   (499, 7, [2, 3, 83]),
   (631, 3, [2, 3, 3, 5, 7]),
   (853, 2, [2, 2, 3, 71]),
   (1423, 3, [2, 3, 3, 79]),
   (1621, 2, [2, 2, 3, 3, 3, 3, 5]),
   (1801, 11, [2, 2, 2, 3, 3, 5, 5]),
   (1879, 6, [2, 3, 313]),
   (2083, 2, [2, 3, 347]),
   (3169, 7, [2, 2, 2, 2, 2, 3, 3, 11]),
   (3463, 3, [2, 3, 577]),
   (3571, 2, [2, 3, 5, 7, 17]),
   (4327, 3, [2, 3, 7, 103]),
   (4639, 3, [2, 3, 773]),
   (5419, 3, [2, 3, 3, 7, 43]),
   (1171, 2, [2, 3, 3, 5, 13]),
   (7027, 2, [2, 3, 1171]),
   (7687, 6, [2, 3, 3, 7, 61]),
   (8269, 2, [2, 2, 3, 13, 53]),
   (9277, 5, [2, 2, 3, 773]),
   (9463, 3, [2, 3, 19, 83]),
   (9721, 7, [2, 2, 2, 3, 3, 3, 3, 3, 5]),
   (13267, 3, [2, 3, 3, 11, 67]),
   (14713, 5, [2, 2, 2, 3, 613]),
   (16651, 2, [2, 3, 3, 5, 5, 37]),
   (19441, 13, [2, 2, 2, 2, 3, 3, 3, 3, 3, 5]),
   (24571, 7, [2, 3, 3, 3, 5, 7, 13]),
   (29611, 3, [2, 3, 3, 5, 7, 47]),
   (55897, 5, [2, 2, 2, 3, 17, 137]),
   (59221, 2, [2, 2, 3, 3, 5, 7, 47]),
   (65323, 2, [2, 3, 3, 19, 191]),
   (72931, 10, [2, 3, 5, 11, 13, 17]),
   (145861, 2, [2, 2, 3, 5, 11, 13, 17]),
   (151201, 17, [2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 7]),
   (176419, 2, [2, 3, 3, 3, 3, 3, 3, 11, 11]),
   (246247, 3, [2, 3, 7, 11, 13, 41]),
   (260191, 6, [2, 3, 3, 5, 7, 7, 59]),
   (292969, 11, [2, 2, 2, 3, 3, 13, 313]),
   (347821, 2, [2, 2, 3, 5, 11, 17, 31]),
   (360187, 2, [2, 3, 173, 347]),
   (368551, 7, [2, 3, 3, 3, 3, 5, 5, 7, 13]),
   (377011, 3, [2, 3, 3, 5, 59, 71]),
   (398581, 2, [2, 2, 3, 5, 7, 13, 73]),
   (1674289, 26, [2, 2, 2, 2, 3, 3, 7, 11, 151]),
   (1987, 2, [2, 3, 331]),
   (1895599, 6, [2, 3, 3, 53, 1987]),
   (3348577, 13, [2, 2, 2, 2, 2, 3, 3, 7, 11, 151]),
   (7174987, 2, [2, 3, 7, 13, 17, 773]),
   (8863, 3, [2, 3, 7, 211]),
   (744493, 2, [2, 2, 3, 7, 8863]),
   (8933917, 2, [2, 2, 3, 744493]),
   (32668561, 19, [2, 2, 2, 2, 3, 3, 5, 17, 17, 157]),
   (8191, 17, [2, 3, 3, 5, 7, 13]),
   (201252871, 33, [2, 3, 3, 3, 5, 7, 13, 8191]),
   (1871, 14, [2, 5, 11, 17]),
   (1531, 2, [2, 3, 3, 5, 17]),
   (1735887607, 6, [2, 3, 101, 1531, 1871])]

private def qRoots : List (ℕ × KT) :=
  [(37, (.step 0 19 (.step 19 127 (.step 127 5419 .dead .dead .dead) .dead .dead) .dead .dead)),
   (61, (.step 0 31 (.step 31 331 (.step 331 7 .dead .dead .dead) .dead .dead) .dead .dead)),
   (73, (.step 0 37 (.step 37 7 (.step 7 19 .dead .dead .dead) .dead .dead) .dead .dead)),
   (97, (.step 0 7 (.step 7 19 (.step 19 127 .dead .dead .dead) .dead .dead) .dead .dead)),
   (109, (.step 0 5 .dead (.step 5 31 (.step 31 331 (.step 331 7 .dead .dead .dead) .dead .dead) .dead .dead) .dead)),
   (157, (.step 0 79 (.step 79 7 (.step 7 19 .dead .dead .dead) .dead .dead) .dead .dead)),
   (181, (.step 0 7 (.step 7 19 (.step 19 127 .dead .dead .dead) .dead .dead) .dead .dead)),
   (193, (.step 0 97 (.step 97 3169 (.step 3169 3348577 .dead .dead .dead) .dead .dead) .dead .dead)),
   (229, (.step 0 5 .dead (.step 5 31 (.step 31 331 (.step 331 7 .dead .dead .dead) .dead .dead) .dead .dead) .dead)),
   (241, (.step 0 11 .dead (.step 11 7 (.step 7 19 (.step 19 127 .dead .dead .dead) .dead .dead) .dead .dead) .dead)),
   (277, (.step 0 139 (.step 139 499 (.step 499 7 .dead .dead .dead) .dead .dead) .dead .dead)),
   (313, (.step 0 157 (.step 157 8269 (.step 8269 7 .dead .dead .dead) .dead .dead) .dead .dead))]

private def zRoots : List (ℕ × KT) :=
  [(7, (.step 7 19 (.step 19 127 .dead .dead .dead) .dead .dead)),
   (19, (.step 19 127 (.step 127 5419 .dead .dead .dead) .dead .dead)),
   (31, (.step 31 331 (.step 331 7 .dead .dead .dead) .dead .dead)),
   (37, (.step 37 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (43, (.step 43 631 (.step 631 307 .dead .dead .dead) .dead .dead)),
   (61, (.step 61 97 (.step 97 3169 .dead .dead (.step 0 5 .dead (.step 5 31 .dead .dead .dead) .dead)) .dead .dead)),
   (67, (.step 67 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (73, (.step 73 1801 (.step 1801 7 .dead .dead .dead) .dead (.step 0 17 .dead (.step 17 307 (.step 307 43 .dead .dead .dead) .dead .dead) .dead))),
   (79, (.step 79 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (97, (.step 97 3169 (.step 3169 3348577 .dead .dead (.step 0 1674289 .dead .dead .dead)) .dead (.step 0 5 .dead (.step 5 31 (.step 31 331 .dead .dead .dead) .dead .dead) .dead))),
   (103, (.step 103 3571 (.step 3571 139 .dead .dead .dead) .dead .dead)),
   (109, (.step 109 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (127, (.step 127 5419 (.step 5419 31 .dead .dead .dead) .dead .dead)),
   (139, (.step 139 499 (.step 499 7 .dead .dead .dead) .dead .dead)),
   (151, (.step 151 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (157, (.step 157 8269 (.step 8269 7 .dead .dead .dead) .dead (.step 0 5 .dead (.step 5 31 (.step 31 331 .dead .dead .dead) .dead .dead) .dead))),
   (163, (.step 163 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (181, (.step 181 79 (.step 79 7 .dead .dead .dead) .dead .dead)),
   (193, (.step 193 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (199, (.step 199 13267 (.step 13267 7 .dead .dead .dead) .dead .dead)),
   (211, (.step 211 31 (.step 31 331 .dead .dead .dead) .dead .dead)),
   (223, (.step 223 16651 (.step 16651 19 .dead .dead .dead) .dead .dead)),
   (229, (.step 229 97 (.step 97 3169 .dead .dead (.step 229 181 .dead .dead .dead)) .dead .dead)),
   (241, (.step 241 19441 (.step 19441 7 .dead .dead .dead) .dead (.step 0 9721 (.step 9721 157 .dead .dead .dead) .dead .dead))),
   (271, (.step 271 24571 (.step 24571 201252871 .dead .dead .dead) .dead .dead)),
   (277, (.step 277 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (283, (.step 283 73 (.step 73 1801 .dead .dead (.step 283 367 .dead .dead .dead)) .dead .dead)),
   (307, (.step 307 43 (.step 43 631 .dead .dead .dead) .dead .dead)),
   (313, (.step 313 181 (.step 181 79 .dead .dead .dead) .dead .dead)),
   (331, (.step 331 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (337, (.step 337 43 (.step 43 631 .dead .dead .dead) .dead .dead)),
   (349, (.step 349 19 (.step 19 127 .dead .dead .dead) .dead .dead)),
   (367, (.step 367 3463 (.step 3463 61 .dead .dead .dead) .dead .dead)),
   (373, (.step 373 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (379, (.step 379 61 (.step 61 97 .dead .dead .dead) .dead .dead)),
   (397, (.step 397 31 (.step 31 331 .dead .dead .dead) .dead .dead)),
   (409, (.step 409 55897 (.step 55897 7 .dead .dead .dead) .dead (.step 0 19 (.step 19 127 .dead .dead .dead) .dead .dead))),
   (421, (.step 421 59221 (.step 59221 7687 .dead .dead .dead) .dead (.step 0 29611 (.step 29611 2083 .dead .dead .dead) .dead .dead))),
   (433, (.step 433 37 (.step 37 7 .dead .dead .dead) .dead .dead)),
   (439, (.step 439 31 (.step 31 331 .dead .dead .dead) .dead .dead)),
   (457, (.step 457 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (463, (.step 463 19 (.step 19 127 .dead .dead .dead) .dead .dead)),
   (487, (.step 487 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (499, (.step 499 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (523, (.step 523 7027 (.step 7027 1879 .dead .dead .dead) .dead .dead)),
   (541, (.step 541 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (547, (.step 547 163 (.step 163 7 .dead .dead .dead) .dead .dead)),
   (571, (.step 571 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (577, (.step 577 19 (.step 19 127 .dead .dead .dead) .dead .dead)),
   (601, (.step 601 9277 (.step 9277 7 .dead .dead .dead) .dead (.step 0 4639 (.step 4639 7174987 .dead .dead .dead) .dead .dead))),
   (607, (.step 607 9463 (.step 9463 457 .dead .dead (.step 9463 65323 .dead .dead .dead)) .dead .dead)),
   (613, (.step 613 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (619, (.step 619 19 (.step 19 127 .dead .dead .dead) .dead .dead)),
   (631, (.step 631 307 (.step 307 43 .dead .dead .dead) .dead .dead)),
   (643, (.step 643 97 (.step 97 3169 .dead .dead (.step 643 1423 .dead .dead .dead)) .dead .dead)),
   (661, (.step 661 145861 (.step 145861 7 .dead .dead .dead) .dead (.step 0 72931 (.step 72931 4327 .dead .dead .dead) .dead .dead))),
   (673, (.step 673 151201 (.step 151201 853 .dead .dead (.step 151201 8933917 .dead .dead .dead)) .dead (.step 0 19 (.step 19 127 .dead .dead .dead) .dead .dead))),
   (691, (.step 691 19 (.step 19 127 .dead .dead .dead) .dead .dead)),
   (709, (.step 709 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (727, (.step 727 176419 (.step 176419 421 .dead .dead (.step 176419 1895599 .dead .dead .dead)) .dead .dead)),
   (733, (.step 733 19 (.step 19 127 .dead .dead .dead) .dead .dead)),
   (739, (.step 739 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (751, (.step 751 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (757, (.step 757 14713 (.step 14713 19 .dead .dead .dead) .dead (.step 0 7 (.step 7 19 .dead .dead .dead) .dead .dead))),
   (769, (.step 769 31 (.step 31 331 .dead .dead .dead) .dead .dead)),
   (787, (.step 787 37 (.step 37 7 .dead .dead .dead) .dead .dead)),
   (811, (.step 811 31 (.step 31 331 .dead .dead .dead) .dead .dead)),
   (823, (.step 823 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (829, (.step 829 211 (.step 211 31 .dead .dead .dead) .dead .dead)),
   (853, (.step 853 43 (.step 43 631 .dead .dead .dead) .dead .dead)),
   (859, (.step 859 246247 (.step 246247 19 .dead .dead .dead) .dead .dead)),
   (877, (.step 877 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (883, (.step 883 260191 (.step 260191 1735887607 .dead .dead .dead) .dead .dead)),
   (907, (.step 907 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (919, (.step 919 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (937, (.step 937 292969 (.step 292969 61 .dead .dead .dead) .dead (.step 0 5 .dead (.step 5 31 (.step 31 331 .dead .dead .dead) .dead .dead) .dead))),
   (967, (.step 967 67 (.step 67 7 .dead .dead .dead) .dead .dead)),
   (991, (.step 991 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (997, (.step 997 31 (.step 31 331 .dead .dead .dead) .dead .dead)),
   (1009, (.step 1009 37 (.step 37 7 .dead .dead .dead) .dead .dead)),
   (1021, (.step 1021 347821 (.step 347821 19 .dead .dead .dead) .dead (.step 0 61 (.step 61 97 .dead .dead .dead) .dead .dead))),
   (1033, (.step 1033 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (1039, (.step 1039 360187 (.step 360187 7 .dead .dead .dead) .dead .dead)),
   (1051, (.step 1051 368551 (.step 368551 367 .dead .dead .dead) .dead .dead)),
   (1063, (.step 1063 377011 (.step 377011 79 .dead .dead .dead) .dead .dead)),
   (1069, (.step 1069 139 (.step 139 499 .dead .dead .dead) .dead .dead)),
   (1087, (.step 1087 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (1093, (.step 1093 398581 (.step 398581 1621 .dead .dead (.step 398581 32668561 .dead .dead .dead)) .dead (.step 0 17 .dead (.step 17 307 (.step 307 43 .dead .dead .dead) .dead .dead) .dead))),
   (1117, (.step 1117 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (1123, (.step 1123 127 (.step 127 5419 .dead .dead .dead) .dead .dead)),
   (1129, (.step 1129 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (1153, (.step 1153 109 (.step 109 7 .dead .dead .dead) .dead .dead)),
   (1171, (.step 1171 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (1201, (.step 1201 7 (.step 7 19 .dead .dead .dead) .dead .dead)),
   (1213, (.step 1213 7 (.step 7 19 .dead .dead .dead) .dead .dead))]

private theorem pratt_ok : Pratt.check prattCert = true := by
  decide +kernel

private def PL : List ℕ := prattCert.map Prod.fst

private theorem PL_prime : ∀ p ∈ PL, p.Prime := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
  exact Pratt.check_sound pratt_ok e he

private theorem cert_q : qRoots.all (fun e => check PL 337 e.1 [] [] e.2) = true := by
  decide +kernel

private theorem cert_z : zRoots.all (fun e => check PL 337 0 [e.1] [] e.2) = true := by
  decide +kernel

private def coverQ (q : ℕ) : Bool :=
  q % 12 != 1 || decide (q ≤ 1) || hasSmallFactor q || q == 13 ||
    qRoots.any (fun e => e.1 == q)

private def coverZ (z : ℕ) : Bool :=
  z % 3 != 1 || decide (z ≤ 1) || hasSmallFactor z || z == 13 ||
    zRoots.any (fun e => e.1 == z)

private theorem cover_q : (List.range 337).all coverQ = true := by
  decide +kernel

private theorem cover_z : (List.range 1225).all coverZ = true := by
  decide +kernel

private theorem box_13 : ∀ a < 15, 13 ^ a < 10 ^ 16 → rootIn [0, 3] (13 ^ a) = true := by
  decide +kernel

private theorem box_A : ∀ a < 12, 3 * 13 ^ a < phi3 1000000 →
    rootIn [1, 22] (3 * 13 ^ a) = true := by
  decide +kernel

private theorem q_tree {q : ℕ} (hq : q.Prime) (h12 : q % 12 = 1) (h13 : q ≠ 13)
    (hlt : q < 337) : ∃ t, check PL 337 q [] [] t = true := by
  have h := (List.all_eq_true.mp cover_q) q (List.mem_range.mpr hlt)
  have h2 := hq.two_le
  unfold coverQ at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · simp [h12] at h
  · simp at h; omega
  · rw [hasSmallFactor_false hq] at h; exact absurd h (by decide)
  · simp at h; exact absurd h h13
  · obtain ⟨e, he, hq'⟩ := List.any_eq_true.mp h
    have hc := (List.all_eq_true.mp cert_q) e he
    simp only [beq_iff_eq] at hq'
    rw [hq'] at hc
    exact ⟨e.2, hc⟩

private theorem z_tree {z : ℕ} (hz : z.Prime) (h3 : z % 3 = 1) (h13 : z ≠ 13)
    (hlt : z < 1225) : ∃ t, check PL 337 0 [z] [] t = true := by
  have h := (List.all_eq_true.mp cover_z) z (List.mem_range.mpr hlt)
  have h2 := hz.two_le
  unfold coverZ at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · simp [h3] at h
  · simp at h; omega
  · rw [hasSmallFactor_false hz] at h; exact absurd h (by decide)
  · simp at h; exact absurd h h13
  · obtain ⟨e, he, hz'⟩ := List.any_eq_true.mp h
    have hc := (List.all_eq_true.mp cert_z) e he
    simp only [beq_iff_eq] at hz'
    rw [hz'] at hc
    exact ⟨e.2, hc⟩

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

/-- The sum over at most `m` slots, all at least `X`. -/
private theorem slot_sum {O : Finset ℕ} {m X : ℕ} (hc : O.card ≤ m) (hX : 10 ≤ X)
    (hO : ∀ x ∈ O, X ≤ x) : ∑ t ∈ O, (fv t - 1) ≤ m * (121 / 100 * (1 / ((X : ℚ) + 1))) := by
  have hb : ∀ t ∈ O, fv t - 1 ≤ 121 / 100 * (1 / ((X : ℚ) + 1)) := by
    intro t ht
    have h10 := hO t ht
    refine (fv_sub_le (by omega)).trans ?_
    have : (X : ℚ) ≤ t := by exact_mod_cast h10
    gcongr
  calc ∑ t ∈ O, (fv t - 1) ≤ ∑ _t ∈ O, 121 / 100 * (1 / ((X : ℚ) + 1)) :=
        Finset.sum_le_sum hb
    _ = O.card * (121 / 100 * (1 / ((X : ℚ) + 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ m * (121 / 100 * (1 / ((X : ℚ) + 1))) := by
        have : (O.card : ℚ) ≤ m := by exact_mod_cast hc
        gcongr

private theorem floor13 {t a b c : ℕ} (htp : t.Prime) (t3 : t ≠ 3) (ha : 13 ≠ a) (hb : 13 ≠ b)
    (hc : 13 ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsupp : (phi3 t).primeFactors ⊆ {13, a, b, c}) (h1 : ¬ a ∣ phi3 t) (h2 : ¬ b ∣ phi3 t)
    (h3 : ¬ c ∣ phi3 t) : 10 ^ 16 ≤ phi3 t := by
  have hV0 : phi3 t ≠ 0 := by unfold phi3; omega
  have hrep := eq_four_pow hV0 ha hb hc hab hac hbc hsupp
  rw [Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd h2,
    Nat.factorization_eq_zero_of_not_dvd h3, pow_zero, pow_zero, pow_zero, mul_one, mul_one,
    mul_one] at hrep
  by_contra hlt
  rw [not_le] at hlt
  have hk : (phi3 t).factorization 13 < 15 := exp_lt_of_pow (c := 13) (by norm_num)
    (Nat.pos_of_ne_zero hV0) ⟨1, by rw [mul_one]; exact hrep⟩ hlt (by norm_num)
  have hmem := mem_of_rootIn (box_13 _ hk (by rw [← hrep]; exact hlt)) hrep
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with e | e
  · exact absurd (e ▸ htp) (by norm_num)
  · exact t3 e

end RestrainedFive

open RestrainedFive


/-! ## The leaf `r = 13` -/

/-- **Restrained, leaf `r = 13`.** Under the hypotheses of `restrained_three_sq_cases`, the
further prime `r` is not `13`. -/
theorem restrained_not_thirteen {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (h3 : N.factorization 3 = 2) : r ≠ 13 := by
  rintro rfl
  have hN0 := h.ne_zero
  have hq4 := (special_mod_four h hq hodd).1
  have q3 : q ≠ 3 := by rintro rfl; norm_num at hq4
  have q13 : q ≠ 13 := Ne.symm hrq
  have mem : ∀ {p}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, hN0⟩
  have d3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have d13 : 13 ∣ N := OPNStarter.force_prime h.perfect Nat.prime_three h3 (by norm_num)
    (by norm_num) (by rw [sigma_prime_sq Nat.prime_three]; norm_num [phi3])
  have dq : q ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  set K : Finset ℕ := {3, 13, q} with hK
  have hKsub : K ⊆ N.primeFactors := by
    intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact mem Nat.prime_three d3
    · exact mem (by norm_num) d13
    · exact mem hq dq
  set T := N.primeFactors \ K with hT
  have hTmem : ∀ {t}, t ∈ T → t.Prime ∧ t ∣ N ∧ t ≠ 3 ∧ t ≠ 13 ∧ t ≠ q := by
    intro t ht
    obtain ⟨htN, htK⟩ := Finset.mem_sdiff.mp ht
    simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or] at htK
    exact ⟨Nat.prime_of_mem_primeFactors htN, Nat.dvd_of_mem_primeFactors htN, htK.1,
      htK.2.1, htK.2.2⟩
  have toT : ∀ {p}, p.Prime → p ∣ N → p ≠ 3 → p ≠ 13 → p ≠ q → p ∈ T := by
    intro p hp hd h3' h13' hq'
    refine Finset.mem_sdiff.mpr ⟨mem hp hd, ?_⟩
    simp only [hK, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h3', h13', hq'⟩
  have key2 : ∀ {t}, t ∈ T → N.factorization t = 2 := fun ht =>
    hsq _ (Finset.mem_sdiff.mp ht).1 (hTmem ht).2.2.2.2 (hTmem ht).2.2.2.1
  have mod3 : ∀ {t}, t.Prime → t ≠ 3 → t % 3 = 1 ∨ t % 3 = 2 := by
    intro t htp t3
    have h0 : t % 3 ≠ 0 := fun h0 => t3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three htp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
    omega
  set O := T.filter (fun t => t % 3 = 1) with hO
  set O2 := T.filter (fun t => ¬ t % 3 = 1) with hO2
  have memO : ∀ {t}, t ∈ O ↔ t ∈ T ∧ t % 3 = 1 := Finset.mem_filter
  have memO2 : ∀ {t}, t ∈ O2 ↔ t ∈ T ∧ ¬ t % 3 = 1 := Finset.mem_filter
  have O2mod : ∀ {t}, t ∈ O2 → t % 3 = 2 := fun ht => by
    obtain ⟨htT, ht1⟩ := memO2.mp ht
    rcases mod3 (hTmem htT).1 (hTmem htT).2.2.1 with e | e
    · exact absurd e ht1
    · exact e
  have hsig0 : σ 1 (q ^ N.factorization q) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  -- the 3-adic ledger over `{q} ∪ O`
  have hledger : O.card + padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤ 2 := by
    have hle := sum_padicValNat_sigma_le_factorization h.perfect Nat.prime_three (by norm_num)
      (insert q O)
    have hqO : q ∉ O := fun hm => (hTmem (memO.mp hm).1).2.2.2.2 rfl
    have hc : ∑ p ∈ O, padicValNat 3 (σ 1 (p ^ N.factorization p)) = O.card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hpT, hp1⟩ := memO.mp hp
      rw [key2 hpT, sigma_prime_sq (hTmem hpT).1, padicValNat_three_phi3, if_pos hp1]
    rw [Finset.sum_insert hqO, hc, h3] at hle
    omega
  -- caps from the ledger at a prime of `T`
  have capG : ∀ y ∈ T, ∀ p m, p ≠ 0 → m ∣ σ 1 (p ^ N.factorization p) → ¬ y ^ 3 ∣ m := by
    intro y hy p m hp0 hm hd
    obtain ⟨hyp, hyN, -, -, -⟩ := hTmem hy
    have hy2 : y ≠ 2 := by rintro rfl; exact h.not_two_dvd hyN
    have hle := sum_padicValNat_sigma_le_factorization h.perfect hyp hy2 {p}
    rw [Finset.sum_singleton, key2 hy] at hle
    have hs0 : σ 1 (p ^ N.factorization p) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hp0)).ne'
    have h3' := (hyp.pow_dvd_iff_le_factorization hs0).mp (hd.trans hm)
    rw [Nat.factorization_def _ hyp, ← Nat.padicValNat_def] at h3'
    omega
  -- prime factors of `σ(w^2)`
  have hstr : ∀ w ∈ T, ∀ d, d.Prime → d ∣ phi3 w →
      d = 3 ∨ d = 13 ∨ d = q ∨ (d ∈ O ∧ d ≠ w) := by
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
    by_cases h13' : d = 13
    · exact Or.inr (Or.inl h13')
    by_cases hq' : d = q
    · exact Or.inr (Or.inr (Or.inl hq'))
    exact Or.inr (Or.inr (Or.inr ⟨memO.mpr ⟨toT hd hdN hd3 h13' hq', hd1⟩, hdw⟩))
  -- the members of `O2` are at least `10`
  have ten_le : (∀ z ∈ O, 32 ≤ z) → q ≠ 31 → ∀ t ∈ O2, 10 ≤ t := by
    intro hO32 hq31 t ht
    obtain ⟨htT, -⟩ := memO2.mp ht
    obtain ⟨htp, htN, -, -, -⟩ := hTmem htT
    by_contra hlt
    rw [not_le] at hlt
    rcases small_cases hlt (O2mod ht) with e | e | e
    · exact h.not_two_dvd (e ▸ htN)
    · rcases hstr t htT 31 (by norm_num) (by rw [e]; norm_num [phi3]) with e' | e' | e' | ⟨h31, -⟩
      · norm_num at e'
      · norm_num at e'
      · exact hq31 e'.symm
      · have := hO32 31 h31; omega
    · exact absurd (e ▸ htp) (by norm_num)
  have slot_facts : ∀ {z}, z ∈ O → z.Prime ∧ z ≠ 13 ∧ z ≠ q ∧ z % 3 = 1 := fun hz => by
    obtain ⟨hzT, hz1⟩ := memO.mp hz
    obtain ⟨hzp, -, -, h13', hq'⟩ := hTmem hzT
    exact ⟨hzp, h13', hq', hz1⟩
  have hsplit : ∑ t ∈ O, (fv t - 1) + ∑ t ∈ O2, (fv t - 1) = ∑ t ∈ T, (fv t - 1) :=
    Finset.sum_filter_add_sum_filter_not T _ _
  have c13 : abundancy (13 ^ N.factorization 13) ≤ 13 / 12 :=
    (abundancy_prime_pow_lt (by norm_num) _).le.trans (le_of_eq (by norm_num))
  have c3 : abundancy (3 ^ N.factorization 3) ≤ 13 / 9 := by
    rw [h3, abundancy_sq Nat.prime_three]; norm_num [fv]
  have cq : ∀ Q : ℕ, 2 ≤ Q → Q ≤ q →
      abundancy (q ^ N.factorization q) ≤ (Q : ℚ) / ((Q : ℚ) - 1) := by
    intro Q hQ2 hQq
    refine (abundancy_prime_pow_lt hq _).le.trans ?_
    have hQ' : (2 : ℚ) ≤ Q := by exact_mod_cast hQ2
    have hQq' : (Q : ℚ) ≤ q := by exact_mod_cast hQq
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  -- closing by abundancy with `c 3 = 13/9`, `c 13 = 13/12`, `c q = Q/(Q - 1)`
  have close : ∀ (Q : ℕ) (S : ℚ), 2 ≤ Q → Q ≤ q → ∑ t ∈ T, (fv t - 1) ≤ S →
      (13 / 9 : ℚ) * (13 / 12 * ((Q : ℚ) / ((Q : ℚ) - 1))) < 2 * (1 - S) → False := by
    intro Q S hQ2 hQq hS hfin
    set c : ℕ → ℚ := fun p => if p = 3 then 13 / 9 else if p = 13 then 13 / 12 else
      (Q : ℚ) / ((Q : ℚ) - 1) with hc
    have eq : c q = (Q : ℚ) / ((Q : ℚ) - 1) := by simp [hc, q3, q13]
    refine abundancy_close h K hKsub c ?_ S (fun t ht => key2 ht) hS ?_
    · intro p hp
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | hpq
      · simpa [hc] using c3
      · simpa [hc] using c13
      · rw [hpq, eq]; exact cq Q hQ2 hQq
    · rw [hK, Finset.prod_insert (by simp [Ne.symm q3]), Finset.prod_pair (Ne.symm q13), eq]
      have e3 : c 3 = 13 / 9 := by simp [hc]
      have e13 : c 13 = 13 / 12 := by simp [hc]
      rw [e3, e13]
      exact hfin
  rcases mod3 hq q3 with hq1 | hq2
  · -- branch B: `q ≡ 1 (mod 12)`
    have hq12 : q % 12 = 1 := by omega
    have hOc : O.card ≤ 2 := by omega
    have inT_of : ∀ {p}, (p ∈ O ∨ p ∈ O2) → p ∈ T := by
      rintro p (hp | hp)
      · exact (memO.mp hp).1
      · exact (memO2.mp hp).1
    have sortT : ∀ {d}, d ∈ T → d ∈ O ∨ d ∈ O2 := by
      intro d hd
      by_cases h1 : d % 3 = 1
      · exact Or.inl (memO.mpr ⟨hd, h1⟩)
      · exact Or.inr (memO2.mpr ⟨hd, h1⟩)
    have F4 : ∀ a b c, a ∈ O → b ∈ O → c ∈ O → a ≠ b → a ≠ c → b ≠ c → False :=
      fun a b c ha hb hc hab hac hbc => by
        have := three_le_card ha hb hc hab hac hbc
        omega
    have killer : ∀ (t : KT) (qk : ℕ) (sl o2 : List ℕ), check PL 337 qk sl o2 t = true →
        (qk ≠ 0 → qk = q) → (qk = 0 → 337 ≤ q) → (∀ x ∈ sl, x ∈ O) → sl.Nodup →
        (∀ x ∈ o2, x ∈ O2) → False :=
      check_sound (inO := fun d => d ∈ O) (inT := fun d => d ∈ O2) PL_prime hq12
        (fun p hp d hd hdd => by
          rcases hstr p (inT_of hp) d hd hdd with e | e | e | ⟨e, -⟩
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
        (fun d hd hdd => by
          by_cases hd2 : d = 2
          · exact Or.inl hd2
          have hdN : d ∣ N := OPNStarter.force_prime h.perfect hq rfl hd hd2
            (hdd.trans (succ_dvd_sigma_special hq hodd))
          by_cases hd3 : d = 3
          · exact Or.inr (Or.inl hd3)
          by_cases hd13 : d = 13
          · exact Or.inr (Or.inr (Or.inl hd13))
          by_cases hdq : d = q
          · exact Or.inr (Or.inr (Or.inr (Or.inl hdq)))
          exact Or.inr (Or.inr (Or.inr (Or.inr (sortT (toT hd hdN hd3 hd13 hdq))))))
        (fun d hd => (memO.mp hd).2) (fun d hd => O2mod hd) F4
        (fun p hp d hd => capG d (inT_of hd) p (phi3 p) (hTmem (inT_of hp)).1.ne_zero
          (by rw [key2 (inT_of hp), sigma_prime_sq (hTmem (inT_of hp)).1]))
        (fun d hd => capG d (inT_of hd) q (q + 1) hq.ne_zero (succ_dvd_sigma_special hq hodd))
    -- `q ≥ 337`
    have hq337 : 337 ≤ q := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨t, ht⟩ := q_tree hq hq12 q13 hlt
      exact killer t q [] [] ht (fun _ => rfl) (fun h0 => absurd h0 hq.ne_zero) (by simp)
        List.nodup_nil (by simp)
    -- slots are at least `1225`
    have hslot : ∀ z ∈ O, 1225 ≤ z := by
      intro z hz
      obtain ⟨hzp, hz13, -, hz1⟩ := slot_facts hz
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨t, ht⟩ := z_tree hzp hz1 hz13 hlt
      exact killer t 0 [z] [] ht (fun h0 => absurd rfl h0) (fun _ => hq337)
        (by simpa using hz) (List.nodup_singleton z) (by simp)
    -- two generators covering the slots
    have D1p : Nat.Prime 1000187 := by norm_num
    have D2p : Nat.Prime 1000199 := by norm_num
    obtain ⟨x, y, hxp, hyp, hxy, hx1, hy1, hx13, hy13, hxq, hyq, hOxy⟩ :
        ∃ x y : ℕ, x.Prime ∧ y.Prime ∧ x ≠ y ∧ 1225 ≤ x ∧ 1225 ≤ y ∧ x ≠ 13 ∧ y ≠ 13 ∧
          x ≠ q ∧ y ≠ q ∧ ∀ z ∈ O, z = x ∨ z = y := by
      have hD1q : (1000187 : ℕ) ≠ q := by intro e; rw [← e] at hq12; norm_num at hq12
      have hD2q : (1000199 : ℕ) ≠ q := by intro e; rw [← e] at hq12; norm_num at hq12
      rcases O.eq_empty_or_nonempty with he | ⟨a, ha⟩
      · exact ⟨1000187, 1000199, D1p, D2p, by norm_num, by norm_num, by norm_num, by norm_num,
          by norm_num, hD1q, hD2q, by simp [he]⟩
      obtain ⟨hap, ha13, haq, ha1⟩ := slot_facts ha
      rcases (O.erase a).eq_empty_or_nonempty with he | ⟨b, hb⟩
      · refine ⟨a, 1000187, hap, D1p, ?_, hslot a ha, by norm_num, ha13, by norm_num, haq,
          hD1q, fun z hz => ?_⟩
        · intro e; rw [e] at ha1; norm_num at ha1
        · left
          by_contra hza
          have : z ∈ O.erase a := Finset.mem_erase.mpr ⟨hza, hz⟩
          rw [he] at this
          simp at this
      · obtain ⟨hba, hbO⟩ := Finset.mem_erase.mp hb
        obtain ⟨hbp, hb13, hbq, -⟩ := slot_facts hbO
        refine ⟨a, b, hap, hbp, Ne.symm hba, hslot a ha, hslot b hbO, ha13, hb13, haq, hbq,
          fun z hz => ?_⟩
        by_contra hz'
        rw [not_or] at hz'
        exact F4 a b z ha hbO hz (Ne.symm hba) (Ne.symm hz'.1) (Ne.symm hz'.2)
    have hS2 := rankin_tail3 O2 (g₁ := 13) (g₂ := q) (g₃ := x) (g₄ := y) (B := 10 ^ 16)
      (α₁ := 2774 / 10000) (α₂ := 1 / ((18 : ℕ) : ℚ)) (α₃ := 1 / ((35 : ℕ) : ℚ))
      (α₄ := 1 / ((35 : ℕ) : ℚ)) (β₁ := 527 / 1000) (β := 1 / 10 ^ 4) hq hxp hyp
      (Ne.symm q13) (Ne.symm hx13) (Ne.symm hy13) (Ne.symm hxq) (Ne.symm hyq) hxy
      (by norm_num) (by positivity) (by positivity) (by positivity)
      (by norm_num) (inv_lt_one' (by norm_num)) (inv_lt_one' (by norm_num))
      (inv_lt_one' (by norm_num))
      (by norm_num) (weight_ok (by norm_num) (by norm_num; omega))
      (weight_ok (by norm_num) (by norm_num; omega)) (weight_ok (by norm_num) (by norm_num; omega))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
        intro t ht
        obtain ⟨htT, -⟩ := memO2.mp ht
        obtain ⟨htp, -, t3, -, -⟩ := hTmem htT
        have ht2 := O2mod ht
        have hsupp : (phi3 t).primeFactors ⊆ {13, q, x, y} := by
          intro d hd
          have hdp := Nat.prime_of_mem_primeFactors hd
          have hdd := Nat.dvd_of_mem_primeFactors hd
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hstr t htT d hdp hdd with e | e | e | ⟨hdO, -⟩
          · subst e; have := (three_dvd_phi3_iff t).1 hdd; omega
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (hOxy d hdO))
        refine ⟨ten_le (fun z hz => by have := hslot z hz; omega) (by omega) t ht, hsupp,
          fun h1 h2 h3' => ?_⟩
        exact floor13 htp t3 (Ne.symm q13) (Ne.symm hx13) (Ne.symm hy13) (Ne.symm hxq)
          (Ne.symm hyq) hxy hsupp h1 h2 h3')
    have hS1 := slot_sum (O := O) (m := 2) (X := 1225) hOc (by norm_num) hslot
    refine close 337 _ (by norm_num) hq337 (hsplit.symm.trans_le (add_le_add hS1 hS2)) ?_
    norm_num
  · -- branch A: `q ≡ 2 (mod 3)`
    have hOc : O.card ≤ 1 := by
      have h3d : 3 ∣ σ 1 (q ^ N.factorization q) :=
        (Nat.dvd_of_mod_eq_zero (by omega : (q + 1) % 3 = 0)).trans
          (succ_dvd_sigma_special hq hodd)
      have := (Nat.prime_three.dvd_iff_one_le_factorization hsig0).mp h3d
      rw [Nat.factorization_def _ Nat.prime_three, ← Nat.padicValNat_def] at this
      omega
    have hOone : ∀ {x y}, x ∈ O → y ∈ O → x = y := fun hx hy =>
      Finset.card_le_one.mp hOc _ hx _ hy
    have notq : ∀ t, ¬ q ∣ phi3 t := by
      intro t hd
      have := prime_dvd_phi3_mod_three hq q3 hd
      omega
    -- slots are at least `10^6`
    have hslot : ∀ z ∈ O, 1000000 ≤ z := by
      intro z hz
      obtain ⟨hzp, -, -, hz1⟩ := slot_facts hz
      obtain ⟨he, hn3⟩ := phi3_div_three hz1
      have hn0 : phi3 z / 3 ≠ 0 := by
        intro h0; rw [h0] at he; unfold phi3 at he; omega
      have hrep : phi3 z / 3 = 13 ^ (phi3 z / 3).primeFactorsList.length := by
        refine Nat.eq_prime_pow_of_unique_prime_dvd hn0 fun {d} hdp hdd => ?_
        have hdz : d ∣ phi3 z := hdd.trans (Dvd.intro_left 3 he.symm)
        rcases hstr z (memO.mp hz).1 d hdp hdz with e | e | e | ⟨hdO, hdw⟩
        · subst e; exact absurd hdd hn3
        · exact e
        · subst e; exact absurd hdz (notq z)
        · exact absurd (hOone hdO hz) hdw
      set k := (phi3 z / 3).primeFactorsList.length
      have hV : phi3 z = 3 * 13 ^ k := by rw [← hrep]; exact he
      by_contra hlt
      rw [not_le] at hlt
      have hlt' : 3 * 13 ^ k < phi3 1000000 := by rw [← hV]; exact phi3_strictMono hlt
      have hk : k < 12 := exp_lt_of_pow (c := 13) (by norm_num) (by positivity)
        (Dvd.intro_left 3 rfl) hlt' (by norm_num [phi3])
      have hmem := mem_of_rootIn (box_A k hk hlt') hV
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with e | e
      · exact absurd (e ▸ hzp) (by norm_num)
      · exact absurd (e ▸ hzp) (by norm_num)
    have D0p : Nat.Prime 1000151 := by norm_num
    have D1p : Nat.Prime 1000187 := by norm_num
    have D2p : Nat.Prime 1000199 := by norm_num
    obtain ⟨x, hxp, hx1, hx13, hxD1, hxD2, hOx⟩ :
        ∃ x : ℕ, x.Prime ∧ 1000000 ≤ x ∧ x ≠ 13 ∧ x ≠ 1000187 ∧ x ≠ 1000199 ∧
          ∀ z ∈ O, z = x := by
      rcases O.eq_empty_or_nonempty with he | ⟨a, ha⟩
      · exact ⟨1000151, D0p, by norm_num, by norm_num, by norm_num, by norm_num, by simp [he]⟩
      obtain ⟨hap, ha13, -, ha1⟩ := slot_facts ha
      refine ⟨a, hap, hslot a ha, ha13, ?_, ?_, fun z hz => hOone hz ha⟩
      · intro e; rw [e] at ha1; norm_num at ha1
      · intro e; rw [e] at ha1; norm_num at ha1
    have hS2 := rankin_tail3 O2 (g₁ := 13) (g₂ := x) (g₃ := 1000187) (g₄ := 1000199)
      (B := 10 ^ 16) (α₁ := 2774 / 10000) (α₂ := 1 / ((1000 : ℕ) : ℚ))
      (α₃ := 1 / ((1000 : ℕ) : ℚ)) (α₄ := 1 / ((1000 : ℕ) : ℚ)) (β₁ := 527 / 1000)
      (β := 1 / 10 ^ 4) hxp D1p D2p
      (Ne.symm hx13) (by norm_num) (by norm_num) hxD1 hxD2 (by norm_num)
      (by norm_num) (by positivity) (by positivity) (by positivity)
      (by norm_num) (inv_lt_one' (by norm_num)) (inv_lt_one' (by norm_num))
      (inv_lt_one' (by norm_num))
      (by norm_num) (weight_ok (by norm_num) (by norm_num; omega))
      (weight_ok (by norm_num) (by norm_num)) (weight_ok (by norm_num) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
        intro t ht
        obtain ⟨htT, -⟩ := memO2.mp ht
        obtain ⟨htp, -, t3, -, -⟩ := hTmem htT
        have ht2 := O2mod ht
        have hsupp : (phi3 t).primeFactors ⊆ {13, x, 1000187, 1000199} := by
          intro d hd
          have hdp := Nat.prime_of_mem_primeFactors hd
          have hdd := Nat.dvd_of_mem_primeFactors hd
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hstr t htT d hdp hdd with e | e | e | ⟨hdO, -⟩
          · subst e; have := (three_dvd_phi3_iff t).1 hdd; omega
          · exact Or.inl e
          · subst e; exact absurd hdd (notq t)
          · exact Or.inr (Or.inl (hOx d hdO))
        refine ⟨ten_le (fun z hz => by have := hslot z hz; omega) (by omega) t ht, hsupp,
          fun h1 h2 h3' => ?_⟩
        exact floor13 htp t3 (Ne.symm hx13) (by norm_num) (by norm_num) hxD1 hxD2 (by norm_num)
          hsupp h1 h2 h3')
    have hS1 := slot_sum (O := O) (m := 1) (X := 1000000) hOc (by norm_num) hslot
    have hq5 : 5 ≤ q := by have := hq.two_le; omega
    refine close 5 _ (by norm_num) hq5 (hsplit.symm.trans_le (add_le_add hS1 hS2)) ?_
    norm_num

/-! ## Final case theorem -/

/-- **Restrained odd perfect numbers, final form.** With the hypotheses of
`three_dvd_of_one_exception`, the exceptional prime is `3`, with `v_3(N)` even and at least
`4`, `q ≡ 1 (mod 3)`, `5 ∤ N` and `7 ∤ N`. The conclusion `r = 3` is the first half of Theorem 1
of Ochem and Zelinsky (arXiv 2607.19746, 2026); this proof uses neither `ω(N) ≥ 10` nor results
on the Nagell-Ljunggren equation. -/
theorem restrained_exception_eq_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    r = 3 ∧ 4 ≤ N.factorization 3 ∧ Even (N.factorization 3) ∧ q % 3 = 1 ∧ ¬ 5 ∣ N ∧
      ¬ 7 ∣ N := by
  rcases restrained_cases_four h hq hodd hr hrq hsq with h1 | ⟨h3, h13⟩
  · exact h1
  · exact absurd h13 (restrained_not_thirteen h hq hodd hrq hsq h3)

end OddPerfect

#print axioms OddPerfect.RestrainedFive.rankin_tail3
#print axioms OddPerfect.restrained_not_thirteen
#print axioms OddPerfect.restrained_exception_eq_three
