import OddPerfect.ThreeFreeTwo
import OddPerfect.OmegaFour

/-!
# The certificate independent core for three exceptional primes

This file is the certificate independent core of a proof built on the method of
`OddPerfect.ThreeFreeTwo`. The setting has four distinguished primes: the special prime `q`
of an odd perfect number `N` and three further primes `r₁, r₂, r₃`; every other prime factor
`s` of `N` (an ordinary prime) has an exponent `e` with `3 ∣ e + 1` (for example `e = 2`), and
`3 ∤ N`. Nothing here depends on a case analysis or certificate; the statement with three
exceptional primes is not proved in this file.

* `ctx4_of_not_three_dvd` replaces arbitrary labels `r₁, r₂, r₃` by three distinct prime
  factors of `N` other than `q` that contain every label dividing `N` (there are at least four
  prime factors by `four_le_card_primeFactors`), and packages the result as `Ctx4`.
* For an ordinary `s`, `1 + s + s^2` divides `σ(s^e)` and hence `N`, so `s ≡ 2 (mod 3)`; every
  prime factor of `1 + s + s^2` is `1` modulo 3, hence not ordinary, hence one of the four
  primes. So `1 + s + s^2 = q^a r₁^b r₂^c r₃^d` with `(a, b, c, d) = vec4 q r₁ r₂ r₃ s` not all
  even, and `vec4` is injective on the ordinary primes.
* With weights `α, β, γ, δ ∈ [0, 1)` satisfying `w² p ≥ 1` for each of the four primes `p`
  (or `p ≡ 2 (mod 3)`), the weight `wt4 α β γ δ (vec4 q r₁ r₂ r₃ s)` times `s + 1` is at
  least 1.
* `Ctx4.close`: the abundancy of `s^e` is below `rv s = s/(s - 1)`. The ordinary primes below
  `cap` lie in an explicit finite set `C`. For the larger ones, `rv s = fv s · s³/(s³ - 1)`
  with `fv s = (s^2 + s + 1)/s^2`; the product of `s³/(s³ - 1)` over `s ≥ cap` is at most
  `tailF cap`, and the product of `fv s` is bounded by summing an arbitrary nonnegative bound
  `g` on `fv s - 1` over the box `[0, M)^4` (`gsum`), with the geometric tail `kk cap * tl4`
  outside the box. If the resulting bound on the abundancy is at most 2, this contradicts
  `abundancy N = 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ThreeFreeThree

/-! ## Analytic part -/

/-- The value `(s^2 + s + 1)/s^2`, the abundancy `σ(s^2)/s^2` when `s` is prime. -/
def fv (s : ℕ) : ℚ := ((s : ℚ) ^ 2 + s + 1) / s ^ 2

/-- The value `s/(s - 1)`, an upper bound for the abundancy of every power of a prime `s`. -/
def rv (s : ℕ) : ℚ := (s : ℚ) / (s - 1)

/-- The tail factor `1/(1 - 1/(2 (cap - 1)^2))`, an upper bound for the product of
`s³/(s³ - 1)` over any finite set of integers `s ≥ cap`. -/
def tailF (cap : ℕ) : ℚ := 1 / (1 - 1 / (2 * ((cap : ℚ) - 1) ^ 2))

/-- The constant `((cap + 1)/cap)^2`. -/
def kk (cap : ℕ) : ℚ := (((cap : ℚ) + 1) / cap) ^ 2

/-- The weight of an exponent vector with four coordinates. -/
def wt4 (α β γ δ : ℚ) (t : ℕ × ℕ × ℕ × ℕ) : ℚ :=
  α ^ t.1 * β ^ t.2.1 * γ ^ t.2.2.1 * δ ^ t.2.2.2

/-- Union bound tail outside the box `[0, M)^4`. -/
def tl4 (α β γ δ : ℚ) (M : ℕ) : ℚ :=
  (α ^ M + β ^ M + γ ^ M + δ ^ M) / ((1 - α) * (1 - β) * (1 - γ) * (1 - δ))

/-- Box sum of an arbitrary per vector bound, over vectors that are not all even. Stated with
nested sums over `Finset.range M` so that a later module can evaluate it. -/
def gsum (g : ℕ × ℕ × ℕ × ℕ → ℚ) (M : ℕ) : ℚ :=
  ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, ∑ c ∈ Finset.range M, ∑ d ∈ Finset.range M,
    if Even a ∧ Even b ∧ Even c ∧ Even d then 0 else g (a, b, c, d)

private theorem one_le_fv {s : ℕ} (hs : 1 ≤ s) : 1 ≤ fv s := by
  have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
  unfold fv
  rw [le_div_iff₀ (by positivity)]
  nlinarith

private theorem wt4_nonneg {α β γ δ : ℚ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (t : ℕ × ℕ × ℕ × ℕ) : 0 ≤ wt4 α β γ δ t := by
  unfold wt4; positivity

private theorem prod_one_add_le {ι : Type*} [DecidableEq ι] (T : Finset ι) (x : ι → ℚ)
    (hx : ∀ i ∈ T, 0 ≤ x i) : (∏ i ∈ T, (1 + x i)) * (1 - ∑ i ∈ T, x i) ≤ 1 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hxa := hx a (Finset.mem_insert_self a s)
    have hs := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hP : 0 ≤ ∏ i ∈ s, (1 + x i) :=
      Finset.prod_nonneg fun i hi => by linarith [hx i (Finset.mem_insert_of_mem hi)]
    have hsum : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    nlinarith [mul_nonneg hP (add_nonneg (mul_nonneg hxa hxa) (mul_nonneg hxa hsum))]

private theorem hyper_sum (α β γ δ : ℚ) (A B C D : Finset ℕ) :
    ∑ t ∈ A ×ˢ B ×ˢ C ×ˢ D, wt4 α β γ δ t =
      (∑ a ∈ A, α ^ a) * (∑ b ∈ B, β ^ b) * (∑ c ∈ C, γ ^ c) * (∑ d ∈ D, δ ^ d) := by
  rw [show (∑ a ∈ A, α ^ a) * (∑ b ∈ B, β ^ b) * (∑ c ∈ C, γ ^ c) * (∑ d ∈ D, δ ^ d) =
      (∑ a ∈ A, α ^ a) * ((∑ b ∈ B, β ^ b) * ((∑ c ∈ C, γ ^ c) * (∑ d ∈ D, δ ^ d))) by ring]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_product, wt4, mul_assoc]

/-- A sum of weights over vectors confined to `A × B × C × D`. -/
private theorem sum_le_hyper {α β γ δ : ℚ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) (T : Finset (ℕ × ℕ × ℕ × ℕ)) (A B C D : Finset ℕ)
    (hT : ∀ t ∈ T, t.1 ∈ A ∧ t.2.1 ∈ B ∧ t.2.2.1 ∈ C ∧ t.2.2.2 ∈ D) :
    ∑ t ∈ T, wt4 α β γ δ t ≤
      (∑ a ∈ A, α ^ a) * (∑ b ∈ B, β ^ b) * (∑ c ∈ C, γ ^ c) * (∑ d ∈ D, δ ^ d) := by
  rw [← hyper_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => wt4_nonneg hα hβ hγ hδ t)
  intro t ht
  obtain ⟨h1, h2, h3, h4⟩ := hT t ht
  simp only [Finset.mem_product]
  exact ⟨h1, h2, h3, h4⟩

private theorem tail4 (T : Finset (ℕ × ℕ × ℕ × ℕ)) (M : ℕ) {α β γ δ : ℚ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hT : ∀ t ∈ T, M ≤ t.1 ∨ M ≤ t.2.1 ∨ M ≤ t.2.2.1 ∨ M ≤ t.2.2.2) :
    ∑ t ∈ T, wt4 α β γ δ t ≤ tl4 α β γ δ M := by
  set K := T.sup (fun t => t.1 + t.2.1 + t.2.2.1 + t.2.2.2) + 1
  have hK : ∀ t ∈ T, t.1 < K ∧ t.2.1 < K ∧ t.2.2.1 < K ∧ t.2.2.2 < K := fun t ht => by
    have := Finset.le_sup (f := fun t => t.1 + t.2.1 + t.2.2.1 + t.2.2.2) ht
    omega
  have hw := wt4_nonneg hα0 hβ0 hγ0 hδ0
  have h1a : 0 < 1 - α := by linarith
  have h1b : 0 < 1 - β := by linarith
  have h1c : 0 < 1 - γ := by linarith
  have h1d : 0 < 1 - δ := by linarith
  have gα : ∑ i ∈ Finset.Ico M K, α ^ i ≤ α ^ M / (1 - α) := geom_sum_Ico_le_of_lt_one hα0 hα1
  have gβ : ∑ i ∈ Finset.Ico M K, β ^ i ≤ β ^ M / (1 - β) := geom_sum_Ico_le_of_lt_one hβ0 hβ1
  have gγ : ∑ i ∈ Finset.Ico M K, γ ^ i ≤ γ ^ M / (1 - γ) := geom_sum_Ico_le_of_lt_one hγ0 hγ1
  have gδ : ∑ i ∈ Finset.Ico M K, δ ^ i ≤ δ ^ M / (1 - δ) := geom_sum_Ico_le_of_lt_one hδ0 hδ1
  have fα : ∑ i ∈ Finset.Ico 0 K, α ^ i ≤ 1 / (1 - α) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hα0 hα1
  have fβ : ∑ i ∈ Finset.Ico 0 K, β ^ i ≤ 1 / (1 - β) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hβ0 hβ1
  have fγ : ∑ i ∈ Finset.Ico 0 K, γ ^ i ≤ 1 / (1 - γ) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hγ0 hγ1
  have fδ : ∑ i ∈ Finset.Ico 0 K, δ ^ i ≤ 1 / (1 - δ) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hδ0 hδ1
  have nn : ∀ (x : ℚ) (m : ℕ), 0 ≤ x → 0 ≤ ∑ i ∈ Finset.Ico m K, x ^ i :=
    fun x m hx => Finset.sum_nonneg fun _ _ => pow_nonneg hx _
  have sα := nn α M hα0
  have sβ := nn β M hβ0
  have sγ := nn γ M hγ0
  have sδ := nn δ M hδ0
  have sα' := nn α 0 hα0
  have sβ' := nn β 0 hβ0
  have sγ' := nn γ 0 hγ0
  have sδ' := nn δ 0 hδ0
  have hA : ∑ t ∈ T.filter (fun t => M ≤ t.1), wt4 α β γ δ t ≤
      α ^ M / (1 - α) * (1 / (1 - β)) * (1 / (1 - γ)) * (1 / (1 - δ)) := by
    refine le_trans (sum_le_hyper hα0 hβ0 hγ0 hδ0 _ (Finset.Ico M K) (Finset.Ico 0 K)
      (Finset.Ico 0 K) (Finset.Ico 0 K) fun t ht => ?_) ?_
    · rw [Finset.mem_filter] at ht
      have := hK t ht.1
      simp only [Finset.mem_Ico]
      omega
    · gcongr
  have hB : ∑ t ∈ T.filter (fun t => M ≤ t.2.1), wt4 α β γ δ t ≤
      1 / (1 - α) * (β ^ M / (1 - β)) * (1 / (1 - γ)) * (1 / (1 - δ)) := by
    refine le_trans (sum_le_hyper hα0 hβ0 hγ0 hδ0 _ (Finset.Ico 0 K) (Finset.Ico M K)
      (Finset.Ico 0 K) (Finset.Ico 0 K) fun t ht => ?_) ?_
    · rw [Finset.mem_filter] at ht
      have := hK t ht.1
      simp only [Finset.mem_Ico]
      omega
    · gcongr
  have hC : ∑ t ∈ T.filter (fun t => M ≤ t.2.2.1), wt4 α β γ δ t ≤
      1 / (1 - α) * (1 / (1 - β)) * (γ ^ M / (1 - γ)) * (1 / (1 - δ)) := by
    refine le_trans (sum_le_hyper hα0 hβ0 hγ0 hδ0 _ (Finset.Ico 0 K) (Finset.Ico 0 K)
      (Finset.Ico M K) (Finset.Ico 0 K) fun t ht => ?_) ?_
    · rw [Finset.mem_filter] at ht
      have := hK t ht.1
      simp only [Finset.mem_Ico]
      omega
    · gcongr
  have hD : ∑ t ∈ T.filter (fun t => M ≤ t.2.2.2), wt4 α β γ δ t ≤
      1 / (1 - α) * (1 / (1 - β)) * (1 / (1 - γ)) * (δ ^ M / (1 - δ)) := by
    refine le_trans (sum_le_hyper hα0 hβ0 hγ0 hδ0 _ (Finset.Ico 0 K) (Finset.Ico 0 K)
      (Finset.Ico 0 K) (Finset.Ico M K) fun t ht => ?_) ?_
    · rw [Finset.mem_filter] at ht
      have := hK t ht.1
      simp only [Finset.mem_Ico]
      omega
    · gcongr
  have hsplit : ∑ t ∈ T, wt4 α β γ δ t ≤
      ∑ t ∈ T.filter (fun t => M ≤ t.1), wt4 α β γ δ t +
      ∑ t ∈ T.filter (fun t => M ≤ t.2.1), wt4 α β γ δ t +
      ∑ t ∈ T.filter (fun t => M ≤ t.2.2.1), wt4 α β γ δ t +
      ∑ t ∈ T.filter (fun t => M ≤ t.2.2.2), wt4 α β γ δ t := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    have h0 := hw t
    have h := hT t ht
    split_ifs <;> first | omega | linarith
  have heq : α ^ M / (1 - α) * (1 / (1 - β)) * (1 / (1 - γ)) * (1 / (1 - δ)) +
      1 / (1 - α) * (β ^ M / (1 - β)) * (1 / (1 - γ)) * (1 / (1 - δ)) +
      1 / (1 - α) * (1 / (1 - β)) * (γ ^ M / (1 - γ)) * (1 / (1 - δ)) +
      1 / (1 - α) * (1 / (1 - β)) * (1 / (1 - γ)) * (δ ^ M / (1 - δ)) = tl4 α β γ δ M := by
    unfold tl4; field_simp
  linarith

/-- `fv s - 1` in closed form. -/
theorem fv_sub_one {s : ℕ} (hs : 1 ≤ s) : fv s - 1 = ((s : ℚ) + 1) / s ^ 2 := by
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  unfold fv; field_simp; ring

/-- For `s ≥ cap ≥ 1`, `fv s - 1 ≤ kk cap / (s + 1)`. -/
theorem fv_sub_le {cap s : ℕ} (hcap : 1 ≤ cap) (hs : cap ≤ s) :
    fv s - 1 ≤ kk cap / ((s : ℚ) + 1) := by
  have hc : (1 : ℚ) ≤ cap := by exact_mod_cast hcap
  have hcs : (cap : ℚ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℚ) < s := by linarith
  have e2 : ((s : ℚ) + 1) * cap ≤ (cap + 1) * s := by nlinarith
  have e3 : (((s : ℚ) + 1) * cap) ^ 2 ≤ ((cap + 1) * s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) e2 2
  rw [fv_sub_one (hcap.trans hs), kk, div_pow, div_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Rewriting `gsum` as a single sum over the box. -/
private theorem gsum_eq (g : ℕ × ℕ × ℕ × ℕ → ℚ) (M : ℕ) :
    gsum g M = ∑ t ∈ Finset.range M ×ˢ Finset.range M ×ˢ Finset.range M ×ˢ Finset.range M,
      (if Even t.1 ∧ Even t.2.1 ∧ Even t.2.2.1 ∧ Even t.2.2.2 then 0 else g t) := by
  simp only [gsum, Finset.sum_product]

/-- The product over the ordinary primes, from the small set `C`, the box bound `g`, and the
geometric tail. -/
private theorem prod_bound4 (S : Finset ℕ) (π : ℕ → ℕ × ℕ × ℕ × ℕ) (hinj : Set.InjOn π S)
    (cap M : ℕ) (hcap : 1 ≤ cap) {α β γ δ : ℚ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (C : Finset ℕ) (hC : ∀ x ∈ C, 1 ≤ x)
    (hS1 : ∀ s ∈ S, 1 ≤ s) (hsmall : ∀ s ∈ S, s < cap → s ∈ C)
    (hlarge : ∀ s ∈ S, cap ≤ s → 1 ≤ wt4 α β γ δ (π s) * ((s : ℚ) + 1))
    (hev : ∀ s ∈ S, ¬ (Even (π s).1 ∧ Even (π s).2.1 ∧ Even (π s).2.2.1 ∧ Even (π s).2.2.2))
    (g : ℕ × ℕ × ℕ × ℕ → ℚ) (hg0 : ∀ v, 0 ≤ g v)
    (hg : ∀ s ∈ S, cap ≤ s → (π s).1 < M → (π s).2.1 < M → (π s).2.2.1 < M →
      (π s).2.2.2 < M → fv s - 1 ≤ g (π s))
    (X : ℚ) (hX : gsum g M + kk cap * tl4 α β γ δ M ≤ X) (hX1 : X < 1) :
    ∏ s ∈ S, fv s ≤ (∏ s ∈ C, fv s) / (1 - X) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun s => s < cap)]
  set Sl := S.filter (fun s => s < cap)
  set Sg := S.filter (fun s => ¬ s < cap)
  have hfv0 : ∀ s ∈ S, 0 ≤ fv s := fun s hs => le_trans zero_le_one (one_le_fv (hS1 s hs))
  have h1 : ∏ s ∈ Sl, fv s ≤ ∏ s ∈ C, fv s := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro s hs; rw [Finset.mem_filter] at hs; exact hsmall s hs.1 hs.2
    · intro s hs; exact hfv0 s (Finset.mem_of_mem_filter s hs)
    · intro s hs _; exact one_le_fv (hC s hs)
  have hw := wt4_nonneg hα0 hβ0 hγ0 hδ0
  have hkk : 0 ≤ kk cap := by unfold kk; positivity
  let box : ℕ × ℕ × ℕ × ℕ → Prop := fun t => t.1 < M ∧ t.2.1 < M ∧ t.2.2.1 < M ∧ t.2.2.2 < M
  let y : ℕ × ℕ × ℕ × ℕ → ℚ := fun t => if box t then g t else kk cap * wt4 α β γ δ t
  have hx : ∀ s ∈ Sg, fv s - 1 ≤ y (π s) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    have hcs : cap ≤ s := by omega
    simp only [y]
    split_ifs with hb
    · exact hg s hs.1 hcs hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
    · refine le_trans (fv_sub_le hcap hcs) ?_
      have hwl := hlarge s hs.1 hcs
      rw [div_le_iff₀ (by positivity)]
      nlinarith
  set I := Sg.image π
  have hI : ∑ t ∈ I, y t ≤ X := by
    simp only [y]
    rw [Finset.sum_ite]
    have hb : ∑ t ∈ I.filter box, g t ≤ gsum g M := by
      rw [gsum_eq]
      calc ∑ t ∈ I.filter box, g t = ∑ t ∈ I.filter box,
            (if Even t.1 ∧ Even t.2.1 ∧ Even t.2.2.1 ∧ Even t.2.2.2 then 0 else g t) := by
            refine Finset.sum_congr rfl fun t ht => ?_
            rw [Finset.mem_filter, Finset.mem_image] at ht
            obtain ⟨⟨s, hs, rfl⟩, -⟩ := ht
            rw [if_neg (hev s (Finset.mem_of_mem_filter s hs))]
        _ ≤ _ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht
              obtain ⟨-, h1, h2, h3, h4⟩ := Finset.mem_filter.mp ht
              simp only [Finset.mem_product, Finset.mem_range]
              exact ⟨h1, h2, h3, h4⟩
            · intro t _ _
              split_ifs
              · exact le_rfl
              · exact hg0 t
    have ht : ∑ t ∈ I.filter (fun t => ¬ box t), kk cap * wt4 α β γ δ t ≤
        kk cap * tl4 α β γ δ M := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hkk
      apply tail4 _ M hα0 hα1 hβ0 hβ1 hγ0 hγ1 hδ0 hδ1
      intro t ht
      have := (Finset.mem_filter.mp ht).2
      simp only [box] at this
      omega
    linarith
  have hsum : ∑ s ∈ Sg, (fv s - 1) ≤ X := by
    calc ∑ s ∈ Sg, (fv s - 1) ≤ ∑ s ∈ Sg, y (π s) := Finset.sum_le_sum hx
      _ = ∑ t ∈ I, y t := by
          rw [Finset.sum_image fun x hx y hy =>
            hinj (Finset.mem_of_mem_filter x hx) (Finset.mem_of_mem_filter y hy)]
      _ ≤ X := hI
  have hx0 : ∀ s ∈ Sg, 0 ≤ fv s - 1 := fun s hs =>
    sub_nonneg.mpr (one_le_fv (hS1 s (Finset.mem_of_mem_filter s hs)))
  have hG := prod_one_add_le Sg (fun s => fv s - 1) hx0
  simp only [add_sub_cancel] at hG
  have hP0 : 0 ≤ ∏ s ∈ Sg, fv s :=
    Finset.prod_nonneg fun s hs => hfv0 s (Finset.mem_of_mem_filter s hs)
  have h2 : ∏ s ∈ Sg, fv s ≤ 1 / (1 - X) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hC0 : 0 ≤ ∏ s ∈ C, fv s :=
    Finset.prod_nonneg fun s hs => le_trans zero_le_one (one_le_fv (hC s hs))
  calc _ ≤ (∏ s ∈ C, fv s) * (1 / (1 - X)) := mul_le_mul h1 h2 hP0 hC0
    _ = _ := by ring

/-- `rv s ≥ 1` for `s ≥ 2`. -/
theorem one_le_rv {s : ℕ} (hs : 2 ≤ s) : 1 ≤ rv s := by
  have hs' : (2 : ℚ) ≤ s := by exact_mod_cast hs
  unfold rv
  rw [le_div_iff₀ (by linarith)]
  linarith

private theorem cube_pos {b : ℚ} (hb : 2 ≤ b) : 0 < b ^ 3 - 1 := by
  have := pow_le_pow_left₀ (by norm_num) hb 3
  norm_num at this
  linarith

/-- One step of the telescoping bound: `1/(b³ - 1) ≤ 1/(2 (b - 1)^2) - 1/(2 b^2)` for `b ≥ 2`. -/
private theorem cube_step {b : ℚ} (hb : 2 ≤ b) :
    1 / (b ^ 3 - 1) ≤ 1 / (2 * (b - 1) ^ 2) - 1 / (2 * b ^ 2) := by
  have h1 : 0 < b - 1 := by linarith
  have h3 := cube_pos hb
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ h3 (by positivity)]
  have ht : 0 ≤ b - 2 := by linarith
  nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht, mul_nonneg ht h1.le]

/-- The telescoping sum of `1/(s³ - 1)` over `cap ≤ s < cap + n`. -/
private theorem cube_sum (cap : ℕ) (hcap : 2 ≤ cap) : ∀ n : ℕ,
    ∑ s ∈ Finset.Ico cap (cap + n), 1 / ((s : ℚ) ^ 3 - 1) ≤
      1 / (2 * ((cap : ℚ) - 1) ^ 2) - 1 / (2 * (((cap + n : ℕ) : ℚ) - 1) ^ 2)
  | 0 => by simp
  | n + 1 => by
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have ih := cube_sum cap hcap n
    have hb : (2 : ℚ) ≤ ((cap + n : ℕ) : ℚ) := by exact_mod_cast (show 2 ≤ cap + n by omega)
    have key := cube_step hb
    have e : (((cap + n + 1 : ℕ) : ℚ) - 1) = ((cap + n : ℕ) : ℚ) := by push_cast; ring
    rw [e]
    linarith

/-- The product of `s³/(s³ - 1) = 1 + 1/(s³ - 1)` over a finite set of integers `s ≥ cap` is
at most `tailF cap`, so the product of `rv s` is at most `tailF cap` times the product of
`fv s`. -/
private theorem prod_rv_le (cap : ℕ) (hcap : 2 ≤ cap) (T : Finset ℕ) (hT : ∀ s ∈ T, cap ≤ s) :
    ∏ s ∈ T, rv s ≤ tailF cap * ∏ s ∈ T, fv s := by
  classical
  set x : ℕ → ℚ := fun s => 1 / ((s : ℚ) ^ 3 - 1)
  have hs2 : ∀ s ∈ T, (2 : ℚ) ≤ s := fun s hs => by exact_mod_cast hcap.trans (hT s hs)
  have hx0 : ∀ s ∈ T, 0 ≤ x s := fun s hs => by
    exact (one_div_pos.mpr (cube_pos (hs2 s hs))).le
  have hrv : ∀ s ∈ T, rv s = fv s * (1 + x s) := fun s hs => by
    have h2 := hs2 s hs
    have h0 : (s : ℚ) ≠ 0 := by positivity
    have h1 : (s : ℚ) - 1 ≠ 0 := by linarith
    have h3 : (s : ℚ) ^ 3 - 1 ≠ 0 := (cube_pos h2).ne'
    simp only [rv, fv, x]
    field_simp
    ring
  rw [Finset.prod_congr rfl hrv, Finset.prod_mul_distrib]
  set K := T.sup id + 1
  have hsub : T ⊆ Finset.Ico cap (cap + K) := fun s hs => by
    have := Finset.le_sup (f := id) hs
    simp only [id] at this
    rw [Finset.mem_Ico]
    exact ⟨hT s hs, by omega⟩
  have hc : (2 : ℚ) ≤ cap := by exact_mod_cast hcap
  have hlast : 0 ≤ 1 / (2 * (((cap + K : ℕ) : ℚ) - 1) ^ 2) := by
    have : (2 : ℚ) ≤ ((cap + K : ℕ) : ℚ) := by exact_mod_cast (show 2 ≤ cap + K by omega)
    have : 0 < (((cap + K : ℕ) : ℚ) - 1) := by linarith
    positivity
  have hsum : ∑ s ∈ T, x s ≤ 1 / (2 * ((cap : ℚ) - 1) ^ 2) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun s hs _ => ?_) ?_
    · have : (2 : ℚ) ≤ s := by
        have := (Finset.mem_Ico.mp hs).1
        exact_mod_cast hcap.trans this
      exact (one_div_pos.mpr (cube_pos this)).le
    · linarith [cube_sum cap hcap K]
  have he : 1 / (2 * ((cap : ℚ) - 1) ^ 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hG := prod_one_add_le T x hx0
  have hP0 : 0 ≤ ∏ s ∈ T, (1 + x s) := Finset.prod_nonneg fun s hs => by linarith [hx0 s hs]
  have hF0 : 0 ≤ ∏ s ∈ T, fv s := Finset.prod_nonneg fun s hs =>
    zero_le_one.trans (one_le_fv (by have := hcap.trans (hT s hs); omega))
  have hpos : 0 < 1 - 1 / (2 * ((cap : ℚ) - 1) ^ 2) := by linarith
  have h2 : ∏ s ∈ T, (1 + x s) ≤ tailF cap := by
    unfold tailF
    rw [le_div_iff₀ hpos]
    nlinarith
  calc (∏ s ∈ T, fv s) * ∏ s ∈ T, (1 + x s) ≤ (∏ s ∈ T, fv s) * tailF cap :=
        mul_le_mul_of_nonneg_left h2 hF0
    _ = _ := by ring

/-! ## The arithmetic setting -/

/-- The core case: `q, r₁, r₂, r₃` are distinct prime factors of the odd perfect number `N`,
`q` is the special prime, every other prime factor has an exponent `e` with `3 ∣ e + 1`, and
`3 ∤ N`. -/
structure Ctx4 (N q r₁ r₂ r₃ : ℕ) : Prop where
  opn : OddPerfect N
  hq : q.Prime
  hodd : Odd (N.factorization q)
  hr₁ : r₁ ∈ N.primeFactors
  hr₂ : r₂ ∈ N.primeFactors
  hr₃ : r₃ ∈ N.primeFactors
  h12 : r₁ ≠ r₂
  h13 : r₁ ≠ r₃
  h23 : r₂ ≠ r₃
  h1q : r₁ ≠ q
  h2q : r₂ ≠ q
  h3q : r₃ ≠ q
  hmod : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → 3 ∣ N.factorization p + 1
  h3 : ¬ 3 ∣ N

variable {N q r₁ r₂ r₃ : ℕ}

/-- Exchanging `r₁` and `r₂`. -/
theorem Ctx4.swap12 (c : Ctx4 N q r₁ r₂ r₃) : Ctx4 N q r₂ r₁ r₃ where
  opn := c.opn
  hq := c.hq
  hodd := c.hodd
  hr₁ := c.hr₂
  hr₂ := c.hr₁
  hr₃ := c.hr₃
  h12 := c.h12.symm
  h13 := c.h23
  h23 := c.h13
  h1q := c.h2q
  h2q := c.h1q
  h3q := c.h3q
  hmod := fun p hp ha hb hc hd => c.hmod p hp ha hc hb hd
  h3 := c.h3

/-- Exchanging `r₂` and `r₃`. -/
theorem Ctx4.swap23 (c : Ctx4 N q r₁ r₂ r₃) : Ctx4 N q r₁ r₃ r₂ where
  opn := c.opn
  hq := c.hq
  hodd := c.hodd
  hr₁ := c.hr₁
  hr₂ := c.hr₃
  hr₃ := c.hr₂
  h12 := c.h13
  h13 := c.h12
  h23 := c.h23.symm
  h1q := c.h1q
  h2q := c.h3q
  h3q := c.h2q
  hmod := fun p hp ha hb hc hd => c.hmod p hp ha hb hd hc
  h3 := c.h3

/-- Padding of the labels: if `3 ∤ N`, there are three distinct prime factors `a, b, d` of `N`,
all different from `q`, such that every prime factor of `N` other than `q, a, b, d` has an
exponent `e` with `3 ∣ e + 1`. They are chosen to contain every `rᵢ` that is a prime factor of
`N` other than `q`; the hypothesis only gets weaker when the set of labels grows. -/
theorem ctx4_of_not_three_dvd {N q r₁ r₂ r₃ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hmod : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → 3 ∣ N.factorization p + 1)
    (h3 : ¬ 3 ∣ N) : ∃ a b d, Ctx4 N q a b d := by
  classical
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos hodd.pos.ne', h.ne_zero⟩
  set P := N.primeFactors.erase q
  have hP : 3 ≤ P.card := by
    have := four_le_card_primeFactors h
    rw [Finset.card_erase_of_mem hqN]
    omega
  set R := P.filter fun p => p = r₁ ∨ p = r₂ ∨ p = r₃
  have hR : R.card ≤ 3 := by
    refine le_trans (Finset.card_le_card (t := {r₁, r₂, r₃}) fun p hp => ?_) Finset.card_le_three
    obtain ⟨-, hp⟩ := Finset.mem_filter.mp hp
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hp
  obtain ⟨R', hRR', hR'P, hcard⟩ := Finset.exists_subsuperset_card_eq (Finset.filter_subset _ P) hR hP
  obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Finset.card_eq_three.mp hcard
  have mem : ∀ x ∈ ({a, b, d} : Finset ℕ), x ∈ N.primeFactors ∧ x ≠ q := fun x hx => by
    have := Finset.mem_erase.mp (hR'P hx)
    exact ⟨this.2, this.1⟩
  have ha := mem a (by simp)
  have hb := mem b (by simp)
  have hd := mem d (by simp)
  refine ⟨a, b, d, h, hq, hodd, ha.1, hb.1, hd.1, hab, had, hbd, ha.2, hb.2, hd.2, ?_, h3⟩
  intro p hp hpq hpa hpb hpd
  have hnot : p ∉ R := fun hm => by
    have := hRR' hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  have hpP : p ∈ P := Finset.mem_erase.mpr ⟨hpq, hp⟩
  refine hmod p hp hpq ?_ ?_ ?_ <;> rintro rfl <;> exact hnot (Finset.mem_filter.mpr ⟨hpP, by tauto⟩)

/-- The ordinary prime factors. -/
def ord4 (N q r₁ r₂ r₃ : ℕ) : Finset ℕ :=
  (((N.primeFactors.erase q).erase r₁).erase r₂).erase r₃

/-- Membership in `ord4`. -/
theorem mem_ord4 {s : ℕ} :
    s ∈ ord4 N q r₁ r₂ r₃ ↔ s ∈ N.primeFactors ∧ s ≠ q ∧ s ≠ r₁ ∧ s ≠ r₂ ∧ s ≠ r₃ := by
  simp only [ord4, Finset.mem_erase]
  tauto

/-- The exponent vector of an ordinary prime: the exponents of `q, r₁, r₂, r₃` in
`1 + s + s^2`. -/
def vec4 (q r₁ r₂ r₃ s : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((1 + s + s ^ 2).factorization q, (1 + s + s ^ 2).factorization r₁,
    (1 + s + s ^ 2).factorization r₂, (1 + s + s ^ 2).factorization r₃)

private theorem sigma_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

/-- The special prime is `1` modulo 12. -/
theorem Ctx4.q_mod (c : Ctx4 N q r₁ r₂ r₃) : q % 12 = 1 := by
  have hN := c.opn
  have hqN : q ∣ N := Nat.dvd_of_factorization_pos c.hodd.pos.ne'
  have hq4 : q % 4 = 1 := by
    obtain ⟨q', hq', -, hq4, hk, -⟩ := exists_special_prime hN
    have := (existsUnique_odd_exponent hN).unique ⟨c.hq, c.hodd⟩
      ⟨hq', Nat.odd_iff.mpr (by omega)⟩
    rw [this]; exact hq4
  have h0 : q % 3 ≠ 0 := fun h0 => c.h3 ((Nat.dvd_of_mod_eq_zero h0).trans hqN)
  have h2 : q % 3 ≠ 2 := by
    intro h2
    have hd : σ 1 (q ^ 1) ∣ σ 1 (q ^ N.factorization q) :=
      OPNExample.sigma_prime_pow_dvd c.hq (by
        obtain ⟨j, hj⟩ := c.hodd; exact ⟨j + 1, by omega⟩)
    have h1 : σ 1 (q ^ 1) = 1 + q := by
      rw [sigma_one_apply_prime_pow c.hq]; simp [Finset.sum_range_succ]
    have h3q : 3 ∣ σ 1 (q ^ 1) := by rw [h1]; omega
    have := (h3q.trans hd).trans (OPNStarter.component_sigma_dvd hN.perfect c.hq rfl)
    exact c.h3 (Nat.Coprime.dvd_of_dvd_mul_left (by decide) this)
  omega

/-- Every prime factor of `N` is at least 5 and prime to 3. -/
theorem Ctx4.five_le (c : Ctx4 N q r₁ r₂ r₃) {p : ℕ} (hp : p ∈ N.primeFactors) :
    5 ≤ p ∧ p % 3 ≠ 0 := by
  obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
  have h3 : p % 3 ≠ 0 := fun h0 => c.h3 ((Nat.dvd_of_mod_eq_zero h0).trans hpN)
  refine ⟨?_, h3⟩
  by_contra hc
  interval_cases p
  · exact absurd hpp (by norm_num)
  · exact absurd hpp (by norm_num)
  · exact c.opn.not_two_dvd hpN
  · omega
  · exact absurd hpp (by norm_num)

/-- Each `rᵢ` is prime, at least 5, and prime to 3. -/
theorem Ctx4.r_prime (c : Ctx4 N q r₁ r₂ r₃) :
    (r₁.Prime ∧ 5 ≤ r₁ ∧ r₁ % 3 ≠ 0) ∧ (r₂.Prime ∧ 5 ≤ r₂ ∧ r₂ % 3 ≠ 0) ∧
      (r₃.Prime ∧ 5 ≤ r₃ ∧ r₃ % 3 ≠ 0) :=
  ⟨⟨Nat.prime_of_mem_primeFactors c.hr₁, c.five_le c.hr₁⟩,
    ⟨Nat.prime_of_mem_primeFactors c.hr₂, c.five_le c.hr₂⟩,
    ⟨Nat.prime_of_mem_primeFactors c.hr₃, c.five_le c.hr₃⟩⟩

/-- If `3 ∤ N` and a prime factor `s` of the odd perfect number `N` has an exponent `e` with
`3 ∣ e + 1`, then `1 + s + s^2` divides `σ(s^e)` and hence `N`, and `s ≡ 2 (mod 3)`. -/
theorem cyc_dvd_of_mod {N s : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) (hs : s ∈ N.primeFactors)
    (he : 3 ∣ N.factorization s + 1) : 1 + s + s ^ 2 ∣ N ∧ s % 3 = 2 := by
  obtain ⟨hsp, hsN, -⟩ := Nat.mem_primeFactors.mp hs
  have h1 : σ 1 (s ^ 2) ∣ σ 1 (s ^ N.factorization s) := OPNExample.sigma_prime_pow_dvd hsp he
  have h2 := h1.trans (OPNStarter.component_sigma_dvd h.perfect hsp rfl)
  rw [sigma_sq hsp] at h2
  have hodd : Odd (1 + s + s ^ 2) := by
    have : Even (s + s ^ 2) := by
      rw [show s + s ^ 2 = s * (s + 1) by ring]
      exact Nat.even_mul_succ_self s
    rw [add_assoc]
    exact this.one_add
  have hdvd : 1 + s + s ^ 2 ∣ N :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hodd)) h2
  refine ⟨hdvd, ?_⟩
  have h0 : s % 3 ≠ 0 := fun h0 => h3 ((Nat.dvd_of_mod_eq_zero h0).trans hsN)
  have h1' : s % 3 ≠ 1 := by
    intro h1'
    obtain ⟨k, hk⟩ : ∃ k, s = 3 * k + 1 := ⟨s / 3, by omega⟩
    apply h3
    refine dvd_trans ⟨3 * k ^ 2 + 3 * k + 1, ?_⟩ hdvd
    subst hk
    ring
  omega

/-- An ordinary prime is prime, has an exponent `e` with `3 ∣ e + 1`, is at least 5, and is
`2` modulo 3. -/
theorem Ctx4.ord_facts {s : ℕ} (c : Ctx4 N q r₁ r₂ r₃) (hs : s ∈ ord4 N q r₁ r₂ r₃) :
    s.Prime ∧ 3 ∣ N.factorization s + 1 ∧ 5 ≤ s ∧ s % 3 = 2 := by
  obtain ⟨hsN, h1, h2, h3, h4⟩ := mem_ord4.mp hs
  have hsp := Nat.prime_of_mem_primeFactors hsN
  have he := c.hmod s hsN h1 h2 h3 h4
  exact ⟨hsp, he, (c.five_le hsN).1, (cyc_dvd_of_mod c.opn c.h3 hsN he).2⟩

/-- None of `q, r₁, r₂, r₃` is ordinary. -/
theorem Ctx4.not_mem_ord (_c : Ctx4 N q r₁ r₂ r₃) :
    q ∉ ord4 N q r₁ r₂ r₃ ∧ r₁ ∉ ord4 N q r₁ r₂ r₃ ∧ r₂ ∉ ord4 N q r₁ r₂ r₃ ∧
      r₃ ∉ ord4 N q r₁ r₂ r₃ := by
  simp only [mem_ord4]
  tauto

/-- Every prime factor of `1 + s + s^2`, for an ordinary `s`, is one of `q, r₁, r₂, r₃` and
is `1` modulo 3. -/
theorem Ctx4.tgt {s : ℕ} (c : Ctx4 N q r₁ r₂ r₃) (hs : s ∈ ord4 N q r₁ r₂ r₃) {d : ℕ}
    (hd : d.Prime) (hdd : d ∣ 1 + s + s ^ 2) :
    (d = q ∨ d = r₁ ∨ d = r₂ ∨ d = r₃) ∧ d % 3 = 1 := by
  obtain ⟨-, he, -⟩ := c.ord_facts hs
  have hdN : d ∣ N := hdd.trans (cyc_dvd_of_mod c.opn c.h3 (mem_ord4.mp hs).1 he).1
  have hd3' : d ≠ 3 := by rintro rfl; exact c.h3 hdN
  have hd3 : d % 3 = 1 := OPNThreeFree.target_mod_three hd hd3' hdd
  refine ⟨?_, hd3⟩
  by_contra hc
  simp only [not_or] at hc
  have hord : d ∈ ord4 N q r₁ r₂ r₃ := mem_ord4.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hd, hdN, c.opn.ne_zero⟩, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  have := (c.ord_facts hord).2.2.2
  omega

private theorem ne_sq {p m : ℕ} (hp : 0 < p) : 1 + p + p ^ 2 ≠ m ^ 2 := by
  intro h
  have h1 : p ^ 2 < m ^ 2 := by rw [← h]; omega
  have h2 : m ^ 2 < (p + 1) ^ 2 := by rw [← h]; nlinarith
  have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h1
  have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
  omega

/-- For an ordinary `s`, `1 + s + s^2` is a product of powers of the four primes, with
exponents not all even. -/
theorem Ctx4.shape {s : ℕ} (c : Ctx4 N q r₁ r₂ r₃) (hs : s ∈ ord4 N q r₁ r₂ r₃) :
    1 + s + s ^ 2 = q ^ (vec4 q r₁ r₂ r₃ s).1 * r₁ ^ (vec4 q r₁ r₂ r₃ s).2.1 *
      r₂ ^ (vec4 q r₁ r₂ r₃ s).2.2.1 * r₃ ^ (vec4 q r₁ r₂ r₃ s).2.2.2 ∧
    ¬ (Even (vec4 q r₁ r₂ r₃ s).1 ∧ Even (vec4 q r₁ r₂ r₃ s).2.1 ∧
       Even (vec4 q r₁ r₂ r₃ s).2.2.1 ∧ Even (vec4 q r₁ r₂ r₃ s).2.2.2) := by
  have hs0 : 0 < s := (c.ord_facts hs).1.pos
  have hne : 1 + s + s ^ 2 ≠ 0 := by positivity
  have heq : 1 + s + s ^ 2 = q ^ (vec4 q r₁ r₂ r₃ s).1 * r₁ ^ (vec4 q r₁ r₂ r₃ s).2.1 *
      r₂ ^ (vec4 q r₁ r₂ r₃ s).2.2.1 * r₃ ^ (vec4 q r₁ r₂ r₃ s).2.2.2 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hne]
    rw [Finsupp.prod_of_support_subset _ (s := {q, r₁, r₂, r₃}) _ _ (fun _ _ => pow_zero _),
      Finset.prod_insert (by simp [c.h1q.symm, c.h2q.symm, c.h3q.symm]),
      Finset.prod_insert (by simp [c.h12, c.h13]),
      Finset.prod_pair c.h23]
    · simp only [vec4]; ring
    intro t ht
    rw [Nat.support_factorization] at ht
    have := (c.tgt hs (Nat.prime_of_mem_primeFactors ht) (Nat.dvd_of_mem_primeFactors ht)).1
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  refine ⟨heq, ?_⟩
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩, ⟨l, hl⟩⟩
  apply ne_sq hs0 (m := q ^ i * r₁ ^ j * r₂ ^ k * r₃ ^ l)
  rw [heq, hi, hj, hk, hl]
  ring

/-- A prime factor of `N` that is `2` modulo 3 never divides `1 + s + s^2` for an ordinary
`s`; in particular its coordinate of `vec4` is 0. -/
theorem Ctx4.vec_zero {s : ℕ} (c : Ctx4 N q r₁ r₂ r₃) (hs : s ∈ ord4 N q r₁ r₂ r₃)
    {r : ℕ} (hr : r ∈ N.primeFactors) (h2 : r % 3 = 2) :
    (1 + s + s ^ 2).factorization r = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  have := (c.tgt hs (Nat.prime_of_mem_primeFactors hr) hd).2
  omega

/-- The exponent vector determines the ordinary prime. -/
theorem Ctx4.vec_inj (c : Ctx4 N q r₁ r₂ r₃) :
    Set.InjOn (vec4 q r₁ r₂ r₃) (ord4 N q r₁ r₂ r₃) := by
  intro x hx y hy hxy
  have ex := (c.shape hx).1
  have ey := (c.shape hy).1
  have hF : 1 + x + x ^ 2 = 1 + y + y ^ 2 := by rw [ex, ey, hxy]
  rcases lt_trichotomy x y with hlt | heq | hgt
  · nlinarith
  · exact heq
  · nlinarith

private theorem pow_ge_one_of {x : ℚ} {r : ℕ} (e : ℕ) (h : 1 ≤ x ^ 2 * r ∨ e = 0) :
    1 ≤ (x ^ 2 * r) ^ e := by
  rcases h with h | h
  · exact one_le_pow₀ h
  · simp [h]

/-- The weight inequality for an ordinary prime. -/
theorem Ctx4.weight {s : ℕ} (c : Ctx4 N q r₁ r₂ r₃) (hs : s ∈ ord4 N q r₁ r₂ r₃)
    {α β γ δ : ℚ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ) (hδ0 : 0 ≤ δ)
    (hα : 1 ≤ α ^ 2 * q ∨ q % 3 = 2) (hβ : 1 ≤ β ^ 2 * r₁ ∨ r₁ % 3 = 2)
    (hγ : 1 ≤ γ ^ 2 * r₂ ∨ r₂ % 3 = 2) (hδ : 1 ≤ δ ^ 2 * r₃ ∨ r₃ % 3 = 2) :
    1 ≤ wt4 α β γ δ (vec4 q r₁ r₂ r₃ s) * ((s : ℚ) + 1) := by
  have hqT : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨c.hq, Nat.dvd_of_factorization_pos c.hodd.pos.ne', c.opn.ne_zero⟩
  set v := vec4 q r₁ r₂ r₃ s
  have hA : 1 ≤ (α ^ 2 * q) ^ v.1 := pow_ge_one_of _ (hα.imp id (c.vec_zero hs hqT))
  have hB : 1 ≤ (β ^ 2 * r₁) ^ v.2.1 := pow_ge_one_of _ (hβ.imp id (c.vec_zero hs c.hr₁))
  have hC : 1 ≤ (γ ^ 2 * r₂) ^ v.2.2.1 := pow_ge_one_of _ (hγ.imp id (c.vec_zero hs c.hr₂))
  have hD : 1 ≤ (δ ^ 2 * r₃) ^ v.2.2.2 := pow_ge_one_of _ (hδ.imp id (c.vec_zero hs c.hr₃))
  have hsh := (c.shape hs).1
  set V : ℕ := q ^ v.1 * r₁ ^ v.2.1 * r₂ ^ v.2.2.1 * r₃ ^ v.2.2.2 with hV
  have hlt : (V : ℚ) < ((s : ℚ) + 1) ^ 2 := by
    have : V < (s + 1) ^ 2 := by rw [← hsh]; nlinarith [(c.ord_facts hs).2.2.1]
    exact_mod_cast this
  set w := wt4 α β γ δ v
  have hw0 : 0 ≤ w := wt4_nonneg hα0 hβ0 hγ0 hδ0 v
  have hwV : 1 ≤ w ^ 2 * (V : ℚ) := by
    have : w ^ 2 * (V : ℚ) = (α ^ 2 * q) ^ v.1 * (β ^ 2 * r₁) ^ v.2.1 *
        (γ ^ 2 * r₂) ^ v.2.2.1 * (δ ^ 2 * r₃) ^ v.2.2.2 := by
      simp only [w, wt4, hV]
      push_cast
      ring
    rw [this]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hB) hC) hD
  have h2 : 1 ≤ (w * ((s : ℚ) + 1)) ^ 2 := by
    rw [mul_pow]
    have hV0 : (0 : ℚ) ≤ (V : ℚ) := by positivity
    nlinarith [sq_nonneg w]
  nlinarith [mul_nonneg hw0 (by positivity : (0 : ℚ) ≤ (s : ℚ) + 1)]

/-- For an ordinary `s ≥ cap`, `fv s - 1` is at most `kk cap` times the smaller of `1/cap` and
the weight of its vector. -/
theorem Ctx4.fv_sub_le_min {s : ℕ} (c : Ctx4 N q r₁ r₂ r₃) (hs : s ∈ ord4 N q r₁ r₂ r₃)
    {cap : ℕ} (hcap : 1 ≤ cap) (hcs : cap ≤ s)
    {α β γ δ : ℚ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ) (hδ0 : 0 ≤ δ)
    (hα : 1 ≤ α ^ 2 * q ∨ q % 3 = 2) (hβ : 1 ≤ β ^ 2 * r₁ ∨ r₁ % 3 = 2)
    (hγ : 1 ≤ γ ^ 2 * r₂ ∨ r₂ % 3 = 2) (hδ : 1 ≤ δ ^ 2 * r₃ ∨ r₃ % 3 = 2) :
    fv s - 1 ≤ kk cap * min (1 / (cap : ℚ)) (wt4 α β γ δ (vec4 q r₁ r₂ r₃ s)) := by
  have hkk : 0 ≤ kk cap := by unfold kk; positivity
  have hcs' : (cap : ℚ) ≤ s := by exact_mod_cast hcs
  have hc' : (1 : ℚ) ≤ cap := by exact_mod_cast hcap
  have hwl := c.weight hs hα0 hβ0 hγ0 hδ0 hα hβ hγ hδ
  refine le_trans (fv_sub_le hcap hcs) ?_
  rw [mul_min_of_nonneg _ _ hkk]
  refine le_min ?_ ?_
  · rw [mul_one_div]
    exact div_le_div_of_nonneg_left hkk (by positivity) (by linarith)
  · rw [div_le_iff₀ (by positivity)]
    nlinarith

private theorem abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy; positivity

/-- The abundancy of `N` is 2, and the abundancy of each prime power factor `p^e` is below
`p/(p - 1)`, which gives a strict inequality. -/
theorem Ctx4.abund_lt (c : Ctx4 N q r₁ r₂ r₃) :
    2 < (q : ℚ) / (q - 1) * ((r₁ : ℚ) / (r₁ - 1)) * ((r₂ : ℚ) / (r₂ - 1)) *
      ((r₃ : ℚ) / (r₃ - 1)) * ∏ s ∈ ord4 N q r₁ r₂ r₃, rv s := by
  have hN := c.opn
  have hN0 := hN.ne_zero
  have hqT : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨c.hq, Nat.dvd_of_factorization_pos c.hodd.pos.ne', hN0⟩
  have hr1T : r₁ ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨c.h1q, c.hr₁⟩
  have hr2T : r₂ ∈ (N.primeFactors.erase q).erase r₁ :=
    Finset.mem_erase.mpr ⟨c.h12.symm, Finset.mem_erase.mpr ⟨c.h2q, c.hr₂⟩⟩
  have hr3T : r₃ ∈ ((N.primeFactors.erase q).erase r₁).erase r₂ :=
    Finset.mem_erase.mpr ⟨c.h23.symm, Finset.mem_erase.mpr ⟨c.h13.symm,
      Finset.mem_erase.mpr ⟨c.h3q, c.hr₃⟩⟩⟩
  have hab := (perfect_iff_abundancy_eq_two hN.pos).mp hN.perfect
  rw [abundancy_eq_prod_primeFactors hN0, ← Finset.mul_prod_erase _ _ hqT,
    ← Finset.mul_prod_erase _ _ hr1T, ← Finset.mul_prod_erase _ _ hr2T,
    ← Finset.mul_prod_erase _ _ hr3T] at hab
  change abundancy _ * (abundancy _ * (abundancy _ * (abundancy _ *
    ∏ x ∈ ord4 N q r₁ r₂ r₃, _))) = 2 at hab
  set A := ∏ x ∈ ord4 N q r₁ r₂ r₃, abundancy (x ^ N.factorization x)
  have hA0 : 0 ≤ A := Finset.prod_nonneg fun x _ => abundancy_nonneg _
  have hle : A ≤ ∏ s ∈ ord4 N q r₁ r₂ r₃, rv s :=
    Finset.prod_le_prod (fun x _ => abundancy_nonneg _)
      fun x hx => (abundancy_prime_pow_lt (c.ord_facts hx).1 _).le
  have hP : 0 < ∏ s ∈ ord4 N q r₁ r₂ r₃, rv s := Finset.prod_pos fun s hs =>
    lt_of_lt_of_le zero_lt_one (one_le_rv (le_trans (by norm_num) (c.ord_facts hs).2.2.1))
  have hgq := abundancy_prime_pow_lt c.hq (N.factorization q)
  have hg1 := abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors c.hr₁) (N.factorization r₁)
  have hg2 := abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors c.hr₂) (N.factorization r₂)
  have hg3 := abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors c.hr₃) (N.factorization r₃)
  have h0q := abundancy_nonneg (q ^ N.factorization q)
  have h01 := abundancy_nonneg (r₁ ^ N.factorization r₁)
  have h02 := abundancy_nonneg (r₂ ^ N.factorization r₂)
  have h03 := abundancy_nonneg (r₃ ^ N.factorization r₃)
  have e3 : abundancy (r₃ ^ N.factorization r₃) * A <
      (r₃ : ℚ) / (r₃ - 1) * ∏ s ∈ ord4 N q r₁ r₂ r₃, rv s :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle h03) (mul_lt_mul_of_pos_right hg3 hP)
  have e2 := mul_lt_mul'' hg2 e3 h02 (mul_nonneg h03 hA0)
  have e1 := mul_lt_mul'' hg1 e2 h01 (mul_nonneg h02 (mul_nonneg h03 hA0))
  have e0 := mul_lt_mul'' hgq e1 h0q (mul_nonneg h01 (mul_nonneg h02 (mul_nonneg h03 hA0)))
  rw [hab] at e0
  calc (2 : ℚ) < _ := e0
    _ = _ := by ring

private theorem div_pred_pos {p : ℕ} (hp : 2 ≤ p) : 0 < (p : ℚ) / (p - 1) := by
  have : (2 : ℚ) ≤ p := by exact_mod_cast hp
  apply div_pos <;> linarith

/-- The closing theorem: the abundancy bound from the small ordinary primes in `C`, the tail
factor `tailF cap`, the box bound `g`, and the geometric tail is at most 2, which is
impossible. -/
theorem Ctx4.close (c : Ctx4 N q r₁ r₂ r₃) (cap M : ℕ) (hcap : 2 ≤ cap)
    {α β γ δ ρ₀ ρ₁ ρ₂ ρ₃ : ℚ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hα : 1 ≤ α ^ 2 * q ∨ q % 3 = 2) (hβ : 1 ≤ β ^ 2 * r₁ ∨ r₁ % 3 = 2)
    (hγ : 1 ≤ γ ^ 2 * r₂ ∨ r₂ % 3 = 2) (hδ : 1 ≤ δ ^ 2 * r₃ ∨ r₃ % 3 = 2)
    (hρ₀ : (q : ℚ) / (q - 1) ≤ ρ₀) (hρ₁ : (r₁ : ℚ) / (r₁ - 1) ≤ ρ₁)
    (hρ₂ : (r₂ : ℚ) / (r₂ - 1) ≤ ρ₂) (hρ₃ : (r₃ : ℚ) / (r₃ - 1) ≤ ρ₃)
    (C : Finset ℕ) (hC : ∀ x ∈ C, 2 ≤ x)
    (hsmall : ∀ s ∈ ord4 N q r₁ r₂ r₃, s < cap → s ∈ C)
    (g : ℕ × ℕ × ℕ × ℕ → ℚ) (hg0 : ∀ v, 0 ≤ g v)
    (hg : ∀ s ∈ ord4 N q r₁ r₂ r₃, cap ≤ s →
      (vec4 q r₁ r₂ r₃ s).1 < M → (vec4 q r₁ r₂ r₃ s).2.1 < M →
      (vec4 q r₁ r₂ r₃ s).2.2.1 < M → (vec4 q r₁ r₂ r₃ s).2.2.2 < M →
      fv s - 1 ≤ g (vec4 q r₁ r₂ r₃ s))
    (X : ℚ) (hX : gsum g M + kk cap * tl4 α β γ δ M ≤ X) (hX1 : X < 1)
    (hfin : ρ₀ * ρ₁ * ρ₂ * ρ₃ * (∏ s ∈ C, rv s) * tailF cap / (1 - X) ≤ 2) : False := by
  classical
  set S := ord4 N q r₁ r₂ r₃
  have hS2 : ∀ s ∈ S, 2 ≤ s := fun s hs => le_trans (by norm_num) (c.ord_facts hs).2.2.1
  set Sg := S.filter (fun s => ¬ s < cap)
  have hSg : ∀ s ∈ Sg, s ∈ S ∧ cap ≤ s := fun s hs => by
    rw [Finset.mem_filter] at hs; exact ⟨hs.1, by omega⟩
  -- the large ordinary primes: `∏ fv ≤ 1/(1 - X)`
  have hPg := prod_bound4 Sg (vec4 q r₁ r₂ r₃) (c.vec_inj.mono (Finset.filter_subset _ S))
    cap M (by omega) hα0 hα1 hβ0 hβ1 hγ0 hγ1 hδ0 hδ1 ∅ (by simp)
    (fun s hs => by have := hS2 s (hSg s hs).1; omega)
    (fun s hs h => absurd (hSg s hs).2 (by omega))
    (fun s hs _ => c.weight (hSg s hs).1 hα0 hβ0 hγ0 hδ0 hα hβ hγ hδ)
    (fun s hs => (c.shape (hSg s hs).1).2)
    g hg0 (fun s hs h => hg s (hSg s hs).1 h) X hX hX1
  rw [Finset.prod_empty] at hPg
  have hTg := prod_rv_le cap hcap Sg fun s hs => (hSg s hs).2
  -- the small ordinary primes: `∏ rv ≤ ∏_C rv`
  have hl : ∏ s ∈ S.filter (fun s => s < cap), rv s ≤ ∏ s ∈ C, rv s := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro s hs; rw [Finset.mem_filter] at hs; exact hsmall s hs.1 hs.2
    · intro s hs
      exact zero_le_one.trans (one_le_rv (hS2 s (Finset.mem_of_mem_filter s hs)))
    · intro s hs _; exact one_le_rv (hC s hs)
  have hsplit := Finset.prod_filter_mul_prod_filter_not S (fun s => s < cap) (f := rv)
  have hl0 : 0 ≤ ∏ s ∈ S.filter (fun s => s < cap), rv s := Finset.prod_nonneg fun s hs =>
    zero_le_one.trans (one_le_rv (hS2 s (Finset.mem_of_mem_filter s hs)))
  have hC0 : 0 ≤ ∏ s ∈ C, rv s := Finset.prod_nonneg fun s hs => zero_le_one.trans (one_le_rv (hC s hs))
  have hg0' : 0 ≤ ∏ s ∈ Sg, rv s := Finset.prod_nonneg fun s hs =>
    zero_le_one.trans (one_le_rv (hS2 s (hSg s hs).1))
  have htf : 0 ≤ tailF cap := by
    have hc : (2 : ℚ) ≤ cap := by exact_mod_cast hcap
    have : 1 / (2 * ((cap : ℚ) - 1) ^ 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    unfold tailF
    apply div_nonneg zero_le_one
    linarith
  have h1X : 0 < 1 - X := by linarith
  have hfv0 : 0 ≤ ∏ s ∈ Sg, fv s := Finset.prod_nonneg fun s hs =>
    zero_le_one.trans (one_le_fv (by have := hS2 s (hSg s hs).1; omega))
  have hG : ∏ s ∈ Sg, rv s ≤ tailF cap * (1 / (1 - X)) :=
    hTg.trans (mul_le_mul_of_nonneg_left (by simpa using hPg) htf)
  have hP : ∏ s ∈ S, rv s ≤ (∏ s ∈ C, rv s) * (tailF cap * (1 / (1 - X))) := by
    rw [← hsplit]
    exact mul_le_mul hl hG hg0' hC0
  have hab := c.abund_lt
  have hP0 : 0 ≤ ∏ s ∈ S, rv s := by rw [← hsplit]; exact mul_nonneg hl0 hg0'
  obtain ⟨⟨-, h1, -⟩, ⟨-, h2, -⟩, ⟨-, h3, -⟩⟩ := c.r_prime
  have b0 := div_pred_pos c.hq.two_le
  have b1 := div_pred_pos (show 2 ≤ r₁ by omega)
  have b2 := div_pred_pos (show 2 ≤ r₂ by omega)
  have b3 := div_pred_pos (show 2 ≤ r₃ by omega)
  have hρ : (q : ℚ) / (q - 1) * ((r₁ : ℚ) / (r₁ - 1)) * ((r₂ : ℚ) / (r₂ - 1)) *
      ((r₃ : ℚ) / (r₃ - 1)) ≤ ρ₀ * ρ₁ * ρ₂ * ρ₃ :=
    mul_le_mul (mul_le_mul (mul_le_mul hρ₀ hρ₁ b1.le (b0.le.trans hρ₀)) hρ₂ b2.le
      (mul_nonneg (b0.le.trans hρ₀) (b1.le.trans hρ₁))) hρ₃ b3.le
      (mul_nonneg (mul_nonneg (b0.le.trans hρ₀) (b1.le.trans hρ₁)) (b2.le.trans hρ₂))
  have hρ0 : 0 ≤ ρ₀ * ρ₁ * ρ₂ * ρ₃ := by
    have := mul_pos (mul_pos (mul_pos b0 b1) b2) b3
    linarith
  have e := mul_le_mul hρ hP hP0 hρ0
  have hfin' : ρ₀ * ρ₁ * ρ₂ * ρ₃ * ((∏ s ∈ C, rv s) * (tailF cap * (1 / (1 - X)))) ≤ 2 := by
    calc _ = ρ₀ * ρ₁ * ρ₂ * ρ₃ * (∏ s ∈ C, rv s) * tailF cap / (1 - X) := by ring
      _ ≤ 2 := hfin
  linarith

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.fv_sub_one
#print axioms OddPerfect.ThreeFreeThree.fv_sub_le
#print axioms OddPerfect.ThreeFreeThree.one_le_rv
#print axioms OddPerfect.ThreeFreeThree.Ctx4.swap12
#print axioms OddPerfect.ThreeFreeThree.Ctx4.swap23
#print axioms OddPerfect.ThreeFreeThree.ctx4_of_not_three_dvd
#print axioms OddPerfect.ThreeFreeThree.mem_ord4
#print axioms OddPerfect.ThreeFreeThree.Ctx4.q_mod
#print axioms OddPerfect.ThreeFreeThree.Ctx4.five_le
#print axioms OddPerfect.ThreeFreeThree.Ctx4.r_prime
#print axioms OddPerfect.ThreeFreeThree.cyc_dvd_of_mod
#print axioms OddPerfect.ThreeFreeThree.Ctx4.ord_facts
#print axioms OddPerfect.ThreeFreeThree.Ctx4.not_mem_ord
#print axioms OddPerfect.ThreeFreeThree.Ctx4.tgt
#print axioms OddPerfect.ThreeFreeThree.Ctx4.shape
#print axioms OddPerfect.ThreeFreeThree.Ctx4.vec_zero
#print axioms OddPerfect.ThreeFreeThree.Ctx4.vec_inj
#print axioms OddPerfect.ThreeFreeThree.Ctx4.weight
#print axioms OddPerfect.ThreeFreeThree.Ctx4.fv_sub_le_min
#print axioms OddPerfect.ThreeFreeThree.Ctx4.abund_lt
#print axioms OddPerfect.ThreeFreeThree.Ctx4.close
