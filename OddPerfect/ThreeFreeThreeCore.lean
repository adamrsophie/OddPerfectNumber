import OddPerfect.ThreeFreeTwo

/-!
# The certificate independent core for three exceptional primes

This file is the certificate independent core of a proof in progress, built on the method of
`OddPerfect.ThreeFreeTwo`. The setting has four distinguished primes: the special prime `q`
of an odd perfect number `N` and three further primes `r₁, r₂, r₃`; every other prime factor
of `N` (an ordinary prime) has exponent exactly 2, and `3 ∤ N`. Nothing here depends on a
case analysis or certificate; the statement with three exceptional primes is not proved in
this file.

* `ctx4_of_not_three_dvd` reduces the degenerate configurations (some `rᵢ` equal to `q`, two
  `rᵢ` equal, or some `rᵢ` not dividing `N`) to `three_dvd_of_two_exceptions`, and packages
  the core configuration as `Ctx4`.
* For an ordinary `s`, every prime factor of `1 + s + s^2` is one of the four primes and is
  `1` modulo 3, so `1 + s + s^2 = q^a r₁^b r₂^c r₃^d` with `(a, b, c, d) = vec4 q r₁ r₂ r₃ s`
  not all even, and `vec4` is injective on the ordinary primes.
* With weights `α, β, γ, δ ∈ [0, 1)` satisfying `w² p ≥ 1` for each of the four primes `p`
  (or `p ≡ 2 (mod 3)`), the weight `wt4 α β γ δ (vec4 q r₁ r₂ r₃ s)` times `s + 1` is at
  least 1.
* `Ctx4.close`: the ordinary primes below `cap` lie in an explicit finite set `C`; for the
  larger ones, an arbitrary nonnegative bound `g` on `fv s - 1` is summed over the box
  `[0, M)^4` (`gsum`), and the weights give the geometric tail `kk cap * tl4` outside the box.
  If the resulting bound on the abundancy is at most 2, this contradicts `abundancy N = 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ThreeFreeThree

/-! ## Analytic part -/

/-- The abundancy `σ(s^2)/s^2` of an exact square. -/
def fv (s : ℕ) : ℚ := ((s : ℚ) ^ 2 + s + 1) / s ^ 2

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

/-! ## The arithmetic setting -/

/-- The core case: `q, r₁, r₂, r₃` are distinct prime factors of the odd perfect number `N`,
`q` is the special prime, every other prime factor has exponent 2, and `3 ∤ N`. -/
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
  hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → N.factorization p = 2
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
  hsq := fun p hp ha hb hc hd => c.hsq p hp ha hc hb hd
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
  hsq := fun p hp ha hb hc hd => c.hsq p hp ha hb hd hc
  h3 := c.h3

/-- Reduction of the degenerate cases to `three_dvd_of_two_exceptions`: if `3 ∤ N`, the four
primes form a core configuration. -/
theorem ctx4_of_not_three_dvd {N q r₁ r₂ r₃ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → N.factorization p = 2)
    (h3 : ¬ 3 ∣ N) : Ctx4 N q r₁ r₂ r₃ := by
  by_cases A : r₁ ∈ N.primeFactors ∧ r₁ ≠ q ∧ r₁ ≠ r₂ ∧ r₁ ≠ r₃
  · by_cases B : r₂ ∈ N.primeFactors ∧ r₂ ≠ q ∧ r₂ ≠ r₃
    · by_cases C : r₃ ∈ N.primeFactors ∧ r₃ ≠ q
      · exact ⟨h, hq, hodd, A.1, B.1, C.1, A.2.2.1, A.2.2.2, B.2.2, A.2.1, B.2.1, C.2, hsq, h3⟩
      · exfalso; apply h3
        refine three_dvd_of_two_exceptions h hq hodd (r₁ := r₁) (r₂ := r₂)
          fun p hp hpq h1 h2 => hsq p hp hpq h1 h2 ?_
        rintro rfl
        exact C ⟨hp, hpq⟩
    · exfalso; apply h3
      refine three_dvd_of_two_exceptions h hq hodd (r₁ := r₁) (r₂ := r₃)
        fun p hp hpq h1 h3' => hsq p hp hpq h1 ?_ h3'
      rintro rfl
      exact B ⟨hp, hpq, h3'⟩
  · exfalso; apply h3
    refine three_dvd_of_two_exceptions h hq hodd (r₁ := r₂) (r₂ := r₃)
      fun p hp hpq h2 h3' => hsq p hp hpq ?_ h2 h3'
    rintro rfl
    exact A ⟨hp, hpq, h2, h3'⟩

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

/-- An ordinary prime is prime, has exponent 2, is at least 5, and is `2` modulo 3. -/
theorem Ctx4.ord_facts {s : ℕ} (c : Ctx4 N q r₁ r₂ r₃) (hs : s ∈ ord4 N q r₁ r₂ r₃) :
    s.Prime ∧ N.factorization s = 2 ∧ 5 ≤ s ∧ s % 3 = 2 := by
  obtain ⟨hsN, h1, h2, h3, h4⟩ := mem_ord4.mp hs
  have hsp := Nat.prime_of_mem_primeFactors hsN
  have he := c.hsq s hsN h1 h2 h3 h4
  exact ⟨hsp, he, (c.five_le hsN).1, OPNThreeFree.source_mod_three c.opn.perfect c.h3 hsp he⟩

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
  obtain ⟨hsp, he, -⟩ := c.ord_facts hs
  rw [← sigma_sq hsp] at hdd
  obtain ⟨-, hdN, -, hd3, hd2⟩ :=
    OPNThreeFree.exact_square_transfer c.opn.perfect c.h3 hsp he hd hdd
  refine ⟨?_, hd3⟩
  by_contra hc
  simp only [not_or] at hc
  exact hd2 (c.hsq d (Nat.mem_primeFactors.mpr ⟨hd, hdN, c.opn.ne_zero⟩) hc.1 hc.2.1 hc.2.2.1
    hc.2.2.2)

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

/-- The abundancy of `N` is 2, so the bound `p/(p - 1)` for the four primes and the exact
value `fv s` for the ordinary primes give a strict inequality. -/
theorem Ctx4.abund_lt (c : Ctx4 N q r₁ r₂ r₃) :
    2 < (q : ℚ) / (q - 1) * ((r₁ : ℚ) / (r₁ - 1)) * ((r₂ : ℚ) / (r₂ - 1)) *
      ((r₃ : ℚ) / (r₃ - 1)) * ∏ s ∈ ord4 N q r₁ r₂ r₃, fv s := by
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
  have heq : ∏ x ∈ ord4 N q r₁ r₂ r₃, abundancy (x ^ N.factorization x) =
      ∏ x ∈ ord4 N q r₁ r₂ r₃, fv x := by
    refine Finset.prod_congr rfl fun x hx => ?_
    obtain ⟨hxp, hxe, -⟩ := c.ord_facts hx
    have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hxp.ne_zero
    rw [hxe, abundancy_prime_pow hxp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, fv]
    field_simp
    ring
  change abundancy _ * (abundancy _ * (abundancy _ * (abundancy _ *
    ∏ x ∈ ord4 N q r₁ r₂ r₃, _))) = 2 at hab
  rw [heq] at hab
  have hP : 0 < ∏ s ∈ ord4 N q r₁ r₂ r₃, fv s := Finset.prod_pos fun s hs =>
    lt_of_lt_of_le zero_lt_one (one_le_fv (le_trans (by norm_num) (c.ord_facts hs).2.2.1))
  have hgq := abundancy_prime_pow_lt c.hq (N.factorization q)
  have hg1 := abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors c.hr₁) (N.factorization r₁)
  have hg2 := abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors c.hr₂) (N.factorization r₂)
  have hg3 := abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors c.hr₃) (N.factorization r₃)
  have h0q := abundancy_nonneg (q ^ N.factorization q)
  have h01 := abundancy_nonneg (r₁ ^ N.factorization r₁)
  have h02 := abundancy_nonneg (r₂ ^ N.factorization r₂)
  have h03 := abundancy_nonneg (r₃ ^ N.factorization r₃)
  have e3 := mul_lt_mul_of_pos_right hg3 hP
  have e2 := mul_lt_mul'' hg2 e3 h02 (mul_nonneg h03 hP.le)
  have e1 := mul_lt_mul'' hg1 e2 h01 (mul_nonneg h02 (mul_nonneg h03 hP.le))
  have e0 := mul_lt_mul'' hgq e1 h0q (mul_nonneg h01 (mul_nonneg h02 (mul_nonneg h03 hP.le)))
  rw [hab] at e0
  calc (2 : ℚ) < _ := e0
    _ = _ := by ring

private theorem div_pred_pos {p : ℕ} (hp : 2 ≤ p) : 0 < (p : ℚ) / (p - 1) := by
  have : (2 : ℚ) ≤ p := by exact_mod_cast hp
  apply div_pos <;> linarith

/-- The closing theorem: the abundancy bound from the small ordinary primes in `C`, the box
bound `g`, and the geometric tail is at most 2, which is impossible. -/
theorem Ctx4.close (c : Ctx4 N q r₁ r₂ r₃) (cap M : ℕ) (hcap : 1 ≤ cap)
    {α β γ δ ρ₀ ρ₁ ρ₂ ρ₃ : ℚ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hα : 1 ≤ α ^ 2 * q ∨ q % 3 = 2) (hβ : 1 ≤ β ^ 2 * r₁ ∨ r₁ % 3 = 2)
    (hγ : 1 ≤ γ ^ 2 * r₂ ∨ r₂ % 3 = 2) (hδ : 1 ≤ δ ^ 2 * r₃ ∨ r₃ % 3 = 2)
    (hρ₀ : (q : ℚ) / (q - 1) ≤ ρ₀) (hρ₁ : (r₁ : ℚ) / (r₁ - 1) ≤ ρ₁)
    (hρ₂ : (r₂ : ℚ) / (r₂ - 1) ≤ ρ₂) (hρ₃ : (r₃ : ℚ) / (r₃ - 1) ≤ ρ₃)
    (C : Finset ℕ) (hC : ∀ x ∈ C, 1 ≤ x)
    (hsmall : ∀ s ∈ ord4 N q r₁ r₂ r₃, s < cap → s ∈ C)
    (g : ℕ × ℕ × ℕ × ℕ → ℚ) (hg0 : ∀ v, 0 ≤ g v)
    (hg : ∀ s ∈ ord4 N q r₁ r₂ r₃, cap ≤ s →
      (vec4 q r₁ r₂ r₃ s).1 < M → (vec4 q r₁ r₂ r₃ s).2.1 < M →
      (vec4 q r₁ r₂ r₃ s).2.2.1 < M → (vec4 q r₁ r₂ r₃ s).2.2.2 < M →
      fv s - 1 ≤ g (vec4 q r₁ r₂ r₃ s))
    (X : ℚ) (hX : gsum g M + kk cap * tl4 α β γ δ M ≤ X) (hX1 : X < 1)
    (hfin : ρ₀ * ρ₁ * ρ₂ * ρ₃ * (∏ s ∈ C, fv s) / (1 - X) ≤ 2) : False := by
  have hP := prod_bound4 (ord4 N q r₁ r₂ r₃) (vec4 q r₁ r₂ r₃) c.vec_inj cap M hcap
    hα0 hα1 hβ0 hβ1 hγ0 hγ1 hδ0 hδ1 C hC
    (fun s hs => le_trans (by norm_num) (c.ord_facts hs).2.2.1) hsmall
    (fun s hs _ => c.weight hs hα0 hβ0 hγ0 hδ0 hα hβ hγ hδ) (fun s hs => (c.shape hs).2)
    g hg0 hg X hX hX1
  have hab := c.abund_lt
  have hP0 : 0 ≤ ∏ s ∈ ord4 N q r₁ r₂ r₃, fv s := Finset.prod_nonneg fun s hs =>
    le_trans zero_le_one (one_le_fv (le_trans (by norm_num) (c.ord_facts hs).2.2.1))
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
  rw [mul_div_assoc] at hfin
  linarith

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.fv_sub_one
#print axioms OddPerfect.ThreeFreeThree.fv_sub_le
#print axioms OddPerfect.ThreeFreeThree.Ctx4.swap12
#print axioms OddPerfect.ThreeFreeThree.Ctx4.swap23
#print axioms OddPerfect.ThreeFreeThree.ctx4_of_not_three_dvd
#print axioms OddPerfect.ThreeFreeThree.mem_ord4
#print axioms OddPerfect.ThreeFreeThree.Ctx4.q_mod
#print axioms OddPerfect.ThreeFreeThree.Ctx4.five_le
#print axioms OddPerfect.ThreeFreeThree.Ctx4.r_prime
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
