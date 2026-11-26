import OddPerfect.Abundancy
import OddPerfect.Euler
import OddPerfect.Seed.ThreeFree
import OddPerfect.Seed.Example
import OddPerfect.ThreeFreeException

/-!
# Odd perfect numbers with two exceptional primes are divisible by 3

Let `N` be an odd perfect number with special prime `q`, and suppose every prime factor of
`N` except `q`, `r₁` and `r₂` has exponent exactly 2. We show `3 ∣ N`. This extends
`three_dvd_of_one_exception` (one exception, the restrained case of Ochem and Zelinsky,
arXiv:2607.19746) to two exceptions.

Assume `3 ∤ N`. The degenerate cases (`rᵢ = q`, `r₁ = r₂`, or `rᵢ ∤ N`) reduce to the one
exception theorem, so let `q, r₁, r₂` be distinct prime factors of `N`. Call the other
prime factors ordinary and let `S` be their set.

* `q ≡ 1 (mod 12)`, `rᵢ ≥ 5`, and for `s ∈ S` every prime factor `d` of
  `σ(s^2) = 1 + s + s^2` is one of `q, r₁, r₂` and is `1` modulo 3
  (`OPNThreeFree.exact_square_transfer`). So `σ(s^2) = q^a r₁^b r₂^c`, with `a, b, c` not
  all even, the map `s ↦ (a, b, c)` is injective, and `b = 0` when `r₁ ≡ 2 (mod 3)`.
* Ordinary primes `s ≥ 300`: with `α² q ≥ 1`, `β² r₁ ≥ 1`, `γ² r₂ ≥ 1` (or `β = 0` for a
  non-target `r₁`), the weight `w = α^a β^b γ^c` satisfies `w (s + 1) ≥ 1`, so
  `σ(s^2)/s^2 - 1 ≤ k min(1/300, w)` with `k = (301/300)^2`. Summing over the distinct
  vectors, a box `[0,5)^3` is evaluated exactly and the rest is a geometric tail, and
  `∏ (1 + x_i) ≤ 1 / (1 - ∑ x_i)`.
* Ordinary primes `s < 300`: a table lists, for each prime `s ≡ 2 (mod 3)` below 300, the
  prime factors of `1 + s + s^2`; each must lie in `{q, r₁, r₂}`. Given the class of
  `r₁, r₂`, `omega` confines the small ordinary primes to an explicit finite set `C`.
* The classes of an exceptional prime are `5`, `7`, `13`, `19`, `31`, `37`, `43`, any prime
  `≡ 2 (mod 3)` at least 11, and any prime `≡ 1 (mod 3)` at least 61. For each unordered
  pair of classes (with the pair `(7, 31)` split by `q ∈ {409, 3541}` and the pair
  `(7, ≥ 61)` split by `r₂ = 307`) the bound
  `13/12 · r₁/(r₁-1) · r₂/(r₂-1) · ∏_C σ(s^2)/s^2 / (1 - k (box + tail))` is below 2,
  which contradicts the abundancy 2 of `N`. The largest of these 41 bounds is about 1.975.

Everything is elementary, with exact rational arithmetic and no computer search beyond
`norm_num` and `omega`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ThreeFreeTwo

/-! ## Analytic part -/

/-- The abundancy `σ(s^2)/s^2` of an exact square. -/
private def fv (s : ℕ) : ℚ := ((s : ℚ) ^ 2 + s + 1) / s ^ 2

/-- The weight of an exponent vector. -/
private def wt (α β γ : ℚ) (t : ℕ × ℕ × ℕ) : ℚ := α ^ t.1 * β ^ t.2.1 * γ ^ t.2.2

/-- The box part of the bound. -/
private def bsum (α β γ : ℚ) (cap M : ℕ) : ℚ :=
  ∑ t ∈ (Finset.range M ×ˢ (Finset.range M ×ˢ Finset.range M)).filter
      (fun t => ¬ (Even t.1 ∧ Even t.2.1 ∧ Even t.2.2)),
    min (1 / (cap : ℚ)) (wt α β γ t)

/-- The geometric tail outside the box. -/
private def tl (α β γ : ℚ) (M : ℕ) : ℚ := (α ^ M + β ^ M + γ ^ M) / ((1 - α) * (1 - β) * (1 - γ))

/-- The constant `((cap + 1)/cap)^2`. -/
private def kk (cap : ℕ) : ℚ := (((cap : ℚ) + 1) / cap) ^ 2

private theorem one_le_fv {s : ℕ} (hs : 1 ≤ s) : 1 ≤ fv s := by
  have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
  unfold fv
  rw [le_div_iff₀ (by positivity)]
  nlinarith

private theorem wt_nonneg {α β γ : ℚ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (t : ℕ × ℕ × ℕ) :
    0 ≤ wt α β γ t := by
  unfold wt; positivity

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

private theorem cube_sum (α β γ : ℚ) (A B C : Finset ℕ) :
    ∑ t ∈ A ×ˢ (B ×ˢ C), wt α β γ t =
      (∑ a ∈ A, α ^ a) * (∑ b ∈ B, β ^ b) * (∑ c ∈ C, γ ^ c) := by
  rw [mul_assoc, Finset.sum_mul, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_product, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [wt]; ring

private theorem geom_le {x : ℚ} (h0 : 0 ≤ x) (h1 : x < 1) (m n : ℕ) :
    ∑ i ∈ Finset.Ico m n, x ^ i ≤ x ^ m / (1 - x) :=
  geom_sum_Ico_le_of_lt_one h0 h1

private theorem tail3 (T : Finset (ℕ × ℕ × ℕ)) (M : ℕ) {α β γ : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hT : ∀ t ∈ T, M ≤ t.1 ∨ M ≤ t.2.1 ∨ M ≤ t.2.2) :
    ∑ t ∈ T, wt α β γ t ≤ tl α β γ M := by
  set K := T.sup (fun t => t.1 + t.2.1 + t.2.2) + 1
  have hK : ∀ t ∈ T, t.1 < K ∧ t.2.1 < K ∧ t.2.2 < K := fun t ht => by
    have := Finset.le_sup (f := fun t => t.1 + t.2.1 + t.2.2) ht
    omega
  have hw := wt_nonneg hα0 hβ0 hγ0
  have h1a : 0 < 1 - α := by linarith
  have h1b : 0 < 1 - β := by linarith
  have h1c : 0 < 1 - γ := by linarith
  have gα := geom_le hα0 hα1 M K
  have gβ := geom_le hβ0 hβ1 M K
  have gγ := geom_le hγ0 hγ1 M K
  have fα := geom_le hα0 hα1 0 K
  have fβ := geom_le hβ0 hβ1 0 K
  have fγ := geom_le hγ0 hγ1 0 K
  simp only [pow_zero] at fα fβ fγ
  have sα : 0 ≤ ∑ i ∈ Finset.Ico M K, α ^ i := Finset.sum_nonneg fun _ _ => by positivity
  have sβ : 0 ≤ ∑ i ∈ Finset.Ico M K, β ^ i := Finset.sum_nonneg fun _ _ => by positivity
  have sγ : 0 ≤ ∑ i ∈ Finset.Ico M K, γ ^ i := Finset.sum_nonneg fun _ _ => by positivity
  have sα' : 0 ≤ ∑ i ∈ Finset.Ico 0 K, α ^ i := Finset.sum_nonneg fun _ _ => by positivity
  have sβ' : 0 ≤ ∑ i ∈ Finset.Ico 0 K, β ^ i := Finset.sum_nonneg fun _ _ => by positivity
  have sγ' : 0 ≤ ∑ i ∈ Finset.Ico 0 K, γ ^ i := Finset.sum_nonneg fun _ _ => by positivity
  -- each filter sum is bounded by a cube sum
  have hA : ∑ t ∈ T.filter (fun t => M ≤ t.1), wt α β γ t ≤
      α ^ M / (1 - α) * (1 / (1 - β)) * (1 / (1 - γ)) := by
    calc _ ≤ ∑ t ∈ Finset.Ico M K ×ˢ (Finset.Ico 0 K ×ˢ Finset.Ico 0 K), wt α β γ t := by
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => hw t)
          intro t ht
          rw [Finset.mem_filter] at ht
          have := hK t ht.1
          simp only [Finset.mem_product, Finset.mem_Ico]
          omega
      _ = _ := cube_sum _ _ _ _ _ _
      _ ≤ _ := by gcongr
  have hB : ∑ t ∈ T.filter (fun t => M ≤ t.2.1), wt α β γ t ≤
      1 / (1 - α) * (β ^ M / (1 - β)) * (1 / (1 - γ)) := by
    calc _ ≤ ∑ t ∈ Finset.Ico 0 K ×ˢ (Finset.Ico M K ×ˢ Finset.Ico 0 K), wt α β γ t := by
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => hw t)
          intro t ht
          rw [Finset.mem_filter] at ht
          have := hK t ht.1
          simp only [Finset.mem_product, Finset.mem_Ico]
          omega
      _ = _ := cube_sum _ _ _ _ _ _
      _ ≤ _ := by gcongr
  have hC : ∑ t ∈ T.filter (fun t => M ≤ t.2.2), wt α β γ t ≤
      1 / (1 - α) * (1 / (1 - β)) * (γ ^ M / (1 - γ)) := by
    calc _ ≤ ∑ t ∈ Finset.Ico 0 K ×ˢ (Finset.Ico 0 K ×ˢ Finset.Ico M K), wt α β γ t := by
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => hw t)
          intro t ht
          rw [Finset.mem_filter] at ht
          have := hK t ht.1
          simp only [Finset.mem_product, Finset.mem_Ico]
          omega
      _ = _ := cube_sum _ _ _ _ _ _
      _ ≤ _ := by gcongr
  have hsplit : ∑ t ∈ T, wt α β γ t ≤
      ∑ t ∈ T.filter (fun t => M ≤ t.1), wt α β γ t +
      ∑ t ∈ T.filter (fun t => M ≤ t.2.1), wt α β γ t +
      ∑ t ∈ T.filter (fun t => M ≤ t.2.2), wt α β γ t := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    have h0 := hw t
    rcases hT t ht with h | h | h
    · have : 0 ≤ (if M ≤ t.2.1 then wt α β γ t else 0) := by split_ifs <;> linarith
      have : 0 ≤ (if M ≤ t.2.2 then wt α β γ t else 0) := by split_ifs <;> linarith
      rw [if_pos h]; linarith
    · have : 0 ≤ (if M ≤ t.1 then wt α β γ t else 0) := by split_ifs <;> linarith
      have : 0 ≤ (if M ≤ t.2.2 then wt α β γ t else 0) := by split_ifs <;> linarith
      rw [if_pos h]; linarith
    · have : 0 ≤ (if M ≤ t.1 then wt α β γ t else 0) := by split_ifs <;> linarith
      have : 0 ≤ (if M ≤ t.2.1 then wt α β γ t else 0) := by split_ifs <;> linarith
      rw [if_pos h]; linarith
  have heq : α ^ M / (1 - α) * (1 / (1 - β)) * (1 / (1 - γ)) +
      1 / (1 - α) * (β ^ M / (1 - β)) * (1 / (1 - γ)) +
      1 / (1 - α) * (1 / (1 - β)) * (γ ^ M / (1 - γ)) = tl α β γ M := by
    unfold tl; field_simp
  linarith


private theorem fv_sub_le {cap s : ℕ} (hcap : 1 ≤ cap) (hs : cap ≤ s) :
    fv s - 1 ≤ kk cap / ((s : ℚ) + 1) := by
  have hc : (1 : ℚ) ≤ cap := by exact_mod_cast hcap
  have hcs : (cap : ℚ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℚ) < s := by linarith
  have e1 : fv s - 1 = ((s : ℚ) + 1) / s ^ 2 := by unfold fv; field_simp; ring
  have e2 : ((s : ℚ) + 1) * cap ≤ (cap + 1) * s := by nlinarith
  have e3 : (((s : ℚ) + 1) * cap) ^ 2 ≤ ((cap + 1) * s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) e2 2
  rw [e1, kk, div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

private theorem prod_bound (S : Finset ℕ) (π : ℕ → ℕ × ℕ × ℕ) (hinj : Set.InjOn π S) (cap M : ℕ)
    (hcap : 1 ≤ cap) {α β γ : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (C : Finset ℕ) (hC : ∀ x ∈ C, 1 ≤ x)
    (hS1 : ∀ s ∈ S, 1 ≤ s) (hsmall : ∀ s ∈ S, s < cap → s ∈ C)
    (hlarge : ∀ s ∈ S, cap ≤ s → 1 ≤ wt α β γ (π s) * ((s : ℚ) + 1))
    (hev : ∀ s ∈ S, ¬ (Even (π s).1 ∧ Even (π s).2.1 ∧ Even (π s).2.2))
    (hlt : kk cap * (bsum α β γ cap M + tl α β γ M) < 1) :
    ∏ s ∈ S, fv s ≤ (∏ s ∈ C, fv s) / (1 - kk cap * (bsum α β γ cap M + tl α β γ M)) := by
  classical
  set K := kk cap * (bsum α β γ cap M + tl α β γ M) with hK
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun s => s < cap)]
  set Sl := S.filter (fun s => s < cap)
  set Sg := S.filter (fun s => ¬ s < cap)
  have hfv0 : ∀ s ∈ S, 0 ≤ fv s := fun s hs => le_trans zero_le_one (one_le_fv (hS1 s hs))
  have h1 : ∏ s ∈ Sl, fv s ≤ ∏ s ∈ C, fv s := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro s hs; rw [Finset.mem_filter] at hs; exact hsmall s hs.1 hs.2
    · intro s hs; exact hfv0 s (Finset.mem_of_mem_filter s hs)
    · intro s hs _; exact one_le_fv (hC s hs)
  have hw := wt_nonneg hα0 hβ0 hγ0
  have hkk : 0 ≤ kk cap := by unfold kk; positivity
  set m : ℕ × ℕ × ℕ → ℚ := fun t => min (1 / (cap : ℚ)) (wt α β γ t) with hm
  have hm0 : ∀ t, 0 ≤ m t := fun t => le_min (by positivity) (hw t)
  have hx : ∀ s ∈ Sg, fv s - 1 ≤ kk cap * m (π s) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    have hcs : cap ≤ s := by omega
    have hcs' : (cap : ℚ) ≤ s := by exact_mod_cast hcs
    have hc' : (1 : ℚ) ≤ cap := by exact_mod_cast hcap
    have hwl := hlarge s hs.1 hcs
    refine le_trans (fv_sub_le hcap hcs) ?_
    rw [hm, mul_min_of_nonneg _ _ hkk]
    refine le_min ?_ ?_
    · rw [mul_one_div]
      exact div_le_div_of_nonneg_left hkk (by positivity) (by linarith)
    · rw [div_le_iff₀ (by positivity)]
      nlinarith
  -- the sum over the image
  have hI : ∑ t ∈ Sg.image π, m t ≤ bsum α β γ cap M + tl α β γ M := by
    rw [← Finset.sum_filter_add_sum_filter_not _
      (fun t => t.1 < M ∧ t.2.1 < M ∧ t.2.2 < M)]
    have hb : ∑ t ∈ (Sg.image π).filter (fun t => t.1 < M ∧ t.2.1 < M ∧ t.2.2 < M), m t ≤
        bsum α β γ cap M := by
      unfold bsum
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => hm0 t)
      intro t ht
      rw [Finset.mem_filter, Finset.mem_image] at ht
      obtain ⟨⟨s, hs, rfl⟩, hbox⟩ := ht
      rw [Finset.mem_filter]
      refine ⟨?_, hev s (Finset.mem_of_mem_filter s hs)⟩
      simp only [Finset.mem_product, Finset.mem_range]
      exact hbox
    have ht : ∑ t ∈ (Sg.image π).filter (fun t => ¬ (t.1 < M ∧ t.2.1 < M ∧ t.2.2 < M)), m t ≤
        tl α β γ M := by
      refine le_trans (Finset.sum_le_sum fun t _ => min_le_right _ _) ?_
      apply tail3 _ M hα0 hα1 hβ0 hβ1 hγ0 hγ1
      intro t ht
      have := (Finset.mem_filter.mp ht).2
      omega
    linarith
  have hsum : ∑ s ∈ Sg, (fv s - 1) ≤ K := by
    calc ∑ s ∈ Sg, (fv s - 1) ≤ ∑ s ∈ Sg, kk cap * m (π s) := Finset.sum_le_sum hx
      _ = kk cap * ∑ t ∈ Sg.image π, m t := by
          rw [← Finset.mul_sum, Finset.sum_image fun x hx y hy =>
            hinj (Finset.mem_of_mem_filter x hx) (Finset.mem_of_mem_filter y hy)]
      _ ≤ K := mul_le_mul_of_nonneg_left hI hkk
  have hx0 : ∀ s ∈ Sg, 0 ≤ fv s - 1 := fun s hs =>
    sub_nonneg.mpr (one_le_fv (hS1 s (Finset.mem_of_mem_filter s hs)))
  have hG := prod_one_add_le Sg (fun s => fv s - 1) hx0
  simp only [add_sub_cancel] at hG
  have hP0 : 0 ≤ ∏ s ∈ Sg, fv s :=
    Finset.prod_nonneg fun s hs => hfv0 s (Finset.mem_of_mem_filter s hs)
  have h2 : ∏ s ∈ Sg, fv s ≤ 1 / (1 - K) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hC0 : 0 ≤ ∏ s ∈ C, fv s :=
    Finset.prod_nonneg fun s hs => le_trans zero_le_one (one_le_fv (hC s hs))
  have hP1 : 0 ≤ ∏ s ∈ Sl, fv s :=
    Finset.prod_nonneg fun s hs => hfv0 s (Finset.mem_of_mem_filter s hs)
  calc _ ≤ (∏ s ∈ C, fv s) * (1 / (1 - K)) := mul_le_mul h1 h2 hP0 hC0
    _ = _ := by ring

/-! ## The arithmetic setting -/

/-- The core case: `q, r₁, r₂` are distinct prime factors, `q` is the special prime, every
other prime factor has exponent 2, and `3 ∤ N`. -/
private structure Ctx (N q r₁ r₂ : ℕ) : Prop where
  opn : OddPerfect N
  hq : q.Prime
  hodd : Odd (N.factorization q)
  hr₁ : r₁ ∈ N.primeFactors
  hr₂ : r₂ ∈ N.primeFactors
  h12 : r₁ ≠ r₂
  h1q : r₁ ≠ q
  h2q : r₂ ≠ q
  hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2
  h3 : ¬ 3 ∣ N

private theorem Ctx.swap {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) : Ctx N q r₂ r₁ where
  opn := c.opn
  hq := c.hq
  hodd := c.hodd
  hr₁ := c.hr₂
  hr₂ := c.hr₁
  h12 := c.h12.symm
  h1q := c.h2q
  h2q := c.h1q
  hsq := fun p hp ha hb hc => c.hsq p hp ha hc hb
  h3 := c.h3

/-- The ordinary prime factors. -/
private def ord (N q r₁ r₂ : ℕ) : Finset ℕ := ((N.primeFactors.erase q).erase r₁).erase r₂

private theorem mem_ord {N q r₁ r₂ s : ℕ} :
    s ∈ ord N q r₁ r₂ ↔ s ∈ N.primeFactors ∧ s ≠ q ∧ s ≠ r₁ ∧ s ≠ r₂ := by
  simp only [ord, Finset.mem_erase]
  tauto

private theorem sigma_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

private theorem Ctx.q_mod {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) : q % 12 = 1 := by
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

private theorem Ctx.five_le {N q r₁ r₂ p : ℕ} (c : Ctx N q r₁ r₂) (hp : p ∈ N.primeFactors) :
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

private theorem Ctx.ord_facts {N q r₁ r₂ s : ℕ} (c : Ctx N q r₁ r₂) (hs : s ∈ ord N q r₁ r₂) :
    s.Prime ∧ N.factorization s = 2 ∧ 5 ≤ s := by
  obtain ⟨hsN, h1, h2, h3⟩ := mem_ord.mp hs
  exact ⟨Nat.prime_of_mem_primeFactors hsN, c.hsq s hsN h1 h2 h3, (c.five_le hsN).1⟩

/-- Every prime factor of `1 + s + s^2`, for an ordinary `s`, is `q`, `r₁` or `r₂`, and is
`1` modulo 3. -/
private theorem Ctx.tgt {N q r₁ r₂ s d : ℕ} (c : Ctx N q r₁ r₂) (hs : s ∈ ord N q r₁ r₂)
    (hd : d.Prime) (hdd : d ∣ 1 + s + s ^ 2) : (d = q ∨ d = r₁ ∨ d = r₂) ∧ d % 3 = 1 := by
  obtain ⟨hsp, he, -⟩ := c.ord_facts hs
  rw [← sigma_sq hsp] at hdd
  obtain ⟨-, hdN, -, hd3, hd2⟩ :=
    OPNThreeFree.exact_square_transfer c.opn.perfect c.h3 hsp he hd hdd
  refine ⟨?_, hd3⟩
  by_contra hc
  simp only [not_or] at hc
  exact hd2 (c.hsq d (Nat.mem_primeFactors.mpr ⟨hd, hdN, c.opn.ne_zero⟩) hc.1 hc.2.1 hc.2.2)

/-- The exponent vector of an ordinary prime. -/
private def vec (q r₁ r₂ s : ℕ) : ℕ × ℕ × ℕ :=
  ((1 + s + s ^ 2).factorization q, (1 + s + s ^ 2).factorization r₁,
    (1 + s + s ^ 2).factorization r₂)

private theorem ne_sq {p m : ℕ} (hp : 0 < p) : 1 + p + p ^ 2 ≠ m ^ 2 := by
  intro h
  have h1 : p ^ 2 < m ^ 2 := by rw [← h]; omega
  have h2 : m ^ 2 < (p + 1) ^ 2 := by rw [← h]; nlinarith
  have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h1
  have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
  omega

private theorem Ctx.shape {N q r₁ r₂ s : ℕ} (c : Ctx N q r₁ r₂) (hs : s ∈ ord N q r₁ r₂) :
    1 + s + s ^ 2 = q ^ (vec q r₁ r₂ s).1 * r₁ ^ (vec q r₁ r₂ s).2.1 * r₂ ^ (vec q r₁ r₂ s).2.2 ∧
    ¬ (Even (vec q r₁ r₂ s).1 ∧ Even (vec q r₁ r₂ s).2.1 ∧ Even (vec q r₁ r₂ s).2.2) := by
  have hs0 : 0 < s := (c.ord_facts hs).1.pos
  have hne : 1 + s + s ^ 2 ≠ 0 := by positivity
  have heq : 1 + s + s ^ 2 =
      q ^ (vec q r₁ r₂ s).1 * r₁ ^ (vec q r₁ r₂ s).2.1 * r₂ ^ (vec q r₁ r₂ s).2.2 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hne]
    rw [Finsupp.prod_of_support_subset _ (s := {q, r₁, r₂}) _ _ (fun _ _ => pow_zero _),
      Finset.prod_insert (by simp [c.h1q.symm, c.h2q.symm]),
      Finset.prod_pair c.h12, mul_assoc]
    · rfl
    intro t ht
    rw [Nat.support_factorization] at ht
    have := (c.tgt hs (Nat.prime_of_mem_primeFactors ht) (Nat.dvd_of_mem_primeFactors ht)).1
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  refine ⟨heq, ?_⟩
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩⟩
  apply ne_sq hs0 (m := q ^ i * r₁ ^ j * r₂ ^ k)
  rw [heq, hi, hj, hk]
  ring

private theorem Ctx.vec_inj {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) :
    Set.InjOn (vec q r₁ r₂) (ord N q r₁ r₂) := by
  intro x hx y hy hxy
  have ex := (c.shape hx).1
  have ey := (c.shape hy).1
  have hF : 1 + x + x ^ 2 = 1 + y + y ^ 2 := by rw [ex, ey, hxy]
  rcases lt_trichotomy x y with hlt | heq | hgt
  · nlinarith
  · exact heq
  · nlinarith

/-- A non-target exceptional prime never divides `1 + s + s^2`. -/
private theorem Ctx.vec_zero {N q r₁ r₂ s : ℕ} (c : Ctx N q r₁ r₂) (hs : s ∈ ord N q r₁ r₂)
    {r : ℕ} (hr : r ∈ N.primeFactors) (h2 : r % 3 = 2) : (1 + s + s ^ 2).factorization r = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  have := (c.tgt hs (Nat.prime_of_mem_primeFactors hr) hd).2
  omega

private theorem pow_ge_one_of {x : ℚ} {r : ℕ} (e : ℕ) (h : 1 ≤ x ^ 2 * r ∨ e = 0) : 1 ≤ (x ^ 2 * r) ^ e := by
  rcases h with h | h
  · exact one_le_pow₀ h
  · simp [h]

private theorem wt_sq (x β γ q r₁ r₂ : ℚ) (a b c : ℕ) :
    (x ^ a * β ^ b * γ ^ c) ^ 2 * (q ^ a * r₁ ^ b * r₂ ^ c) =
      (x ^ 2 * q) ^ a * (β ^ 2 * r₁) ^ b * (γ ^ 2 * r₂) ^ c := by ring

/-- The weight inequality for a large ordinary prime. -/
private theorem Ctx.weight {N q r₁ r₂ s : ℕ} (c : Ctx N q r₁ r₂) (hs : s ∈ ord N q r₁ r₂)
    {β γ : ℚ} (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ)
    (hβ : 1 ≤ β ^ 2 * r₁ ∨ r₁ % 3 = 2) (hγ : 1 ≤ γ ^ 2 * r₂ ∨ r₂ % 3 = 2) :
    1 ≤ wt (5 / 18) β γ (vec q r₁ r₂ s) * ((s : ℚ) + 1) := by
  have hq13 : (13 : ℚ) ≤ q := by
    have := c.q_mod; have := c.hq.two_le
    exact_mod_cast (show 13 ≤ q by omega)
  set v := vec q r₁ r₂ s
  have hA : 1 ≤ ((5 / 18 : ℚ) ^ 2 * q) ^ v.1 := one_le_pow₀ (by nlinarith)
  have hB : 1 ≤ (β ^ 2 * r₁) ^ v.2.1 := pow_ge_one_of _ (by
    rcases hβ with h | h
    · exact Or.inl h
    · exact Or.inr (c.vec_zero hs c.hr₁ h))
  have hC : 1 ≤ (γ ^ 2 * r₂) ^ v.2.2 := pow_ge_one_of _ (by
    rcases hγ with h | h
    · exact Or.inl h
    · exact Or.inr (c.vec_zero hs c.hr₂ h))
  have hsh := (c.shape hs).1
  have hlt : ((q ^ v.1 * r₁ ^ v.2.1 * r₂ ^ v.2.2 : ℕ) : ℚ) < ((s : ℚ) + 1) ^ 2 := by
    have : q ^ v.1 * r₁ ^ v.2.1 * r₂ ^ v.2.2 < (s + 1) ^ 2 := by
      rw [← hsh]; nlinarith [(c.ord_facts hs).2.2]
    exact_mod_cast this
  set w := wt (5 / 18) β γ v
  have hw0 : 0 ≤ w := wt_nonneg (by norm_num) hβ0 hγ0 v
  have hwV : 1 ≤ w ^ 2 * ((q ^ v.1 * r₁ ^ v.2.1 * r₂ ^ v.2.2 : ℕ) : ℚ) := by
    have : w ^ 2 * ((q ^ v.1 * r₁ ^ v.2.1 * r₂ ^ v.2.2 : ℕ) : ℚ) =
        ((5 / 18 : ℚ) ^ 2 * q) ^ v.1 * (β ^ 2 * r₁) ^ v.2.1 * (γ ^ 2 * r₂) ^ v.2.2 := by
      simp only [w, wt]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow]
      exact wt_sq _ _ _ _ _ _ _ _ _
    rw [this]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hB) hC
  have h2 : 1 ≤ (w * ((s : ℚ) + 1)) ^ 2 := by
    rw [mul_pow]
    have hV0 : (0 : ℚ) ≤ ((q ^ v.1 * r₁ ^ v.2.1 * r₂ ^ v.2.2 : ℕ) : ℚ) := by positivity
    nlinarith [sq_nonneg w]
  nlinarith [mul_nonneg hw0 (by positivity : (0 : ℚ) ≤ (s : ℚ) + 1)]

private theorem div_pred_le {p m : ℕ} (hm : 2 ≤ m) (hp : m ≤ p) :
    (p : ℚ) / (p - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hp' : (m : ℚ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy; positivity

/-- The closing inequality: a leaf of the case analysis. -/
private theorem Ctx.close {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (C : Finset ℕ) {β γ ρ₁ ρ₂ B : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hβ : 1 ≤ β ^ 2 * r₁ ∨ r₁ % 3 = 2) (hγ : 1 ≤ γ ^ 2 * r₂ ∨ r₂ % 3 = 2)
    (hρ₁ : (r₁ : ℚ) / (r₁ - 1) ≤ ρ₁) (hρ₂ : (r₂ : ℚ) / (r₂ - 1) ≤ ρ₂)
    (hC : ∀ x ∈ C, 1 ≤ x)
    (hsmall : ∀ s ∈ ord N q r₁ r₂, s < 300 → s ∈ C)
    (hB : bsum (5 / 18) β γ 300 5 ≤ B)
    (hk : kk 300 * (B + tl (5 / 18) β γ 5) < 1)
    (hnum : 13 / 12 * ρ₁ * ρ₂ * ((∏ s ∈ C, fv s) / (1 - kk 300 * (B + tl (5 / 18) β γ 5))) < 2) :
    False := by
  have hN := c.opn
  have hN0 := hN.ne_zero
  have hqT : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨c.hq, Nat.dvd_of_factorization_pos c.hodd.pos.ne', hN0⟩
  have hr1T : r₁ ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨c.h1q, c.hr₁⟩
  have hr2T : r₂ ∈ (N.primeFactors.erase q).erase r₁ :=
    Finset.mem_erase.mpr ⟨c.h12.symm, Finset.mem_erase.mpr ⟨c.h2q, c.hr₂⟩⟩
  have hab := (perfect_iff_abundancy_eq_two hN.pos).mp hN.perfect
  rw [abundancy_eq_prod_primeFactors hN0, ← Finset.mul_prod_erase _ _ hqT,
    ← Finset.mul_prod_erase _ _ hr1T, ← Finset.mul_prod_erase _ _ hr2T] at hab
  have heq : ∏ x ∈ ord N q r₁ r₂, abundancy (x ^ N.factorization x) =
      ∏ x ∈ ord N q r₁ r₂, fv x := by
    refine Finset.prod_congr rfl fun x hx => ?_
    obtain ⟨hxp, hxe, -⟩ := c.ord_facts hx
    have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hxp.ne_zero
    rw [hxe, abundancy_prime_pow hxp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, fv]
    field_simp
    ring
  change abundancy _ * (abundancy _ * (abundancy _ * ∏ x ∈ ord N q r₁ r₂, _)) = 2 at hab
  rw [heq] at hab
  -- the ordinary part
  have hP := prod_bound (ord N q r₁ r₂) (vec q r₁ r₂) c.vec_inj 300 5 (by norm_num)
    (α := 5 / 18) (by norm_num) (by norm_num) hβ0 hβ1 hγ0 hγ1 C hC
    (fun s hs => le_trans (by norm_num) (c.ord_facts hs).2.2) hsmall
    (fun s hs _ => c.weight hs hβ0 hγ0 hβ hγ) (fun s hs => (c.shape hs).2) (by
      have : kk 300 * (bsum (5 / 18) β γ 300 5 + tl (5 / 18) β γ 5) ≤
          kk 300 * (B + tl (5 / 18) β γ 5) := by
        apply mul_le_mul_of_nonneg_left _ (by unfold kk; positivity); linarith
      linarith)
  have hP' : ∏ s ∈ ord N q r₁ r₂, fv s ≤
      (∏ s ∈ C, fv s) / (1 - kk 300 * (B + tl (5 / 18) β γ 5)) := by
    refine le_trans hP ?_
    have hC0 : 0 ≤ ∏ s ∈ C, fv s :=
      Finset.prod_nonneg fun s hs => le_trans zero_le_one (one_le_fv (hC s hs))
    apply div_le_div_of_nonneg_left hC0 (by linarith)
    have : kk 300 * (bsum (5 / 18) β γ 300 5 + tl (5 / 18) β γ 5) ≤
        kk 300 * (B + tl (5 / 18) β γ 5) := by
      apply mul_le_mul_of_nonneg_left _ (by unfold kk; positivity); linarith
    linarith
  have hP0 : 0 ≤ ∏ s ∈ ord N q r₁ r₂, fv s := Finset.prod_nonneg fun s hs =>
    le_trans zero_le_one (one_le_fv (le_trans (by norm_num) (c.ord_facts hs).2.2))
  have hgq := abundancy_prime_pow_lt c.hq (N.factorization q)
  have hlq := div_pred_le (by norm_num) (show 13 ≤ q by have := c.q_mod; have := c.hq.two_le; omega)
  have hg1 := abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors c.hr₁) (N.factorization r₁)
  have hg2 := abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors c.hr₂) (N.factorization r₂)
  have h0q := abundancy_nonneg (q ^ N.factorization q)
  have h01 := abundancy_nonneg (r₁ ^ N.factorization r₁)
  have h02 := abundancy_nonneg (r₂ ^ N.factorization r₂)
  norm_num at hlq
  have e2 := mul_le_mul (hg2.le.trans hρ₂) hP' hP0 (by linarith)
  have e1 := mul_le_mul (hg1.le.trans hρ₁) e2 (mul_nonneg h02 hP0) (by linarith)
  have e0 := mul_le_mul (hgq.le.trans hlq) e1 (mul_nonneg h01 (mul_nonneg h02 hP0))
    (by norm_num)
  nlinarith


/-! ## Small ordinary primes -/

/-- The small ordinary primes: for each prime `s < 300` with `s ≡ 2 (mod 3)`, every prime
factor of `1 + s + s^2` is `q`, `r₁` or `r₂`. -/
private theorem Ctx.table {N q r₁ r₂ s : ℕ} (c : Ctx N q r₁ r₂) (hs : s ∈ ord N q r₁ r₂)
    (hlt : s < 300) :
    (s = 5 ∧ (31 = q ∨ 31 = r₁ ∨ 31 = r₂)) ∨
    (s = 11 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (19 = q ∨ 19 = r₁ ∨ 19 = r₂)) ∨
    (s = 17 ∧ (307 = q ∨ 307 = r₁ ∨ 307 = r₂)) ∨
    (s = 23 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (79 = q ∨ 79 = r₁ ∨ 79 = r₂)) ∨
    (s = 29 ∧ (13 = q ∨ 13 = r₁ ∨ 13 = r₂) ∧ (67 = q ∨ 67 = r₁ ∨ 67 = r₂)) ∨
    (s = 41 ∧ (1723 = q ∨ 1723 = r₁ ∨ 1723 = r₂)) ∨
    (s = 47 ∧ (37 = q ∨ 37 = r₁ ∨ 37 = r₂) ∧ (61 = q ∨ 61 = r₁ ∨ 61 = r₂)) ∨
    (s = 53 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (409 = q ∨ 409 = r₁ ∨ 409 = r₂)) ∨
    (s = 59 ∧ (3541 = q ∨ 3541 = r₁ ∨ 3541 = r₂)) ∨
    (s = 71 ∧ (5113 = q ∨ 5113 = r₁ ∨ 5113 = r₂)) ∨
    (s = 83 ∧ (19 = q ∨ 19 = r₁ ∨ 19 = r₂) ∧ (367 = q ∨ 367 = r₁ ∨ 367 = r₂)) ∨
    (s = 89 ∧ (8011 = q ∨ 8011 = r₁ ∨ 8011 = r₂)) ∨
    (s = 101 ∧ (10303 = q ∨ 10303 = r₁ ∨ 10303 = r₂)) ∨
    (s = 107 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (13 = q ∨ 13 = r₁ ∨ 13 = r₂) ∧ (127 = q ∨ 127 = r₁ ∨ 127 = r₂)) ∨
    (s = 113 ∧ (13 = q ∨ 13 = r₁ ∨ 13 = r₂) ∧ (991 = q ∨ 991 = r₁ ∨ 991 = r₂)) ∨
    (s = 131 ∧ (17293 = q ∨ 17293 = r₁ ∨ 17293 = r₂)) ∨
    (s = 137 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (37 = q ∨ 37 = r₁ ∨ 37 = r₂) ∧ (73 = q ∨ 73 = r₁ ∨ 73 = r₂)) ∨
    (s = 149 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (31 = q ∨ 31 = r₁ ∨ 31 = r₂) ∧ (103 = q ∨ 103 = r₁ ∨ 103 = r₂)) ∨
    (s = 167 ∧ (28057 = q ∨ 28057 = r₁ ∨ 28057 = r₂)) ∨
    (s = 173 ∧ (30103 = q ∨ 30103 = r₁ ∨ 30103 = r₂)) ∨
    (s = 179 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (4603 = q ∨ 4603 = r₁ ∨ 4603 = r₂)) ∨
    (s = 191 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (13 = q ∨ 13 = r₁ ∨ 13 = r₂) ∧ (31 = q ∨ 31 = r₁ ∨ 31 = r₂)) ∨
    (s = 197 ∧ (19 = q ∨ 19 = r₁ ∨ 19 = r₂) ∧ (2053 = q ∨ 2053 = r₁ ∨ 2053 = r₂)) ∨
    (s = 227 ∧ (73 = q ∨ 73 = r₁ ∨ 73 = r₂) ∧ (709 = q ∨ 709 = r₁ ∨ 709 = r₂)) ∨
    (s = 233 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (7789 = q ∨ 7789 = r₁ ∨ 7789 = r₂)) ∨
    (s = 239 ∧ (19 = q ∨ 19 = r₁ ∨ 19 = r₂) ∧ (3019 = q ∨ 3019 = r₁ ∨ 3019 = r₂)) ∨
    (s = 251 ∧ (43 = q ∨ 43 = r₁ ∨ 43 = r₂) ∧ (1471 = q ∨ 1471 = r₁ ∨ 1471 = r₂)) ∨
    (s = 257 ∧ (61 = q ∨ 61 = r₁ ∨ 61 = r₂) ∧ (1087 = q ∨ 1087 = r₁ ∨ 1087 = r₂)) ∨
    (s = 263 ∧ (7 = q ∨ 7 = r₁ ∨ 7 = r₂) ∧ (13 = q ∨ 13 = r₁ ∨ 13 = r₂) ∧ (109 = q ∨ 109 = r₁ ∨ 109 = r₂)) ∨
    (s = 269 ∧ (13 = q ∨ 13 = r₁ ∨ 13 = r₂) ∧ (37 = q ∨ 37 = r₁ ∨ 37 = r₂) ∧ (151 = q ∨ 151 = r₁ ∨ 151 = r₂)) ∨
    (s = 281 ∧ (109 = q ∨ 109 = r₁ ∨ 109 = r₂) ∧ (727 = q ∨ 727 = r₁ ∨ 727 = r₂)) ∨
    (s = 293 ∧ (86143 = q ∨ 86143 = r₁ ∨ 86143 = r₂)) := by
  obtain ⟨hsp, he, h5⟩ := c.ord_facts hs
  have hm := OPNThreeFree.source_mod_three c.opn.perfect c.h3 hsp he
  have hL : s = 5 ∨ s = 11 ∨ s = 17 ∨ s = 23 ∨ s = 29 ∨ s = 41 ∨ s = 47 ∨ s = 53 ∨ s = 59 ∨ s = 71 ∨ s = 83 ∨ s = 89 ∨ s = 101 ∨ s = 107 ∨ s = 113 ∨ s = 131 ∨ s = 137 ∨ s = 149 ∨ s = 167 ∨ s = 173 ∨ s = 179 ∨ s = 191 ∨ s = 197 ∨ s = 227 ∨ s = 233 ∨ s = 239 ∨ s = 251 ∨ s = 257 ∨ s = 263 ∨ s = 269 ∨ s = 281 ∨ s = 293 := by
    interval_cases s <;> first | omega | (exfalso; norm_num at hsp)
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, (c.tgt hs (d := 31) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 19) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 307) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 79) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 13) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 67) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 1723) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 37) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 61) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 409) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 3541) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 5113) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 19) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 367) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 8011) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 10303) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 13) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 127) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 13) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 991) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 17293) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 37) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 73) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 31) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 103) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 28057) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 30103) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 4603) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 13) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 31) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 19) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 2053) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 73) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 709) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 7789) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 19) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 3019) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 43) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 1471) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 61) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 1087) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 7) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 13) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 109) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 13) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 37) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 151) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, (c.tgt hs (d := 109) (by norm_num) (by norm_num)).1, (c.tgt hs (d := 727) (by norm_num) (by norm_num)).1⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨rfl, (c.tgt hs (d := 86143) (by norm_num) (by norm_num)).1⟩

/-! ## Box sums -/

private theorem box_0_0 : bsum (5 / 18) (0) (0) 300 5 ≤ 17 / 2500 := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]

private theorem box_0_7 : bsum (5 / 18) (0) (14 / 37) 300 5 ≤ 441 / 10000 := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]

private theorem box_0_13 : bsum (5 / 18) (0) (5 / 18) 300 5 ≤ 3 / 80 := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]

private theorem box_0_31 : bsum (5 / 18) (0) (2 / 11) 300 5 ≤ 39 / 1250 := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]

private theorem box_7_13 : bsum (5 / 18) (14 / 37) (5 / 18) 300 5 ≤ 1473 / 10000 := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]

private theorem box_7_31 : bsum (5 / 18) (14 / 37) (2 / 11) 300 5 ≤ 1193 / 10000 := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]

private theorem box_13_13 : bsum (5 / 18) (5 / 18) (5 / 18) 300 5 ≤ 243 / 2000 := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]

private theorem box_13_31 : bsum (5 / 18) (5 / 18) (2 / 11) 300 5 ≤ 1 / 10 := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]

private theorem box_31_31 : bsum (5 / 18) (2 / 11) (2 / 11) 300 5 ≤ 51 / 625 := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]

/-! ## Leaves -/

set_option maxHeartbeats 1000000 in
private theorem leaf_5_n2 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 5)
    (h2 : r₂ % 3 = 2 ∧ 11 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 5 ≤ r₁ := by omega
  have hm2 : 11 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167} (β := 0) (γ := 0) (ρ₁ := 5 / 4) (ρ₂ := 11 / 10)
    (B := 17 / 2500) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inr (by omega))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_0 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_5_7 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 5)
    (h2 : r₂ = 7) : False := by
  have hq12 := c.q_mod
  have hm1 : 5 ≤ r₁ := by omega
  have hm2 : 7 ≤ r₂ := by omega
  refine c.close {53, 59, 71, 131, 167, 233} (β := 0) (γ := 14 / 37) (ρ₁ := 5 / 4) (ρ₂ := 7 / 6)
    (B := 441 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_7 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_5_13 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 5)
    (h2 : r₂ = 13) : False := by
  have hq12 := c.q_mod
  have hm1 : 5 ≤ r₁ := by omega
  have hm2 : 13 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167} (β := 0) (γ := 5 / 18) (ρ₁ := 5 / 4) (ρ₂ := 13 / 12)
    (B := 3 / 80) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (13 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_13 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_5_19 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 5)
    (h2 : r₂ = 19) : False := by
  have hq12 := c.q_mod
  have hm1 : 5 ≤ r₁ := by omega
  have hm2 : 19 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167, 197} (β := 0) (γ := 5 / 18) (ρ₁ := 5 / 4) (ρ₂ := 19 / 18)
    (B := 3 / 80) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (19 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_13 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_5_31 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 5)
    (h2 : r₂ = 31) : False := by
  have hq12 := c.q_mod
  have hm1 : 5 ≤ r₁ := by omega
  have hm2 : 31 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167} (β := 0) (γ := 2 / 11) (ρ₁ := 5 / 4) (ρ₂ := 31 / 30)
    (B := 39 / 1250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_5_37 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 5)
    (h2 : r₂ = 37) : False := by
  have hq12 := c.q_mod
  have hm1 : 5 ≤ r₁ := by omega
  have hm2 : 37 ≤ r₂ := by omega
  refine c.close {47, 59, 71, 131, 167} (β := 0) (γ := 2 / 11) (ρ₁ := 5 / 4) (ρ₂ := 37 / 36)
    (B := 39 / 1250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (37 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_5_43 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 5)
    (h2 : r₂ = 43) : False := by
  have hq12 := c.q_mod
  have hm1 : 5 ≤ r₁ := by omega
  have hm2 : 43 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167} (β := 0) (γ := 2 / 11) (ρ₁ := 5 / 4) (ρ₂ := 43 / 42)
    (B := 39 / 1250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (43 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_5_big {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 5)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 5 ≤ r₁ := by omega
  have hm2 : 61 ≤ r₂ := by omega
  refine c.close {17, 29, 41, 47, 59, 71, 89, 101, 113, 131, 167, 173, 227, 257, 281, 293} (β := 0) (γ := 2 / 11) (ρ₁ := 5 / 4) (ρ₂ := 61 / 60)
    (B := 39 / 1250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_n2_n2 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ % 3 = 2 ∧ 11 ≤ r₁)
    (h2 : r₂ % 3 = 2 ∧ 11 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 11 ≤ r₁ := by omega
  have hm2 : 11 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167} (β := 0) (γ := 0) (ρ₁ := 11 / 10) (ρ₂ := 11 / 10)
    (B := 17 / 2500) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inr (by omega))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_0 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_n2_7 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ % 3 = 2 ∧ 11 ≤ r₁)
    (h2 : r₂ = 7) : False := by
  have hq12 := c.q_mod
  have hm1 : 11 ≤ r₁ := by omega
  have hm2 : 7 ≤ r₂ := by omega
  refine c.close {53, 59, 71, 131, 167, 233} (β := 0) (γ := 14 / 37) (ρ₁ := 11 / 10) (ρ₂ := 7 / 6)
    (B := 441 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_7 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_n2_13 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ % 3 = 2 ∧ 11 ≤ r₁)
    (h2 : r₂ = 13) : False := by
  have hq12 := c.q_mod
  have hm1 : 11 ≤ r₁ := by omega
  have hm2 : 13 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167} (β := 0) (γ := 5 / 18) (ρ₁ := 11 / 10) (ρ₂ := 13 / 12)
    (B := 3 / 80) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (13 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_13 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_n2_19 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ % 3 = 2 ∧ 11 ≤ r₁)
    (h2 : r₂ = 19) : False := by
  have hq12 := c.q_mod
  have hm1 : 11 ≤ r₁ := by omega
  have hm2 : 19 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167, 197} (β := 0) (γ := 5 / 18) (ρ₁ := 11 / 10) (ρ₂ := 19 / 18)
    (B := 3 / 80) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (19 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_13 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_n2_31 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ % 3 = 2 ∧ 11 ≤ r₁)
    (h2 : r₂ = 31) : False := by
  have hq12 := c.q_mod
  have hm1 : 11 ≤ r₁ := by omega
  have hm2 : 31 ≤ r₂ := by omega
  refine c.close {5, 59, 71, 131, 167} (β := 0) (γ := 2 / 11) (ρ₁ := 11 / 10) (ρ₂ := 31 / 30)
    (B := 39 / 1250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_n2_37 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ % 3 = 2 ∧ 11 ≤ r₁)
    (h2 : r₂ = 37) : False := by
  have hq12 := c.q_mod
  have hm1 : 11 ≤ r₁ := by omega
  have hm2 : 37 ≤ r₂ := by omega
  refine c.close {47, 59, 71, 131, 167} (β := 0) (γ := 2 / 11) (ρ₁ := 11 / 10) (ρ₂ := 37 / 36)
    (B := 39 / 1250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (37 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_n2_43 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ % 3 = 2 ∧ 11 ≤ r₁)
    (h2 : r₂ = 43) : False := by
  have hq12 := c.q_mod
  have hm1 : 11 ≤ r₁ := by omega
  have hm2 : 43 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167} (β := 0) (γ := 2 / 11) (ρ₁ := 11 / 10) (ρ₂ := 43 / 42)
    (B := 39 / 1250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (43 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_n2_big {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ % 3 = 2 ∧ 11 ≤ r₁)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 11 ≤ r₁ := by omega
  have hm2 : 61 ≤ r₂ := by omega
  refine c.close {17, 29, 41, 47, 59, 71, 89, 101, 113, 131, 167, 173, 227, 257, 281, 293} (β := 0) (γ := 2 / 11) (ρ₁ := 11 / 10) (ρ₂ := 61 / 60)
    (B := 39 / 1250) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by omega))
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_0_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_7_13 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ = 13) : False := by
  have hq12 := c.q_mod
  have hm1 : 7 ≤ r₁ := by omega
  have hm2 : 13 ≤ r₂ := by omega
  refine c.close {53, 59, 71, 131, 167, 233, 263} (β := 14 / 37) (γ := 5 / 18) (ρ₁ := 7 / 6) (ρ₂ := 13 / 12)
    (B := 1473 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (13 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_7_13 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_7_19 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ = 19) : False := by
  have hq12 := c.q_mod
  have hm1 : 7 ≤ r₁ := by omega
  have hm2 : 19 ≤ r₂ := by omega
  refine c.close {11, 53, 59, 71, 131, 167, 197, 233} (β := 14 / 37) (γ := 5 / 18) (ρ₁ := 7 / 6) (ρ₂ := 19 / 18)
    (B := 1473 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (19 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_7_13 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_7_31_a {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ = 31) (hq : q = 409) : False := by
  have hq12 := c.q_mod
  have hm1 : 7 ≤ r₁ := by omega
  have hm2 : 31 ≤ r₂ := by omega
  refine c.close {5, 53} (β := 14 / 37) (γ := 2 / 11) (ρ₁ := 7 / 6) (ρ₂ := 31 / 30)
    (B := 1193 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_7_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_7_31_b {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ = 31) (hq : q = 3541) : False := by
  have hq12 := c.q_mod
  have hm1 : 7 ≤ r₁ := by omega
  have hm2 : 31 ≤ r₂ := by omega
  refine c.close {5, 59} (β := 14 / 37) (γ := 2 / 11) (ρ₁ := 7 / 6) (ρ₂ := 31 / 30)
    (B := 1193 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_7_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_7_31_c {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ = 31) (hq : q ≠ 409 ∧ q ≠ 3541) : False := by
  have hq12 := c.q_mod
  have hm1 : 7 ≤ r₁ := by omega
  have hm2 : 31 ≤ r₂ := by omega
  refine c.close {5, 71, 131, 167, 191, 233} (β := 14 / 37) (γ := 2 / 11) (ρ₁ := 7 / 6) (ρ₂ := 31 / 30)
    (B := 1193 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_7_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_7_37 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ = 37) : False := by
  have hq12 := c.q_mod
  have hm1 : 7 ≤ r₁ := by omega
  have hm2 : 37 ≤ r₂ := by omega
  refine c.close {47, 53, 59, 71, 131, 137, 167, 233} (β := 14 / 37) (γ := 2 / 11) (ρ₁ := 7 / 6) (ρ₂ := 37 / 36)
    (B := 1193 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (37 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_7_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_7_43 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ = 43) : False := by
  have hq12 := c.q_mod
  have hm1 : 7 ≤ r₁ := by omega
  have hm2 : 43 ≤ r₂ := by omega
  refine c.close {53, 59, 71, 131, 167, 233} (β := 14 / 37) (γ := 2 / 11) (ρ₁ := 7 / 6) (ρ₂ := 43 / 42)
    (B := 1193 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (43 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_7_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_7_307 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ = 307) : False := by
  have hq12 := c.q_mod
  have hm1 : 7 ≤ r₁ := by omega
  have hm2 : 307 ≤ r₂ := by omega
  refine c.close {17, 53, 59, 71, 131, 167, 233} (β := 14 / 37) (γ := 2 / 11) (ρ₁ := 7 / 6) (ρ₂ := 307 / 306)
    (B := 1193 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (307 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_7_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_7_big307 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂ ∧ r₂ ≠ 307) : False := by
  have hq12 := c.q_mod
  have hm1 : 7 ≤ r₁ := by omega
  have hm2 : 61 ≤ r₂ := by omega
  refine c.close {23, 29, 41, 47, 53, 59, 71, 89, 101, 107, 113, 131, 137, 167, 173, 179, 227, 233, 257, 263, 281, 293} (β := 14 / 37) (γ := 2 / 11) (ρ₁ := 7 / 6) (ρ₂ := 61 / 60)
    (B := 1193 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (7 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_7_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_13_19 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 13)
    (h2 : r₂ = 19) : False := by
  have hq12 := c.q_mod
  have hm1 : 13 ≤ r₁ := by omega
  have hm2 : 19 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167, 197} (β := 5 / 18) (γ := 5 / 18) (ρ₁ := 13 / 12) (ρ₂ := 19 / 18)
    (B := 243 / 2000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (13 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (19 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_13_13 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_13_31 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 13)
    (h2 : r₂ = 31) : False := by
  have hq12 := c.q_mod
  have hm1 : 13 ≤ r₁ := by omega
  have hm2 : 31 ≤ r₂ := by omega
  refine c.close {5, 59, 71, 131, 167} (β := 5 / 18) (γ := 2 / 11) (ρ₁ := 13 / 12) (ρ₂ := 31 / 30)
    (B := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (13 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_13_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_13_37 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 13)
    (h2 : r₂ = 37) : False := by
  have hq12 := c.q_mod
  have hm1 : 13 ≤ r₁ := by omega
  have hm2 : 37 ≤ r₂ := by omega
  refine c.close {47, 59, 71, 131, 167} (β := 5 / 18) (γ := 2 / 11) (ρ₁ := 13 / 12) (ρ₂ := 37 / 36)
    (B := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (13 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (37 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_13_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_13_43 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 13)
    (h2 : r₂ = 43) : False := by
  have hq12 := c.q_mod
  have hm1 : 13 ≤ r₁ := by omega
  have hm2 : 43 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167} (β := 5 / 18) (γ := 2 / 11) (ρ₁ := 13 / 12) (ρ₂ := 43 / 42)
    (B := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (13 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (43 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_13_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_13_big {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 13)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 13 ≤ r₁ := by omega
  have hm2 : 61 ≤ r₂ := by omega
  refine c.close {17, 29, 41, 47, 59, 71, 89, 101, 113, 131, 167, 173, 227, 257, 269, 281, 293} (β := 5 / 18) (γ := 2 / 11) (ρ₁ := 13 / 12) (ρ₂ := 61 / 60)
    (B := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (13 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_13_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_19_31 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 19)
    (h2 : r₂ = 31) : False := by
  have hq12 := c.q_mod
  have hm1 : 19 ≤ r₁ := by omega
  have hm2 : 31 ≤ r₂ := by omega
  refine c.close {5, 59, 71, 131, 167, 197} (β := 5 / 18) (γ := 2 / 11) (ρ₁ := 19 / 18) (ρ₂ := 31 / 30)
    (B := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (19 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_13_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_19_37 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 19)
    (h2 : r₂ = 37) : False := by
  have hq12 := c.q_mod
  have hm1 : 19 ≤ r₁ := by omega
  have hm2 : 37 ≤ r₂ := by omega
  refine c.close {47, 59, 71, 131, 167, 197} (β := 5 / 18) (γ := 2 / 11) (ρ₁ := 19 / 18) (ρ₂ := 37 / 36)
    (B := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (19 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (37 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_13_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_19_43 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 19)
    (h2 : r₂ = 43) : False := by
  have hq12 := c.q_mod
  have hm1 : 19 ≤ r₁ := by omega
  have hm2 : 43 ≤ r₂ := by omega
  refine c.close {59, 71, 131, 167, 197} (β := 5 / 18) (γ := 2 / 11) (ρ₁ := 19 / 18) (ρ₂ := 43 / 42)
    (B := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (19 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (43 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_13_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_19_big {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 19)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 19 ≤ r₁ := by omega
  have hm2 : 61 ≤ r₂ := by omega
  refine c.close {17, 29, 41, 47, 59, 71, 83, 89, 101, 113, 131, 167, 173, 197, 227, 239, 257, 281, 293} (β := 5 / 18) (γ := 2 / 11) (ρ₁ := 19 / 18) (ρ₂ := 61 / 60)
    (B := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (19 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_13_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_31_37 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 31)
    (h2 : r₂ = 37) : False := by
  have hq12 := c.q_mod
  have hm1 : 31 ≤ r₁ := by omega
  have hm2 : 37 ≤ r₂ := by omega
  refine c.close {5, 47, 59, 71, 131, 167} (β := 2 / 11) (γ := 2 / 11) (ρ₁ := 31 / 30) (ρ₂ := 37 / 36)
    (B := 51 / 625) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (37 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_31_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_31_43 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 31)
    (h2 : r₂ = 43) : False := by
  have hq12 := c.q_mod
  have hm1 : 31 ≤ r₁ := by omega
  have hm2 : 43 ≤ r₂ := by omega
  refine c.close {5, 59, 71, 131, 167} (β := 2 / 11) (γ := 2 / 11) (ρ₁ := 31 / 30) (ρ₂ := 43 / 42)
    (B := 51 / 625) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (43 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_31_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_31_big {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 31)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 31 ≤ r₁ := by omega
  have hm2 : 61 ≤ r₂ := by omega
  refine c.close {5, 17, 29, 41, 47, 59, 71, 89, 101, 113, 131, 167, 173, 227, 257, 281, 293} (β := 2 / 11) (γ := 2 / 11) (ρ₁ := 31 / 30) (ρ₂ := 61 / 60)
    (B := 51 / 625) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (31 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_31_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_37_43 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 37)
    (h2 : r₂ = 43) : False := by
  have hq12 := c.q_mod
  have hm1 : 37 ≤ r₁ := by omega
  have hm2 : 43 ≤ r₂ := by omega
  refine c.close {47, 59, 71, 131, 167} (β := 2 / 11) (γ := 2 / 11) (ρ₁ := 37 / 36) (ρ₂ := 43 / 42)
    (B := 51 / 625) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (37 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (43 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_31_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_37_big {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 37)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 37 ≤ r₁ := by omega
  have hm2 : 61 ≤ r₂ := by omega
  refine c.close {17, 29, 41, 47, 59, 71, 89, 101, 113, 131, 167, 173, 227, 257, 269, 281, 293} (β := 2 / 11) (γ := 2 / 11) (ρ₁ := 37 / 36) (ρ₂ := 61 / 60)
    (B := 51 / 625) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (37 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_31_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_43_big {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 43)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 43 ≤ r₁ := by omega
  have hm2 : 61 ≤ r₂ := by omega
  refine c.close {17, 29, 41, 47, 59, 71, 89, 101, 113, 131, 167, 173, 227, 251, 257, 281, 293} (β := 2 / 11) (γ := 2 / 11) (ρ₁ := 43 / 42) (ρ₂ := 61 / 60)
    (B := 51 / 625) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (43 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_31_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
private theorem leaf_big_big {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ % 3 = 1 ∧ 61 ≤ r₁)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂) : False := by
  have hq12 := c.q_mod
  have hm1 : 61 ≤ r₁ := by omega
  have hm2 : 61 ≤ r₂ := by omega
  refine c.close {17, 29, 41, 47, 59, 71, 89, 101, 113, 131, 167, 173, 227, 257, 281, 293} (β := 2 / 11) (γ := 2 / 11) (ρ₁ := 61 / 60) (ρ₂ := 61 / 60)
    (B := 51 / 625) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₁ by exact_mod_cast hm1]))
    (Or.inl (by nlinarith [show (61 : ℚ) ≤ r₂ by exact_mod_cast hm2]))
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_31_31 (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  rcases c.table hs hlt with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega

set_option maxHeartbeats 1000000 in
/-- Splitting the pair `(7, 31)` by the value of `q`. -/
private theorem leaf_7_31 {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7) (h2 : r₂ = 31) : False := by
  by_cases ha : q = 409
  · exact leaf_7_31_a c h1 h2 ha
  by_cases hb : q = 3541
  · exact leaf_7_31_b c h1 h2 hb
  exact leaf_7_31_c c h1 h2 ⟨ha, hb⟩

set_option maxHeartbeats 1000000 in
/-- Splitting the pair `(7, ≥ 61)` by `r₂ = 307`. -/
private theorem leaf_7_big {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) (h1 : r₁ = 7)
    (h2 : r₂ % 3 = 1 ∧ 61 ≤ r₂) : False := by
  by_cases h : r₂ = 307
  · exact leaf_7_307 c h1 h
  · exact leaf_7_big307 c h1 ⟨h2.1, h2.2, h⟩

/-- The class of an exceptional prime. -/
private theorem Ctx.cls {N q r₁ r₂ r : ℕ} (c : Ctx N q r₁ r₂) (hr : r ∈ N.primeFactors) :
    r = 5 ∨ (r % 3 = 2 ∧ 11 ≤ r) ∨ r = 7 ∨ r = 13 ∨ r = 19 ∨ r = 31 ∨ r = 37 ∨ r = 43 ∨
      (r % 3 = 1 ∧ 61 ≤ r) := by
  obtain ⟨h5, h3⟩ := c.five_le hr
  have hp := Nat.prime_of_mem_primeFactors hr
  by_cases hl : 61 ≤ r
  · omega
  · interval_cases r <;> first | omega | (exfalso; norm_num at hp)

private theorem Ctx.contra {N q r₁ r₂ : ℕ} (c : Ctx N q r₁ r₂) : False := by
  have h12 := c.h12
  rcases c.cls c.hr₁ with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
  rcases c.cls c.hr₂ with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
  · omega
  · exact leaf_5_n2 c h1 h2
  · exact leaf_5_7 c h1 h2
  · exact leaf_5_13 c h1 h2
  · exact leaf_5_19 c h1 h2
  · exact leaf_5_31 c h1 h2
  · exact leaf_5_37 c h1 h2
  · exact leaf_5_43 c h1 h2
  · exact leaf_5_big c h1 h2
  · exact leaf_5_n2 c.swap h2 h1
  · exact leaf_n2_n2 c h1 h2
  · exact leaf_n2_7 c h1 h2
  · exact leaf_n2_13 c h1 h2
  · exact leaf_n2_19 c h1 h2
  · exact leaf_n2_31 c h1 h2
  · exact leaf_n2_37 c h1 h2
  · exact leaf_n2_43 c h1 h2
  · exact leaf_n2_big c h1 h2
  · exact leaf_5_7 c.swap h2 h1
  · exact leaf_n2_7 c.swap h2 h1
  · omega
  · exact leaf_7_13 c h1 h2
  · exact leaf_7_19 c h1 h2
  · exact leaf_7_31 c h1 h2
  · exact leaf_7_37 c h1 h2
  · exact leaf_7_43 c h1 h2
  · exact leaf_7_big c h1 h2
  · exact leaf_5_13 c.swap h2 h1
  · exact leaf_n2_13 c.swap h2 h1
  · exact leaf_7_13 c.swap h2 h1
  · omega
  · exact leaf_13_19 c h1 h2
  · exact leaf_13_31 c h1 h2
  · exact leaf_13_37 c h1 h2
  · exact leaf_13_43 c h1 h2
  · exact leaf_13_big c h1 h2
  · exact leaf_5_19 c.swap h2 h1
  · exact leaf_n2_19 c.swap h2 h1
  · exact leaf_7_19 c.swap h2 h1
  · exact leaf_13_19 c.swap h2 h1
  · omega
  · exact leaf_19_31 c h1 h2
  · exact leaf_19_37 c h1 h2
  · exact leaf_19_43 c h1 h2
  · exact leaf_19_big c h1 h2
  · exact leaf_5_31 c.swap h2 h1
  · exact leaf_n2_31 c.swap h2 h1
  · exact leaf_7_31 c.swap h2 h1
  · exact leaf_13_31 c.swap h2 h1
  · exact leaf_19_31 c.swap h2 h1
  · omega
  · exact leaf_31_37 c h1 h2
  · exact leaf_31_43 c h1 h2
  · exact leaf_31_big c h1 h2
  · exact leaf_5_37 c.swap h2 h1
  · exact leaf_n2_37 c.swap h2 h1
  · exact leaf_7_37 c.swap h2 h1
  · exact leaf_13_37 c.swap h2 h1
  · exact leaf_19_37 c.swap h2 h1
  · exact leaf_31_37 c.swap h2 h1
  · omega
  · exact leaf_37_43 c h1 h2
  · exact leaf_37_big c h1 h2
  · exact leaf_5_43 c.swap h2 h1
  · exact leaf_n2_43 c.swap h2 h1
  · exact leaf_7_43 c.swap h2 h1
  · exact leaf_13_43 c.swap h2 h1
  · exact leaf_19_43 c.swap h2 h1
  · exact leaf_31_43 c.swap h2 h1
  · exact leaf_37_43 c.swap h2 h1
  · omega
  · exact leaf_43_big c h1 h2
  · exact leaf_5_big c.swap h2 h1
  · exact leaf_n2_big c.swap h2 h1
  · exact leaf_7_big c.swap h2 h1
  · exact leaf_13_big c.swap h2 h1
  · exact leaf_19_big c.swap h2 h1
  · exact leaf_31_big c.swap h2 h1
  · exact leaf_37_big c.swap h2 h1
  · exact leaf_43_big c.swap h2 h1
  · exact leaf_big_big c h1 h2

end ThreeFreeTwo

open ThreeFreeTwo in
/-- The one exception theorem with no side conditions on `r`. -/
theorem three_dvd_of_one_exception' {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) : 3 ∣ N := by
  by_cases hr : r.Prime ∧ r ≠ q
  · exact three_dvd_of_one_exception h hq hodd hr.1 hr.2 hsq
  · have hq2 : q ≠ 2 := fun h2 =>
      h.not_two_dvd (h2 ▸ Nat.dvd_of_factorization_pos hodd.pos.ne')
    refine three_dvd_of_one_exception h hq hodd Nat.prime_two (Ne.symm hq2) ?_
    intro p hp hpq _
    apply hsq p hp hpq
    rintro rfl
    exact hr ⟨Nat.prime_of_mem_primeFactors hp, hpq⟩

/-- An odd perfect number in which every prime factor other than the special prime `q` and
two further primes `r₁`, `r₂` has exponent exactly 2 is divisible by 3. -/
theorem three_dvd_of_two_exceptions {N q r₁ r₂ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    3 ∣ N := by
  by_contra h3
  by_cases A : r₁ ∈ N.primeFactors ∧ r₁ ≠ q ∧ r₁ ≠ r₂
  · by_cases B : r₂ ∈ N.primeFactors ∧ r₂ ≠ q
    · exact (ThreeFreeTwo.Ctx.mk h hq hodd A.1 B.1 A.2.2 A.2.1 B.2 hsq h3).contra
    · apply h3
      refine three_dvd_of_one_exception' h hq hodd (r := r₁) fun p hp hpq hpr => ?_
      refine hsq p hp hpq hpr ?_
      rintro rfl
      exact B ⟨hp, hpq⟩
  · apply h3
    refine three_dvd_of_one_exception' h hq hodd (r := r₂) fun p hp hpq hpr => ?_
    refine hsq p hp hpq ?_ hpr
    rintro rfl
    exact A ⟨hp, hpq, hpr⟩

end OddPerfect

#print axioms OddPerfect.three_dvd_of_one_exception'
#print axioms OddPerfect.three_dvd_of_two_exceptions
