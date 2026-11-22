import OddPerfect.ThreeFreeException
import OddPerfect.Steuerwald
import OddPerfect.Phi3
import OddPerfect.Valuation
import OddPerfect.ValuationBounds
import OddPerfect.SpecialPrime
import OddPerfect.Reciprocity
import OddPerfect.Certificate

/-!
# Restrained odd perfect numbers divisible by 3

Setting: `N` is an odd perfect number with special prime `q`, `r ≠ q` is a further prime,
and every prime factor other than `q` and `r` has exponent exactly 2 (an *ordinary* prime).
By `three_dvd_of_one_exception`, `3 ∣ N`; since `q ≡ 1 (mod 4)`, `3 ≠ q`.

## Case `r ≠ 3`, so `3^2 ∥ N`

Every ordinary `p ≡ 1 (mod 3)` sends exactly one factor `3` into `σ(N)`, so there are at
most two of them. Forcing from `σ(3^2) = 13` gives nine leaves according to which of the
forced primes `13, 61, 97, 7, 19, 127, 31, 331` equal `q` or `r`; every other branch has
three ordinary primes `≡ 1 (mod 3)`. Five leaves are closed here:

* `q = 13, r = 127` (`7^2, 19^2 ∥ N`), `q = 61, r = 331` (`13^2, 31^2 ∥ N`) and
  `q = 97, r = 7` (`13^2, 61^2 ∥ N`): both units of the `3`-adic budget are spent, so every
  other ordinary prime `t` is `2 (mod 3)` and `σ(t^2)` is supported on four known primes,
  two of them with a ledger cap. An exact kernel checked search (`box_*`, with a bisection
  root candidate whose output is verified through the strict monotonicity of `x^2 + x + 1`)
  lists the `t` with `σ(t^2) < B`; the survivors `11` and `5` die by an abundant divisor
  (`Cert.check_sound`), and `107` is carried in the bound. All other `t` have `σ(t^2) ≥ B`,
  and Rankin's trick (`sum_weight_le`) bounds `∑ 1/(t+1)` by `β ∏ 1/(1 - α_g)` with
  `α_g^4 g ≥ 1` and `β^4 B ≥ 1`. The abundancy then stays below `2` (`close_leaf`).
* `q = 13, r = 19` (`7^2 ∥ N`) and `q = 61, r = 31` (`13^2 ∥ N`): one unit is free, so at
  most one further ordinary prime `x ≡ 1 (mod 3)` exists (`slot_le_one`). Then
  `σ(x^2) = 3 m` with `m` supported on the known primes, and the exact search shows
  `σ(x^2) ≥ 10^24`, so `x ≥ 10^12`; `x` becomes a fourth generator and the argument above
  applies (survivors `11` and `653`, respectively `5`).

The four remaining leaves, stated exactly by `restrained_three_sq_cases`, are closed in later
modules:

* `r = 97` with `13^2, 61^2 ∥ N`: `OddPerfect.RestrainedTwo` (`restrained_not_97`), which also
  shows `q ≡ 1 (mod 3)` in the leaf `r = 61`;
* `q = 13, r = 7`: `OddPerfect.RestrainedThree` (`restrained_not_thirteen_seven`);
* `r = 61` with `13^2 ∥ N`: `OddPerfect.RestrainedFour` (`restrained_not_sixty_one`);
* `r = 13`: `OddPerfect.RestrainedFive` (`restrained_not_thirteen`).

Hence `restrained_exception_eq_three` (in `OddPerfect.RestrainedFive`) gives `r = 3`. Ochem and
Zelinsky (arXiv 2607.19746, Section 3) close these leaves with searches to `10^10`, long factor
trees and Nielsen's `ω(N) ≥ 10`; the conclusion `r = 3` is the first half of their Theorem 1.

## Case `r = 3`

`restrained_exception_three`: `v_3(N)` is even and at least `4`, `q ≡ 1 (mod 3)` (a special
prime `2 (mod 3)` divides no `σ(p^2)`, so it divides `σ(3^{e})` with `e` even, making `3` a
quadratic residue modulo `q`, against reciprocity), and `5 ∤ N` (the chain
`5 → 31 → 331 → 7` makes `3^4 5^2 7^2` abundant), and `7 ∤ N` (a factor tree through
`19, 127, 5419, 31, 331, 313, 1009, 181`, closed by overflow at `7` or abundancy). This case is open in the literature: the
paper only proves `v_3(N) ≥ 2.3 · 10^10` by a three week sieve.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace Restrained

/-! ## Rational helpers -/

/-- The abundancy `σ(s^2)/s^2` of an exact square. -/
private def fval (s : ℕ) : ℚ := ((s : ℚ) ^ 2 + s + 1) / s ^ 2

private theorem abundancy_sq {p : ℕ} (hp : p.Prime) : abundancy (p ^ 2) = fval p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [abundancy_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fval]
  field_simp
  ring

private theorem abundancy_nonneg' (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy; positivity

private theorem one_le_fval {s : ℕ} (hs : 1 ≤ s) : 1 ≤ fval s := by
  have hs' : (1 : ℚ) ≤ s := by exact_mod_cast hs
  unfold fval
  rw [le_div_iff₀ (pow_pos (by linarith) 2)]
  nlinarith

private theorem fval_sub_le {s : ℕ} (hs : 3 ≤ s) : fval s - 1 ≤ 2 * (1 / ((s : ℚ) + 1)) := by
  have hs' : (3 : ℚ) ≤ s := by exact_mod_cast hs
  unfold fval
  have hs0 : (0 : ℚ) < s := by linarith
  rw [div_sub_one (pow_pos hs0 2).ne', mul_one_div,
    div_le_div_iff₀ (pow_pos hs0 2) (by positivity)]
  nlinarith

private theorem prod_one_add_mul_le {ι : Type*} [DecidableEq ι] (T : Finset ι) (x : ι → ℚ)
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

private theorem geom_le {α : ℚ} (h0 : 0 ≤ α) (h1 : α < 1) (K : ℕ) :
    ∑ i ∈ Finset.range K, α ^ i ≤ 1 / (1 - α) := by
  have := geom_sum_Ico_le_of_lt_one (x := α) (m := 0) (n := K) h0 h1
  rwa [← Finset.range_eq_Ico, pow_zero] at this

/-! ## Four generator representation and the Rankin bound -/

/-- A positive integer whose prime factors lie in `{a, b, c, d}` is the product of the
corresponding prime powers. -/
private theorem eq_four_pow {V a b c d : ℕ} (hV : V ≠ 0) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hsub : V.primeFactors ⊆ {a, b, c, d}) :
    V = a ^ V.factorization a * b ^ V.factorization b * c ^ V.factorization c *
      d ^ V.factorization d := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hV]
  rw [Finsupp.prod_of_support_subset _ (s := {a, b, c, d}) (by rwa [Nat.support_factorization])
    _ (fun _ _ => pow_zero _)]
  rw [Finset.prod_insert (by simp [hab, hac, had]), Finset.prod_insert (by simp [hbc, hbd]),
    Finset.prod_pair hcd]
  ring

/-- The weight bound of one ordinary prime: if `B ≤ V < (t + 1)^2` and
`V = a^i b^j c^k d^l`, then `1 / (t + 1) ≤ β α₁^i α₂^j α₃^k α₄^l`. -/
private theorem weight_le {t a b c d i j k l B : ℕ} {α₁ α₂ α₃ α₄ β : ℚ}
    (h1 : 0 ≤ α₁) (h2 : 0 ≤ α₂) (h3 : 0 ≤ α₃) (h4 : 0 ≤ α₄) (hβ : 0 ≤ β)
    (g1 : 1 ≤ α₁ ^ 4 * a) (g2 : 1 ≤ α₂ ^ 4 * b) (g3 : 1 ≤ α₃ ^ 4 * c) (g4 : 1 ≤ α₄ ^ 4 * d)
    (gB : 1 ≤ β ^ 4 * B) (hB : B ≤ a ^ i * b ^ j * c ^ k * d ^ l)
    (hlt : a ^ i * b ^ j * c ^ k * d ^ l < (t + 1) ^ 2) :
    1 / ((t : ℚ) + 1) ≤ β * (α₁ ^ i * α₂ ^ j * α₃ ^ k * α₄ ^ l) := by
  set P := α₁ ^ i * α₂ ^ j * α₃ ^ k * α₄ ^ l with hP
  set V : ℕ := a ^ i * b ^ j * c ^ k * d ^ l with hV
  have hP0 : 0 ≤ P := by positivity
  have hPV : 1 ≤ P ^ 4 * V := by
    have : P ^ 4 * (V : ℚ) =
        (α₁ ^ 4 * a) ^ i * (α₂ ^ 4 * b) ^ j * (α₃ ^ 4 * c) ^ k * (α₄ ^ 4 * d) ^ l := by
      simp only [hP, hV]; push_cast; ring
    rw [this]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ g1) (one_le_pow₀ g2)) (one_le_pow₀ g3))
      (one_le_pow₀ g4)
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
      have : (V : ℚ) ^ 2 ≤ (((t : ℚ) + 1) ^ 2) ^ 2 := by
        exact pow_le_pow_left₀ hV0 hVt.le 2
      have hc : 0 ≤ β ^ 4 * P ^ 4 := by positivity
      exact mul_le_mul_of_nonneg_left this hc
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

private theorem sum_prod_mul {γ : Type*} (s : Finset ℕ) (t : Finset γ) (f : ℕ → ℚ) (g : γ → ℚ) :
    ∑ u ∈ s ×ˢ t, f u.1 * g u.2 = (∑ i ∈ s, f i) * ∑ v ∈ t, g v := by
  rw [Finset.sum_product, Finset.sum_mul_sum]

/-- Rankin's bound over a finite set of ordinary primes. -/
private theorem sum_weight_le (T : Finset ℕ) {a b c d B : ℕ} {α₁ α₂ α₃ α₄ β : ℚ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : 0 ≤ α₁) (h2 : 0 ≤ α₂) (h3 : 0 ≤ α₃) (h4 : 0 ≤ α₄) (hβ : 0 ≤ β)
    (l1 : α₁ < 1) (l2 : α₂ < 1) (l3 : α₃ < 1) (l4 : α₄ < 1)
    (g1 : 1 ≤ α₁ ^ 4 * a) (g2 : 1 ≤ α₂ ^ 4 * b) (g3 : 1 ≤ α₃ ^ 4 * c) (g4 : 1 ≤ α₄ ^ 4 * d)
    (gB : 1 ≤ β ^ 4 * B)
    (hT : ∀ t ∈ T, 1 ≤ t ∧ (phi3 t).primeFactors ⊆ {a, b, c, d} ∧ B ≤ phi3 t) :
    ∑ t ∈ T, 1 / ((t : ℚ) + 1) ≤
      β * (1 / (1 - α₁) * (1 / (1 - α₂)) * (1 / (1 - α₃)) * (1 / (1 - α₄))) := by
  set π : ℕ → ℕ × ℕ × ℕ × ℕ := fun t => ((phi3 t).factorization a,
    (phi3 t).factorization b, (phi3 t).factorization c, (phi3 t).factorization d) with hπ
  have hrep : ∀ t ∈ T, phi3 t = a ^ (π t).1 * b ^ (π t).2.1 * c ^ (π t).2.2.1 *
      d ^ (π t).2.2.2 := fun t ht =>
    eq_four_pow (by unfold phi3; omega) hab hac had hbc hbd hcd (hT t ht).2.1
  have hinj : Set.InjOn π T := by
    intro x hx y hy hxy
    have : phi3 x = phi3 y := by rw [hrep x hx, hrep y hy, hxy]
    exact phi3_strictMono.injective this
  set F : ℕ × ℕ × ℕ × ℕ → ℚ := fun u => α₁ ^ u.1 * (α₂ ^ u.2.1 * (α₃ ^ u.2.2.1 * α₄ ^ u.2.2.2))
    with hF
  have hw : ∀ t ∈ T, 1 / ((t : ℚ) + 1) ≤ β * F (π t) := by
    intro t ht
    have hlt : phi3 t < (t + 1) ^ 2 := phi3_lt_succ_sq (hT t ht).1
    rw [hrep t ht] at hlt
    have hB := (hT t ht).2.2
    rw [hrep t ht] at hB
    refine (weight_le h1 h2 h3 h4 hβ g1 g2 g3 g4 gB hB hlt).trans_eq ?_
    simp only [hF]; ring
  set K := (T.image π).sup (fun u => max (max u.1 u.2.1) (max u.2.2.1 u.2.2.2)) + 1
  set box := Finset.range K ×ˢ Finset.range K ×ˢ Finset.range K ×ˢ Finset.range K
  have hsub : T.image π ⊆ box := by
    intro u hu
    have := Finset.le_sup (f := fun u => max (max u.1 u.2.1) (max u.2.2.1 u.2.2.2)) hu
    simp only [box, Finset.mem_product, Finset.mem_range]
    omega
  have hF0 : ∀ u, 0 ≤ F u := fun u => by positivity
  have hbox : ∑ u ∈ box, F u = (∑ i ∈ Finset.range K, α₁ ^ i) *
      (∑ i ∈ Finset.range K, α₂ ^ i) * (∑ i ∈ Finset.range K, α₃ ^ i) *
      (∑ i ∈ Finset.range K, α₄ ^ i) := by
    rw [sum_prod_mul _ _ (fun i => α₁ ^ i)
        (fun v : ℕ × ℕ × ℕ => α₂ ^ v.1 * (α₃ ^ v.2.1 * α₄ ^ v.2.2)),
      sum_prod_mul _ _ (fun i => α₂ ^ i) (fun v : ℕ × ℕ => α₃ ^ v.1 * α₄ ^ v.2),
      sum_prod_mul _ _ (fun i => α₃ ^ i) (fun i => α₄ ^ i)]
    ring
  calc ∑ t ∈ T, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ T, β * F (π t) := Finset.sum_le_sum hw
    _ = β * ∑ u ∈ T.image π, F u := by
        rw [← Finset.mul_sum, Finset.sum_image fun x hx y hy h => hinj hx hy h]
    _ ≤ β * ∑ u ∈ box, F u := by
        gcongr
    _ ≤ _ := by
        rw [hbox]
        gcongr
        all_goals first
          | exact geom_le h1 l1 K
          | exact geom_le h2 l2 K
          | exact geom_le h3 l3 K
          | exact geom_le h4 l4 K

/-! ## Closing a leaf by abundancy -/

/-- The per prime bound used for the known components: `p/(p-1)` at the two exceptional
primes and `σ(p^2)/p^2` at the ordinary ones. -/
private def cbound (q r p : ℕ) : ℚ := if p = q ∨ p = r then (p : ℚ) / (p - 1) else fval p

private theorem abundancy_le_cbound {N q r p : ℕ} (hp : p.Prime)
    (hsq : p ≠ q → p ≠ r → N.factorization p = 2) :
    abundancy (p ^ N.factorization p) ≤ cbound q r p := by
  unfold cbound
  split_ifs with hc
  · exact (abundancy_prime_pow_lt hp _).le
  · push Not at hc
    rw [hsq hc.1 hc.2, abundancy_sq hp]

/-- A leaf closes when the known components `K` have abundancy at most `C`, every other
prime factor `t` is an exact square with `σ(t^2)` supported on four primes and
`σ(t^2) ≥ B`, and the Rankin tail leaves room below `2`. -/
private theorem close_leaf {N : ℕ} (h : OddPerfect N) (K : Finset ℕ) (hK : K ⊆ N.primeFactors)
    (c : ℕ → ℚ) (hC : ∀ p ∈ K, abundancy (p ^ N.factorization p) ≤ c p)
    {a b c' d B : ℕ} {α₁ α₂ α₃ α₄ β : ℚ}
    (hab : a ≠ b) (hac : a ≠ c') (had : a ≠ d) (hbc : b ≠ c') (hbd : b ≠ d) (hcd : c' ≠ d)
    (h1 : 0 ≤ α₁) (h2 : 0 ≤ α₂) (h3 : 0 ≤ α₃) (h4 : 0 ≤ α₄) (hβ : 0 ≤ β)
    (l1 : α₁ < 1) (l2 : α₂ < 1) (l3 : α₃ < 1) (l4 : α₄ < 1)
    (g1 : 1 ≤ α₁ ^ 4 * a) (g2 : 1 ≤ α₂ ^ 4 * b) (g3 : 1 ≤ α₃ ^ 4 * c') (g4 : 1 ≤ α₄ ^ 4 * d)
    (gB : 1 ≤ β ^ 4 * B)
    (hT : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2 ∧
      (phi3 t).primeFactors ⊆ {a, b, c', d} ∧ B ≤ phi3 t)
    (hfin : ∏ p ∈ K, c p < 2 * (1 - 2 * (β * (1 / (1 - α₁) * (1 / (1 - α₂)) *
      (1 / (1 - α₃)) * (1 / (1 - α₄)))))) : False := by
  set S := β * (1 / (1 - α₁) * (1 / (1 - α₂)) * (1 / (1 - α₃)) * (1 / (1 - α₄))) with hS
  have hN0 := h.ne_zero
  set T := N.primeFactors \ K with hTdef
  have hTmem : ∀ {t}, t ∈ T → t ∈ N.primeFactors ∧ t ∉ K := fun ht => Finset.mem_sdiff.mp ht
  have ht3 : ∀ t ∈ T, 3 ≤ t := by
    intro t ht
    obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp (hTmem ht).1
    have := hpp.two_le
    have : t ≠ 2 := by rintro rfl; exact h.not_two_dvd hpN
    omega
  have hsum := sum_weight_le T hab hac had hbc hbd hcd h1 h2 h3 h4 hβ l1 l2 l3 l4 g1 g2 g3 g4 gB
    (fun t ht => ⟨by have := ht3 t ht; omega, (hT t (hTmem ht).1 (hTmem ht).2).2⟩)
  have hx0 : ∀ t ∈ T, 0 ≤ fval t - 1 := fun t ht =>
    sub_nonneg.mpr (one_le_fval (by have := ht3 t ht; omega))
  have hG := prod_one_add_mul_le T (fun t => fval t - 1) hx0
  simp only [add_sub_cancel] at hG
  have hxs : ∑ t ∈ T, (fval t - 1) ≤ 2 * S := by
    calc ∑ t ∈ T, (fval t - 1) ≤ ∑ t ∈ T, 2 * (1 / ((t : ℚ) + 1)) :=
          Finset.sum_le_sum fun t ht => fval_sub_le (ht3 t ht)
      _ = 2 * ∑ t ∈ T, 1 / ((t : ℚ) + 1) := by rw [Finset.mul_sum]
      _ ≤ 2 * S := by linarith
  have hab' := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors hN0, ← Finset.prod_sdiff hK] at hab'
  have hTeq : ∏ t ∈ T, abundancy (t ^ N.factorization t) = ∏ t ∈ T, fval t :=
    Finset.prod_congr rfl fun t ht => by
      rw [(hT t (hTmem ht).1 (hTmem ht).2).1,
        abundancy_sq (Nat.prime_of_mem_primeFactors (hTmem ht).1)]
  rw [← hTdef, hTeq] at hab'
  have hP0 : 0 ≤ ∏ t ∈ T, fval t := Finset.prod_nonneg fun t ht =>
    le_trans zero_le_one (one_le_fval (by have := ht3 t ht; omega))
  have hK0 : 0 ≤ ∏ p ∈ K, abundancy (p ^ N.factorization p) :=
    Finset.prod_nonneg fun _ _ => abundancy_nonneg' _
  have hKC : ∏ p ∈ K, abundancy (p ^ N.factorization p) ≤ ∏ p ∈ K, c p :=
    Finset.prod_le_prod (fun _ _ => abundancy_nonneg' _) hC
  have hPT : (∏ t ∈ T, fval t) * (1 - 2 * S) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hxs hP0]
  have hpos : 0 < 1 - 2 * S := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hPT hK0]

/-! ## Structure of the remaining ordinary primes in a saturated leaf -/

/-- If `3^2 ∥ N` and two exact square primes `x, y ≡ 1 (mod 3)` lie in `K`, then every
exact square prime outside `K` is `2 (mod 3)` and every prime factor of its `σ(t^2)`
lies in `K` and differs from `3`. -/
private theorem leaf_struct {N : ℕ} (h : OddPerfect N) (K : Finset ℕ) (hK3 : 3 ∈ K)
    {x y : ℕ} (hx : x.Prime) (hy : y.Prime) (hxy : x ≠ y) (hxK : x ∈ K) (hyK : y ∈ K)
    (hx2 : N.factorization x = 2) (hy2 : N.factorization y = 2) (hx1 : x % 3 = 1)
    (hy1 : y % 3 = 1) (h3 : N.factorization 3 = 2)
    (hord : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2)
    {t : ℕ} (ht : t ∈ N.primeFactors) (htK : t ∉ K) :
    t % 3 = 2 ∧ ∀ d, d.Prime → d ∣ phi3 t → d ∈ K ∧ d ≠ 3 := by
  have key : ∀ s ∈ N.primeFactors, s ∉ K → s % 3 = 2 := by
    intro s hs hsK
    have hsp := Nat.prime_of_mem_primeFactors hs
    have hs3 : s ≠ 3 := by rintro rfl; exact hsK hK3
    have hsx : s ≠ x := by rintro rfl; exact hsK hxK
    have hsy : s ≠ y := by rintro rfl; exact hsK hyK
    by_contra hc
    have hs1 : s % 3 = 1 := by
      have : s % 3 ≠ 0 := fun h0 => hs3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hsp).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
      omega
    have hle := sum_padicValNat_sigma_le_factorization h.perfect Nat.prime_three (by norm_num)
      {x, y, s}
    rw [Finset.sum_insert (by simp [hxy, hsx.symm]), Finset.sum_pair hsy.symm, h3, hx2, hy2,
      hord s hs hsK, sigma_prime_sq hx, sigma_prime_sq hy, sigma_prime_sq hsp,
      padicValNat_three_phi3, padicValNat_three_phi3, padicValNat_three_phi3, if_pos hx1,
      if_pos hy1, if_pos hs1] at hle
    omega
  refine ⟨key t ht htK, fun d hd hdd => ?_⟩
  have htp := Nat.prime_of_mem_primeFactors ht
  have ht2 := key t ht htK
  have hd3 : d ≠ 3 := by
    rintro rfl
    have := (three_dvd_phi3_iff t).1 hdd
    omega
  have hd1 := prime_dvd_phi3_mod_three hd hd3 hdd
  have hdN : d ∣ N := OPNStarter.force_prime h.perfect htp (hord t ht htK) hd
    (by rintro rfl; omega) (by rw [sigma_prime_sq htp]; exact hdd)
  refine ⟨?_, hd3⟩
  by_contra hdK
  have := key d (Nat.mem_primeFactors.mpr ⟨hd, hdN, h.ne_zero⟩) hdK
  omega

/-- Ledger cap: the components over `S` and one further exact square `t` supply at most
`v_x(N)` factors of `x`. -/
private theorem cap_le {N x t : ℕ} (hN : N.Perfect) (hx : x.Prime) (hx2 : x ≠ 2) (S : Finset ℕ)
    (htS : t ∉ S) (htp : t.Prime) (ht2 : N.factorization t = 2) :
    ∑ s ∈ S, padicValNat x (σ 1 (s ^ N.factorization s)) + padicValNat x (phi3 t) ≤
      N.factorization x := by
  have := sum_padicValNat_sigma_le_factorization hN hx hx2 (insert t S)
  rwa [Finset.sum_insert htS, ht2, sigma_prime_sq htp, add_comm] at this

/-! ## Exact search for small values of `σ(t^2)` -/

/-- Bisection with fuel; any output is acceptable, `ok_sound` only uses monotonicity. -/
private def bis (V : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if ((lo + hi) / 2) * ((lo + hi) / 2) + (lo + hi) / 2 + 1 ≤ V then bis V f ((lo + hi) / 2) hi
    else bis V f lo ((lo + hi) / 2)

/-- A candidate root of `m^2 + m + 1 = V`. -/
private def cand (V : ℕ) : ℕ := bis V 70 0 (2 ^ 64)

/-- Certificate test: either `V` lies strictly between two consecutive values of `phi3`,
or `V = phi3 m` with `m` in the list `L`. -/
private def ok (L : List ℕ) (V : ℕ) : Bool :=
  (cand V * cand V + cand V + 1 < V && V < (cand V + 1) * (cand V + 1) + (cand V + 1) + 1) ||
    (cand V * cand V + cand V + 1 == V && L.contains (cand V))

private theorem ok_sound {L : List ℕ} {V t : ℕ} (hok : ok L V = true) (ht : phi3 t = V) : t ∈ L := by
  unfold ok at hok
  set m := cand V
  have e : ∀ n, n * n + n + 1 = phi3 n := fun n => by unfold phi3; ring
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem, e] at hok
  rcases hok with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← ht] at h1 h2
    have := phi3_strictMono.lt_iff_lt.mp h1
    have := phi3_strictMono.lt_iff_lt.mp h2
    omega
  · rw [← ht] at h1
    rw [← phi3_strictMono.injective h1]
    exact h2

/-- Exponent bound from size. -/
private theorem exp_lt_of_pow {c k V B K : ℕ} (hc : 1 ≤ c) (hV0 : 0 < V) (hdvd : c ^ k ∣ V) (hV : V < B)
    (hK : B ≤ c ^ K) : k < K := by
  by_contra hk
  have h1 : c ^ K ≤ c ^ k := Nat.pow_le_pow_right hc (by omega)
  have h2 : c ^ k ≤ V := Nat.le_of_dvd hV0 hdvd
  omega

private theorem search {t a b c d i j k l B I J K L : ℕ} {Ls : List ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hbox : ∀ i < I, ∀ j < J, ∀ k < K, ∀ l < L,
      a ^ i * b ^ j * c ^ k * d ^ l < B → ok Ls (a ^ i * b ^ j * c ^ k * d ^ l) = true)
    (hrep : phi3 t = a ^ i * b ^ j * c ^ k * d ^ l) (hi : i < I) (hj : j < J)
    (hK : B ≤ c ^ K) (hL : B ≤ d ^ L) (hlt : phi3 t < B) : t ∈ Ls := by
  have hV0 : 0 < phi3 t := by unfold phi3; omega
  have hk : k < K := exp_lt_of_pow hc hV0 (by rw [hrep]; exact ⟨a ^ i * b ^ j * d ^ l,
    by ring⟩) hlt hK
  have hl : l < L := exp_lt_of_pow hd hV0 (by rw [hrep]; exact ⟨a ^ i * b ^ j * c ^ k,
    by ring⟩) hlt hL
  exact ok_sound (hbox i hi j hj k hk l hl (hrep ▸ hlt)) hrep

/-! ## Small helpers -/

private theorem mem_pf {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hd : p ∣ N) :
    p ∈ N.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hp, hd, h.ne_zero⟩

private theorem sigma_ne_zero' {p e : ℕ} (hp : p.Prime) : σ 1 (p ^ e) ≠ 0 :=
  (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'

private theorem one_le_pv {x n : ℕ} (hx : x.Prime) (hn : n ≠ 0) (hd : x ∣ n) :
    1 ≤ padicValNat x n := by
  have := Fact.mk hx
  exact one_le_padicValNat_of_dvd hn hd

/-- Three distinct exact square primes `≡ 1 (mod 3)` overflow `3^2 ∥ N`. -/
private theorem three_sq_overflow {N p₁ p₂ p₃ : ℕ} (h : OddPerfect N) (h3 : N.factorization 3 = 2)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime) (e₁ : N.factorization p₁ = 2)
    (e₂ : N.factorization p₂ = 2) (e₃ : N.factorization p₃ = 2) (m₁ : p₁ % 3 = 1)
    (m₂ : p₂ % 3 = 1) (m₃ : p₃ % 3 = 1) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) :
    False := by
  have hle := sum_padicValNat_sigma_le_factorization h.perfect Nat.prime_three (by norm_num)
    {p₁, p₂, p₃}
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23, h3, e₁, e₂, e₃,
    sigma_prime_sq hp₁, sigma_prime_sq hp₂, sigma_prime_sq hp₃, padicValNat_three_phi3,
    padicValNat_three_phi3, padicValNat_three_phi3, if_pos m₁, if_pos m₂, if_pos m₃] at hle
  omega

/-! ## The three saturated leaves -/

private theorem box_97_7 : ∀ i < 1, ∀ j < 2, ∀ k < 7, ∀ l < 15,
    13 ^ i * 61 ^ j * 97 ^ k * 7 ^ l < 10 ^ 12 →
      ok [0, 2, 18] (13 ^ i * 61 ^ j * 97 ^ k * 7 ^ l) = true := by
  decide +kernel

private theorem box_61_331 : ∀ i < 2, ∀ j < 2, ∀ k < 7, ∀ l < 5,
    13 ^ i * 31 ^ j * 61 ^ k * 331 ^ l < 10 ^ 12 →
      ok [0, 3, 5] (13 ^ i * 31 ^ j * 61 ^ k * 331 ^ l) = true := by
  decide +kernel

private theorem box_13_127 : ∀ i < 2, ∀ j < 2, ∀ k < 15, ∀ l < 8,
    7 ^ i * 19 ^ j * 13 ^ k * 127 ^ l < 10 ^ 16 →
      ok [0, 2, 3, 9, 146, 107, 11] (7 ^ i * 19 ^ j * 13 ^ k * 127 ^ l) = true := by
  decide +kernel

/-- Leaf: `3^2, 13^2, 61^2 ∥ N`, special prime `97`, exceptional prime `7`. -/
private theorem leaf_97_7 {N : ℕ} (h : OddPerfect N) (hodd : Odd (N.factorization 97))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 97 → p ≠ 7 → N.factorization p = 2)
    (h3 : 3 ∣ N) (h13 : 13 ∣ N) (h61 : 61 ∣ N) : False := by
  have e3 : N.factorization 3 = 2 :=
    hsq 3 (mem_pf h Nat.prime_three h3) (by norm_num) (by norm_num)
  have e13 : N.factorization 13 = 2 := hsq 13 (mem_pf h (by norm_num) h13) (by norm_num) (by norm_num)
  have e61 : N.factorization 61 = 2 := hsq 61 (mem_pf h (by norm_num) h61) (by norm_num) (by norm_num)
  have h97 : 97 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have h7 : 7 ∣ N := OPNStarter.force_prime h.perfect (by norm_num : Nat.Prime 97) rfl
    (by norm_num) (by norm_num) ((by norm_num : 7 ∣ 97 + 1).trans
      (succ_dvd_sigma_special (by norm_num) hodd))
  set K : Finset ℕ := {3, 13, 61, 97, 7} with hK
  have hKsub : K ⊆ N.primeFactors := by
    intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact mem_pf h (by norm_num) h3
    · exact mem_pf h (by norm_num) h13
    · exact mem_pf h (by norm_num) h61
    · exact mem_pf h (by norm_num) h97
    · exact mem_pf h (by norm_num) h7
  have hord : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2 := fun t ht htK =>
    hsq t ht (fun e => htK (by simp [hK, e])) (fun e => htK (by simp [hK, e]))
  refine close_leaf h K hKsub (cbound 97 7)
    (fun p hp => abundancy_le_cbound (Nat.prime_of_mem_primeFactors (hKsub hp))
      (hsq p (hKsub hp)))
    (a := 13) (b := 61) (c' := 97) (d := 7) (B := 10 ^ 12) (α₁ := 53 / 100) (α₂ := 9 / 25)
    (α₃ := 8 / 25) (α₄ := 13 / 20) (β := 1 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · intro t ht htK
    have htp := Nat.prime_of_mem_primeFactors ht
    have ht2 := hord t ht htK
    obtain ⟨-, hdK⟩ := leaf_struct h K (by simp [hK]) (x := 13) (y := 61) (by norm_num)
      (by norm_num) (by norm_num) (by simp [hK]) (by simp [hK]) e13 e61 (by norm_num)
      (by norm_num) e3 hord ht htK
    have hsupp : (phi3 t).primeFactors ⊆ {13, 61, 97, 7} := by
      intro d hd
      obtain ⟨hdK', hd3⟩ := hdK d (Nat.prime_of_mem_primeFactors hd)
        (Nat.dvd_of_mem_primeFactors hd)
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hdK' ⊢
      omega
    refine ⟨ht2, hsupp, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hV0 : phi3 t ≠ 0 := by unfold phi3; omega
    have hrep := eq_four_pow hV0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hsupp
    have hS1 : t ∉ ({3, 61} : Finset ℕ) := fun hm => htK (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> simp [hK])
    have c13 := cap_le h.perfect (x := 13) (by norm_num) (by norm_num) {3, 61} hS1 htp ht2
    rw [Finset.sum_pair (by norm_num), e3, e61, e13] at c13
    have s1 : 1 ≤ padicValNat 13 (σ 1 (3 ^ 2)) := one_le_pv (by norm_num)
      (sigma_ne_zero' Nat.prime_three) (by rw [sigma_prime_sq Nat.prime_three]; decide)
    have s2 : 1 ≤ padicValNat 13 (σ 1 (61 ^ 2)) := one_le_pv (by norm_num)
      (sigma_ne_zero' (by norm_num)) (by rw [sigma_prime_sq (by norm_num)]; decide)
    have hS2 : t ∉ ({13} : Finset ℕ) := fun hm => htK (by
      rw [Finset.mem_singleton] at hm; subst hm; simp [hK])
    have c61 := cap_le h.perfect (x := 61) (by norm_num) (by norm_num) {13} hS2 htp ht2
    rw [Finset.sum_singleton, e13, e61] at c61
    have s3 : 1 ≤ padicValNat 61 (σ 1 (13 ^ 2)) := one_le_pv (by norm_num)
      (sigma_ne_zero' (by norm_num)) (by rw [sigma_prime_sq (by norm_num)]; decide)
    have hmem := search (I := 1) (J := 2) (K := 7) (L := 15) (by norm_num) (by norm_num)
      box_97_7 hrep (by rw [Nat.factorization_def _ (by norm_num)]; omega)
      (by rw [Nat.factorization_def _ (by norm_num)]; omega) (by norm_num) (by norm_num) hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact absurd htp (by norm_num)
    · exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors ht)
    · exact absurd htp (by norm_num)
  · rw [hK, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num [cbound, fval]

/-- Leaf: `3^2, 13^2, 31^2 ∥ N`, special prime `61`, exceptional prime `331`. -/
private theorem leaf_61_331 {N : ℕ} (h : OddPerfect N) (hodd : Odd (N.factorization 61))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 61 → p ≠ 331 → N.factorization p = 2)
    (h3 : 3 ∣ N) (h13 : 13 ∣ N) (h31 : 31 ∣ N) (h331 : 331 ∣ N) : False := by
  have e3 : N.factorization 3 = 2 :=
    hsq 3 (mem_pf h Nat.prime_three h3) (by norm_num) (by norm_num)
  have e13 : N.factorization 13 = 2 := hsq 13 (mem_pf h (by norm_num) h13) (by norm_num) (by norm_num)
  have e31 : N.factorization 31 = 2 := hsq 31 (mem_pf h (by norm_num) h31) (by norm_num) (by norm_num)
  have h61 : 61 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  set K : Finset ℕ := {3, 13, 31, 61, 331} with hK
  have hKsub : K ⊆ N.primeFactors := by
    intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact mem_pf h (by norm_num) h3
    · exact mem_pf h (by norm_num) h13
    · exact mem_pf h (by norm_num) h31
    · exact mem_pf h (by norm_num) h61
    · exact mem_pf h (by norm_num) h331
  have hord : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2 := fun t ht htK =>
    hsq t ht (fun e => htK (by simp [hK, e])) (fun e => htK (by simp [hK, e]))
  refine close_leaf h K hKsub (cbound 61 331)
    (fun p hp => abundancy_le_cbound (Nat.prime_of_mem_primeFactors (hKsub hp))
      (hsq p (hKsub hp)))
    (a := 13) (b := 31) (c' := 61) (d := 331) (B := 10 ^ 12) (α₁ := 53 / 100)
    (α₂ := 43 / 100) (α₃ := 9 / 25) (α₄ := 6 / 25) (β := 1 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · intro t ht htK
    have htp := Nat.prime_of_mem_primeFactors ht
    have ht2 := hord t ht htK
    obtain ⟨-, hdK⟩ := leaf_struct h K (by simp [hK]) (x := 13) (y := 31) (by norm_num)
      (by norm_num) (by norm_num) (by simp [hK]) (by simp [hK]) e13 e31 (by norm_num)
      (by norm_num) e3 hord ht htK
    have hsupp : (phi3 t).primeFactors ⊆ {13, 31, 61, 331} := by
      intro d hd
      obtain ⟨hdK', hd3⟩ := hdK d (Nat.prime_of_mem_primeFactors hd)
        (Nat.dvd_of_mem_primeFactors hd)
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hdK' ⊢
      omega
    refine ⟨ht2, hsupp, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hV0 : phi3 t ≠ 0 := by unfold phi3; omega
    have hrep := eq_four_pow hV0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hsupp
    have hS1 : t ∉ ({3} : Finset ℕ) := fun hm => htK (by
      rw [Finset.mem_singleton] at hm; subst hm; simp [hK])
    have c13 := cap_le h.perfect (x := 13) (by norm_num) (by norm_num) {3} hS1 htp ht2
    rw [Finset.sum_singleton, e3, e13] at c13
    have s1 : 1 ≤ padicValNat 13 (σ 1 (3 ^ 2)) := one_le_pv (by norm_num)
      (sigma_ne_zero' Nat.prime_three) (by rw [sigma_prime_sq Nat.prime_three]; decide)
    have hS2 : t ∉ ({61} : Finset ℕ) := fun hm => htK (by
      rw [Finset.mem_singleton] at hm; subst hm; simp [hK])
    have c31 := cap_le h.perfect (x := 31) (by norm_num) (by norm_num) {61} hS2 htp ht2
    rw [Finset.sum_singleton, e31] at c31
    have s2 : 1 ≤ padicValNat 31 (σ 1 (61 ^ N.factorization 61)) := one_le_pv (by norm_num)
      (sigma_ne_zero' (by norm_num)) ((by norm_num : 31 ∣ 61 + 1).trans
        (succ_dvd_sigma_special (by norm_num) hodd))
    have hmem := search (I := 2) (J := 2) (K := 7) (L := 5) (by norm_num) (by norm_num)
      box_61_331 hrep (by rw [Nat.factorization_def _ (by norm_num)]; omega)
      (by rw [Nat.factorization_def _ (by norm_num)]; omega) (by norm_num) (by norm_num) hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact absurd htp (by norm_num)
    · exact htK (by simp [hK])
    · have e5 := ht2
      exact Cert.check_sound
        (s := [.exact 3 2, .exact 5 2, .exact 13 2, .exact 31 2, .powDvd 61 1])
        (c := .abundant [(3, 2), (5, 2), (13, 2), (31, 2), (61, 1)]) (by decide +kernel) N h
        (by simp [Cert.State.Holds, Cert.Fact.Holds, e3, e5, e13, e31, h61])
  · rw [hK, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num [cbound, fval]

/-- Leaf: `3^2, 7^2, 19^2 ∥ N`, special prime `13`, exceptional prime `127`. -/
private theorem leaf_13_127 {N : ℕ} (h : OddPerfect N) (hodd : Odd (N.factorization 13))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 13 → p ≠ 127 → N.factorization p = 2)
    (h3 : 3 ∣ N) (h7 : 7 ∣ N) (h19 : 19 ∣ N) (h127 : 127 ∣ N) : False := by
  have e3 : N.factorization 3 = 2 :=
    hsq 3 (mem_pf h Nat.prime_three h3) (by norm_num) (by norm_num)
  have e7 : N.factorization 7 = 2 := hsq 7 (mem_pf h (by norm_num) h7) (by norm_num) (by norm_num)
  have e19 : N.factorization 19 = 2 := hsq 19 (mem_pf h (by norm_num) h19) (by norm_num) (by norm_num)
  have h13 : 13 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  set K : Finset ℕ := {3, 7, 19, 13, 127} with hK
  have hKsub : K ⊆ N.primeFactors := by
    intro p hp
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact mem_pf h (by norm_num) h3
    · exact mem_pf h (by norm_num) h7
    · exact mem_pf h (by norm_num) h19
    · exact mem_pf h (by norm_num) h13
    · exact mem_pf h (by norm_num) h127
  have hord : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2 := fun t ht htK =>
    hsq t ht (fun e => htK (by simp [hK, e])) (fun e => htK (by simp [hK, e]))
  have hT0 : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2 ∧
      (phi3 t).primeFactors ⊆ {7, 19, 13, 127} ∧ (10 ^ 16 ≤ phi3 t ∨ t = 107) := by
    intro t ht htK
    have htp := Nat.prime_of_mem_primeFactors ht
    have ht2 := hord t ht htK
    obtain ⟨-, hdK⟩ := leaf_struct h K (by simp [hK]) (x := 7) (y := 19) (by norm_num)
      (by norm_num) (by norm_num) (by simp [hK]) (by simp [hK]) e7 e19 (by norm_num)
      (by norm_num) e3 hord ht htK
    have hsupp : (phi3 t).primeFactors ⊆ {7, 19, 13, 127} := by
      intro d hd
      obtain ⟨hdK', hd3⟩ := hdK d (Nat.prime_of_mem_primeFactors hd)
        (Nat.dvd_of_mem_primeFactors hd)
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hdK' ⊢
      omega
    refine ⟨ht2, hsupp, ?_⟩
    by_contra hlt
    rw [not_or, not_le] at hlt
    have hV0 : phi3 t ≠ 0 := by unfold phi3; omega
    have hrep := eq_four_pow hV0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hsupp
    have hS1 : t ∉ ({13} : Finset ℕ) := fun hm => htK (by
      rw [Finset.mem_singleton] at hm; subst hm; simp [hK])
    have c7 := cap_le h.perfect (x := 7) (by norm_num) (by norm_num) {13} hS1 htp ht2
    rw [Finset.sum_singleton, e7] at c7
    have s1 : 1 ≤ padicValNat 7 (σ 1 (13 ^ N.factorization 13)) := one_le_pv (by norm_num)
      (sigma_ne_zero' (by norm_num)) ((by norm_num : 7 ∣ 13 + 1).trans
        (succ_dvd_sigma_special (by norm_num) hodd))
    have hS2 : t ∉ ({7} : Finset ℕ) := fun hm => htK (by
      rw [Finset.mem_singleton] at hm; subst hm; simp [hK])
    have c19 := cap_le h.perfect (x := 19) (by norm_num) (by norm_num) {7} hS2 htp ht2
    rw [Finset.sum_singleton, e7, e19] at c19
    have s2 : 1 ≤ padicValNat 19 (σ 1 (7 ^ 2)) := one_le_pv (by norm_num)
      (sigma_ne_zero' (by norm_num)) (by rw [sigma_prime_sq (by norm_num)]; decide)
    have hmem := search (I := 2) (J := 2) (K := 15) (L := 8) (by norm_num) (by norm_num)
      box_13_127 hrep (by rw [Nat.factorization_def _ (by norm_num)]; omega)
      (by rw [Nat.factorization_def _ (by norm_num)]; omega) (by norm_num) (by norm_num)
      hlt.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd htp (by norm_num)
    · exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors ht)
    · exact htK (by simp [hK])
    · exact absurd htp (by norm_num)
    · exact absurd htp (by norm_num)
    · exact hlt.2 rfl
    · have e11 := ht2
      exact Cert.check_sound
        (s := [.exact 3 2, .exact 7 2, .exact 11 2, .exact 19 2, .powDvd 13 1])
        (c := .abundant [(3, 2), (7, 2), (11, 2), (19, 2), (13, 1)]) (by decide +kernel) N h
        (by simp [Cert.State.Holds, Cert.Fact.Holds, e3, e7, e11, e19, h13])
  by_cases h107 : 107 ∣ N
  · have hK' : insert 107 K ⊆ N.primeFactors :=
      Finset.insert_subset (mem_pf h (by norm_num) h107) hKsub
    refine close_leaf h (insert 107 K) hK' (cbound 13 127)
      (fun p hp => abundancy_le_cbound (Nat.prime_of_mem_primeFactors (hK' hp))
        (hsq p (hK' hp)))
      (a := 7) (b := 19) (c' := 13) (d := 127) (B := 10 ^ 16) (α₁ := 13 / 20)
      (α₂ := 12 / 25) (α₃ := 53 / 100) (α₄ := 3 / 10) (β := 1 / 10000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · intro t ht htK
      have htK1 : t ∉ K := fun hm => htK (Finset.mem_insert_of_mem hm)
      have ht107 : t ≠ 107 := fun e => htK (e ▸ Finset.mem_insert_self 107 K)
      obtain ⟨a1, a2, a3⟩ := hT0 t ht htK1
      exact ⟨a1, a2, a3.resolve_right ht107⟩
    · rw [hK, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
      norm_num [cbound, fval]
  · refine close_leaf h K hKsub (cbound 13 127)
      (fun p hp => abundancy_le_cbound (Nat.prime_of_mem_primeFactors (hKsub hp))
        (hsq p (hKsub hp)))
      (a := 7) (b := 19) (c' := 13) (d := 127) (B := 10 ^ 16) (α₁ := 13 / 20)
      (α₂ := 12 / 25) (α₃ := 53 / 100) (α₄ := 3 / 10) (β := 1 / 10000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · intro t ht htK
      obtain ⟨a1, a2, a3⟩ := hT0 t ht htK
      refine ⟨a1, a2, a3.resolve_right ?_⟩
      rintro rfl
      exact h107 (Nat.dvd_of_mem_primeFactors ht)
    · rw [hK, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
      norm_num [cbound, fval]

/-! ## Leaves with one free slot in the `3`-adic budget -/

/-- If `3^2 ∥ N` and one exact square prime `y ≡ 1 (mod 3)` lies in `K0`, then at most one
prime factor outside `K0` is `1 (mod 3)`. -/
private theorem slot_le_one {N : ℕ} (h : OddPerfect N) (h3 : N.factorization 3 = 2) (K0 : Finset ℕ)
    {y : ℕ} (hy : y.Prime) (hyK : y ∈ K0) (hy2 : N.factorization y = 2) (hy1 : y % 3 = 1)
    (hord : ∀ p ∈ N.primeFactors, p ∉ K0 → N.factorization p = 2) :
    ∃ x, ∀ p ∈ N.primeFactors, p ∉ K0 → p % 3 = 1 → p = x := by
  set O1 := N.primeFactors.filter (fun p => p ∉ K0 ∧ p % 3 = 1) with hO1
  have hle := sum_padicValNat_sigma_le_factorization h.perfect Nat.prime_three (by norm_num)
    (insert y O1)
  have hyO : y ∉ O1 := fun hm => (Finset.mem_filter.mp hm).2.1 hyK
  rw [Finset.sum_insert hyO, h3, hy2, sigma_prime_sq hy, padicValNat_three_phi3,
    if_pos hy1] at hle
  have hc : ∑ p ∈ O1, padicValNat 3 (σ 1 (p ^ N.factorization p)) = O1.card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpN, hpK, hp1⟩ := Finset.mem_filter.mp hp
    rw [hord p hpN hpK, sigma_prime_sq (Nat.prime_of_mem_primeFactors hpN),
      padicValNat_three_phi3, if_pos hp1]
  have hcard : O1.card ≤ 1 := by omega
  rcases O1.eq_empty_or_nonempty with he | ⟨x, hx⟩
  · refine ⟨0, fun p hp hpK hp1 => ?_⟩
    have : p ∈ O1 := Finset.mem_filter.mpr ⟨hp, hpK, hp1⟩
    rw [he] at this
    exact absurd this (Finset.notMem_empty p)
  · exact ⟨x, fun p hp hpK hp1 =>
      Finset.card_le_one.mp hcard p (Finset.mem_filter.mpr ⟨hp, hpK, hp1⟩) x hx⟩

/-- Variant of `leaf_struct` with the residue condition given directly. -/
private theorem leaf_struct_of_key {N : ℕ} (h : OddPerfect N) (K : Finset ℕ)
    (hkey : ∀ s ∈ N.primeFactors, s ∉ K → s % 3 = 2)
    (hord : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2)
    {t : ℕ} (ht : t ∈ N.primeFactors) (htK : t ∉ K) :
    ∀ d, d.Prime → d ∣ phi3 t → d ∈ K ∧ d ≠ 3 := by
  intro d hd hdd
  have htp := Nat.prime_of_mem_primeFactors ht
  have ht2 := hkey t ht htK
  have hd3 : d ≠ 3 := by
    rintro rfl
    have := (three_dvd_phi3_iff t).1 hdd
    omega
  have hd1 := prime_dvd_phi3_mod_three hd hd3 hdd
  have hdN : d ∣ N := OPNStarter.force_prime h.perfect htp (hord t ht htK) hd
    (by rintro rfl; omega) (by rw [sigma_prime_sq htp]; exact hdd)
  refine ⟨?_, hd3⟩
  by_contra hdK
  have := hkey d (Nat.mem_primeFactors.mpr ⟨hd, hdN, h.ne_zero⟩) hdK
  omega

private theorem fval_le_of_large {s : ℕ} (hs : 10 ^ 12 ≤ s) : fval s ≤ 1 + 1 / 10 ^ 11 := by
  have h1 := fval_sub_le (s := s) (by omega)
  have hs' : (10 : ℚ) ^ 12 ≤ s := by exact_mod_cast hs
  have : 2 * (1 / ((s : ℚ) + 1)) ≤ 1 / 10 ^ 11 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

private theorem large_of_phi3 {x : ℕ} (h : 10 ^ 24 ≤ phi3 x) : 10 ^ 12 ≤ x := by
  by_contra hc
  rw [not_le] at hc
  have h1 : phi3 x < (x + 1) ^ 2 := phi3_lt_succ_sq (by
    by_contra h0; rw [not_le, Nat.lt_one_iff] at h0; subst h0; norm_num [phi3] at h)
  have h2 : (x + 1) ^ 2 ≤ (10 ^ 12) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

private theorem box_13_19_t : ∀ i < 2, ∀ j < 11, ∀ k < 10,
    7 ^ i * 13 ^ j * 19 ^ k < 10 ^ 12 →
      ok [0, 2, 3, 9, 11, 68, 653] (7 ^ i * 13 ^ j * 19 ^ k) = true := by
  decide +kernel

private theorem box_13_19_x : ∀ i < 2, ∀ j < 2, ∀ k < 22, ∀ l < 19,
    3 ^ i * 7 ^ j * 13 ^ k * 19 ^ l < 10 ^ 24 →
      ok [0, 1, 2, 3, 4, 7, 9, 11, 16, 22, 68, 653] (3 ^ i * 7 ^ j * 13 ^ k * 19 ^ l) = true := by
  decide +kernel

private theorem box_61_31_t : ∀ i < 2, ∀ j < 9, ∀ k < 7,
    13 ^ i * 31 ^ j * 61 ^ k < 10 ^ 12 →
      ok [0, 3, 5] (13 ^ i * 31 ^ j * 61 ^ k) = true := by
  decide +kernel

private theorem box_61_31_x : ∀ i < 2, ∀ j < 2, ∀ k < 17, ∀ l < 14,
    3 ^ i * 13 ^ j * 31 ^ k * 61 ^ l < 10 ^ 24 →
      ok [0, 1, 3, 5, 13] (3 ^ i * 13 ^ j * 31 ^ k * 61 ^ l) = true := by
  decide +kernel

/-- Leaf: `3^2, 13^2 ∥ N`, special prime `61`, exceptional prime `31`. -/
private theorem leaf_61_31 {N : ℕ} (h : OddPerfect N) (hodd : Odd (N.factorization 61))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 61 → p ≠ 31 → N.factorization p = 2)
    (h3 : 3 ∣ N) (h13 : 13 ∣ N) : False := by
  have e3 : N.factorization 3 = 2 :=
    hsq 3 (mem_pf h Nat.prime_three h3) (by norm_num) (by norm_num)
  have e13 : N.factorization 13 = 2 := hsq 13 (mem_pf h (by norm_num) h13) (by norm_num) (by norm_num)
  have h61 : 61 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have h31 : 31 ∣ N := OPNStarter.force_prime h.perfect (by norm_num : Nat.Prime 61) rfl
    (by norm_num) (by norm_num) ((by norm_num : 31 ∣ 61 + 1).trans
      (succ_dvd_sigma_special (by norm_num) hodd))
  have h31sq : 31 ^ 2 ∣ N := sq_dvd_of_ne_special h (by norm_num) hodd (by norm_num)
    (by norm_num) h31
  set K0 : Finset ℕ := {3, 13, 31, 61} with hK0
  have hK0sub : K0 ⊆ N.primeFactors := by
    intro p hp
    simp only [hK0, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_pf h (by norm_num) h3
    · exact mem_pf h (by norm_num) h13
    · exact mem_pf h (by norm_num) h31
    · exact mem_pf h (by norm_num) h61
  have hord0 : ∀ t ∈ N.primeFactors, t ∉ K0 → N.factorization t = 2 := fun t ht htK =>
    hsq t ht (fun e => htK (by simp [hK0, e])) (fun e => htK (by simp [hK0, e]))
  obtain ⟨x, hx⟩ := slot_le_one h e3 K0 (y := 13) (by norm_num) (by simp [hK0]) e13
    (by norm_num) hord0
  -- the 13-adic cap from `σ(3^2) = 13`
  have cap13 : ∀ t ∈ N.primeFactors, t ∉ K0 → padicValNat 13 (phi3 t) ≤ 1 := by
    intro t ht htK
    have hS1 : t ∉ ({3} : Finset ℕ) := fun hm => htK (by
      rw [Finset.mem_singleton] at hm; subst hm; simp [hK0])
    have c13 := cap_le h.perfect (x := 13) (by norm_num) (by norm_num) {3} hS1
      (Nat.prime_of_mem_primeFactors ht) (hord0 t ht htK)
    rw [Finset.sum_singleton, e3, e13] at c13
    have s1 : 1 ≤ padicValNat 13 (σ 1 (3 ^ 2)) := one_le_pv (by norm_num)
      (sigma_ne_zero' Nat.prime_three) (by rw [sigma_prime_sq Nat.prime_three]; decide)
    omega
  have core : ∀ (d : ℕ) (K : Finset ℕ), 10 ^ 12 ≤ d → K ⊆ N.primeFactors → K0 ⊆ K →
      (∀ p ∈ K, p ∉ K0 → p = d) → (∀ s ∈ N.primeFactors, s ∉ K → s % 3 = 2) → False := by
    intro d K hd hKsub hK0K hKd hkey
    have hdK0 : d ∉ K0 := by simp only [hK0, Finset.mem_insert, Finset.mem_singleton]; omega
    have hord : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2 := fun t ht htK =>
      hord0 t ht (fun hm => htK (hK0K hm))
    set c : ℕ → ℚ := fun p => if p ∈ K0 then cbound 61 31 p else 1 + 1 / 10 ^ 11 with hc
    have hd' : (10 : ℚ) ^ 12 ≤ d := by exact_mod_cast hd
    refine close_leaf h K hKsub c ?_ (a := 13) (b := 31) (c' := 61) (d := d) (B := 10 ^ 12)
      (α₁ := 53 / 100) (α₂ := 43 / 100) (α₃ := 9 / 25) (α₄ := 1 / 1000) (β := 1 / 1000)
      (by norm_num) (by norm_num) (by omega) (by norm_num) (by omega) (by omega)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num) ?_ ?_
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors (hKsub hp)
      by_cases hp0 : p ∈ K0
      · simp only [hc, if_pos hp0]
        exact abundancy_le_cbound hpp (hsq p (hKsub hp))
      · simp only [hc, if_neg hp0]
        have hpd := hKd p hp hp0
        rw [hord0 p (hKsub hp) hp0, abundancy_sq hpp]
        exact fval_le_of_large (hpd ▸ hd)
    · intro t ht htK
      have htp := Nat.prime_of_mem_primeFactors ht
      have ht2 := hord t ht htK
      have hdK := leaf_struct_of_key h K hkey hord ht htK
      have htK0 : t ∉ K0 := fun hm => htK (hK0K hm)
      have hsupp : (phi3 t).primeFactors ⊆ {13, 31, 61, d} := by
        intro e he
        obtain ⟨heK, he3⟩ := hdK e (Nat.prime_of_mem_primeFactors he)
          (Nat.dvd_of_mem_primeFactors he)
        by_cases he0 : e ∈ K0
        · simp only [hK0, Finset.mem_insert, Finset.mem_singleton] at he0 ⊢
          omega
        · have := hKd e heK he0
          simp [this]
      refine ⟨ht2, hsupp, ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      have hV0 : 0 < phi3 t := by unfold phi3; omega
      have hrep := eq_four_pow hV0.ne' (by norm_num) (by norm_num) (by omega) (by norm_num)
        (by omega) (by omega) hsupp
      have hc13 := cap13 t ht htK0
      have dv1 : d ^ (phi3 t).factorization d ∣ phi3 t := by
        conv_rhs => rw [hrep]
        exact Dvd.intro_left _ rfl
      have dv2 : 31 ^ (phi3 t).factorization 31 ∣ phi3 t := by
        conv_rhs => rw [hrep]
        exact ⟨13 ^ (phi3 t).factorization 13 * 61 ^ (phi3 t).factorization 61 *
          d ^ (phi3 t).factorization d, by ring⟩
      have dv3 : 61 ^ (phi3 t).factorization 61 ∣ phi3 t := by
        conv_rhs => rw [hrep]
        exact ⟨13 ^ (phi3 t).factorization 13 * 31 ^ (phi3 t).factorization 31 *
          d ^ (phi3 t).factorization d, by ring⟩
      have hl : (phi3 t).factorization d < 1 :=
        exp_lt_of_pow (by omega) hV0 dv1 hlt (by simpa using hd)
      have hj : (phi3 t).factorization 31 < 9 :=
        exp_lt_of_pow (by norm_num) hV0 dv2 hlt (by norm_num)
      have hk : (phi3 t).factorization 61 < 7 :=
        exp_lt_of_pow (by norm_num) hV0 dv3 hlt (by norm_num)
      have hl0 : (phi3 t).factorization d = 0 := by omega
      rw [hl0, pow_zero, mul_one] at hrep
      have hmem := ok_sound (box_61_31_t _ (by rw [Nat.factorization_def _ (by norm_num)]; omega)
        _ hj _ hk (hrep ▸ hlt)) hrep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact absurd htp (by norm_num)
      · exact htK0 (by simp [hK0])
      · have e5 := ht2
        exact Cert.check_sound
          (s := [.exact 3 2, .exact 5 2, .exact 13 2, .powDvd 31 2, .powDvd 61 1])
          (c := .abundant [(3, 2), (5, 2), (13, 2), (31, 2), (61, 1)]) (by decide +kernel) N h
          (by simp [Cert.State.Holds, Cert.Fact.Holds, e3, e5, e13, h61,
            show 961 ∣ N by simpa using h31sq])
    · have hsub : K ⊆ insert d K0 := fun p hp => by
        by_cases hp0 : p ∈ K0
        · exact Finset.mem_insert_of_mem hp0
        · rw [hKd p hp hp0]; exact Finset.mem_insert_self d K0
      have hcd : c d = 1 + 1 / 10 ^ 11 := by simp only [hc, if_neg hdK0]
      have hcK0 : ∏ p ∈ K0, c p = ∏ p ∈ K0, cbound 61 31 p :=
        Finset.prod_congr rfl fun p hp => by simp only [hc, if_pos hp]
      have hc0 : ∀ p ∈ insert d K0, 0 ≤ c p := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp0
        · rw [hcd]; norm_num
        · rw [show c p = cbound 61 31 p by simp only [hc, if_pos hp0]]
          simp only [hK0, Finset.mem_insert, Finset.mem_singleton] at hp0
          rcases hp0 with rfl | rfl | rfl | rfl <;> norm_num [cbound, fval]
      calc ∏ p ∈ K, c p ≤ ∏ p ∈ insert d K0, c p :=
            Finset.prod_le_prod_of_subset_of_one_le hsub (fun p hp => hc0 p (hsub hp)) (fun p hp hpK => by
              rcases Finset.mem_insert.mp hp with rfl | hp0
              · rw [hcd]; norm_num
              · exact absurd (hK0K hp0) hpK)
        _ = c d * ∏ p ∈ K0, cbound 61 31 p := by rw [Finset.prod_insert hdK0, hcK0]
        _ < _ := by
          rw [hcd, hK0, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
            Finset.prod_insert (by decide), Finset.prod_singleton]
          norm_num [cbound, fval]
  by_cases hxin : x ∈ N.primeFactors ∧ x ∉ K0 ∧ x % 3 = 1
  · obtain ⟨hxN, hxK0, hx1⟩ := hxin
    have hxp := Nat.prime_of_mem_primeFactors hxN
    have hx2 := hord0 x hxN hxK0
    have hbig : 10 ^ 24 ≤ phi3 x := by
      by_contra hlt
      rw [not_le] at hlt
      have hV0 : 0 < phi3 x := by unfold phi3; omega
      have hsupp : (phi3 x).primeFactors ⊆ {3, 13, 31, 61} := by
        intro e he
        have hep := Nat.prime_of_mem_primeFactors he
        have hed := Nat.dvd_of_mem_primeFactors he
        have heN : e ∣ N := OPNStarter.force_prime h.perfect hxp hx2 hep
          (by rintro rfl; exact absurd hed (by
            have := phi3_odd x; rw [Nat.odd_iff] at this; omega))
          (by rw [sigma_prime_sq hxp]; exact hed)
        have hex : e ≠ x := by
          rintro rfl
          have := Nat.Coprime.eq_one_of_dvd (phi3_coprime_self e).symm hed
          exact hep.one_lt.ne' this
        by_cases he3 : e = 3
        · simp [he3]
        have he1 := prime_dvd_phi3_mod_three hep he3 hed
        by_contra heK
        exact hex (hx e (mem_pf h hep heN) (by simpa [hK0] using heK) he1)
      have hrep := eq_four_pow hV0.ne' (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hsupp
      have hxS : x ∉ ({3} : Finset ℕ) := fun hm => hxK0 (by
        rw [Finset.mem_singleton] at hm; subst hm; simp [hK0])
      have c13 := cap13 x hxN hxK0
      have hmem := search (I := 2) (J := 2) (K := 17) (L := 14) (by norm_num) (by norm_num)
        box_61_31_x hrep (by rw [factorization_three_phi3]; split_ifs <;> omega)
        (by rw [Nat.factorization_def _ (by norm_num)]; omega) (by norm_num) (by norm_num) hlt
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl
      · exact absurd hxp (by norm_num)
      · exact absurd hxp (by norm_num)
      · exact hxK0 (by simp [hK0])
      · omega
      · exact hxK0 (by simp [hK0])
    refine core x (insert x K0) (large_of_phi3 hbig)
      (Finset.insert_subset hxN hK0sub) (Finset.subset_insert x K0) (fun p hp hp0 => ?_) ?_
    · rcases Finset.mem_insert.mp hp with rfl | h'
      · rfl
      · exact absurd h' hp0
    · intro s hs hsK
      have hsK0 : s ∉ K0 := fun hm => hsK (Finset.mem_insert_of_mem hm)
      have hsp := Nat.prime_of_mem_primeFactors hs
      have hs3 : s ≠ 3 := by rintro rfl; exact hsK0 (by simp [hK0])
      have : s % 3 ≠ 0 := fun h0 => hs3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hsp).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
      have : s % 3 ≠ 1 := fun h1 => hsK (by rw [hx s hs hsK0 h1]; exact Finset.mem_insert_self x K0)
      omega
  · refine core (10 ^ 12) K0 le_rfl hK0sub subset_rfl (fun p hp hp0 => absurd hp hp0) ?_
    intro s hs hsK0
    have hsp := Nat.prime_of_mem_primeFactors hs
    have hs3 : s ≠ 3 := by rintro rfl; exact hsK0 (by simp [hK0])
    have : s % 3 ≠ 0 := fun h0 => hs3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hsp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
    have : s % 3 ≠ 1 := fun h1 => by
      have := hx s hs hsK0 h1
      subst this
      exact hxin ⟨hs, hsK0, h1⟩
    omega

/-- Leaf: `3^2, 7^2 ∥ N`, special prime `13`, exceptional prime `19`. -/
private theorem leaf_13_19 {N : ℕ} (h : OddPerfect N) (hodd : Odd (N.factorization 13))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ 13 → p ≠ 19 → N.factorization p = 2)
    (h3 : 3 ∣ N) (h7 : 7 ∣ N) (h19 : 19 ∣ N) : False := by
  have e3 : N.factorization 3 = 2 :=
    hsq 3 (mem_pf h Nat.prime_three h3) (by norm_num) (by norm_num)
  have e7 : N.factorization 7 = 2 := hsq 7 (mem_pf h (by norm_num) h7) (by norm_num) (by norm_num)
  have h13 : 13 ∣ N := Nat.dvd_of_factorization_pos hodd.pos.ne'
  have h19sq : 19 ^ 2 ∣ N := sq_dvd_of_ne_special h (by norm_num) hodd (by norm_num)
    (by norm_num) h19
  set K0 : Finset ℕ := {3, 7, 13, 19} with hK0
  have hK0sub : K0 ⊆ N.primeFactors := by
    intro p hp
    simp only [hK0, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_pf h (by norm_num) h3
    · exact mem_pf h (by norm_num) h7
    · exact mem_pf h (by norm_num) h13
    · exact mem_pf h (by norm_num) h19
  have hord0 : ∀ t ∈ N.primeFactors, t ∉ K0 → N.factorization t = 2 := fun t ht htK =>
    hsq t ht (fun e => htK (by simp [hK0, e])) (fun e => htK (by simp [hK0, e]))
  obtain ⟨x, hx⟩ := slot_le_one h e3 K0 (y := 7) (by norm_num) (by simp [hK0]) e7
    (by norm_num) hord0
  -- the 7-adic cap from `14 ∣ σ(13^k)`
  have cap7 : ∀ t ∈ N.primeFactors, t ∉ K0 → padicValNat 7 (phi3 t) ≤ 1 := by
    intro t ht htK
    have hS1 : t ∉ ({13} : Finset ℕ) := fun hm => htK (by
      rw [Finset.mem_singleton] at hm; subst hm; simp [hK0])
    have c7 := cap_le h.perfect (x := 7) (by norm_num) (by norm_num) {13} hS1
      (Nat.prime_of_mem_primeFactors ht) (hord0 t ht htK)
    rw [Finset.sum_singleton, e7] at c7
    have s1 : 1 ≤ padicValNat 7 (σ 1 (13 ^ N.factorization 13)) := one_le_pv (by norm_num)
      (sigma_ne_zero' (by norm_num)) ((by norm_num : 7 ∣ 13 + 1).trans
        (succ_dvd_sigma_special (by norm_num) hodd))
    omega
  have core : ∀ (d : ℕ) (K : Finset ℕ), 10 ^ 12 ≤ d → K ⊆ N.primeFactors → K0 ⊆ K →
      (∀ p ∈ K, p ∉ K0 → p = d) → (∀ s ∈ N.primeFactors, s ∉ K → s % 3 = 2) → False := by
    intro d K hd hKsub hK0K hKd hkey
    have hdK0 : d ∉ K0 := by simp only [hK0, Finset.mem_insert, Finset.mem_singleton]; omega
    have hd653 : d ≠ 653 := by omega
    have hord : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2 := fun t ht htK =>
      hord0 t ht (fun hm => htK (hK0K hm))
    set c : ℕ → ℚ := fun p => if p ∈ K0 then cbound 13 19 p else
      if p = 653 then fval 653 else 1 + 1 / 10 ^ 11 with hc
    have hd' : (10 : ℚ) ^ 12 ≤ d := by exact_mod_cast hd
    have hT0 : ∀ t ∈ N.primeFactors, t ∉ K → N.factorization t = 2 ∧
        (phi3 t).primeFactors ⊆ {7, 13, 19, d} ∧ (10 ^ 12 ≤ phi3 t ∨ t = 653) := by
      intro t ht htK
      have htp := Nat.prime_of_mem_primeFactors ht
      have ht2 := hord t ht htK
      have hdK := leaf_struct_of_key h K hkey hord ht htK
      have htK0 : t ∉ K0 := fun hm => htK (hK0K hm)
      have hsupp : (phi3 t).primeFactors ⊆ {7, 13, 19, d} := by
        intro e he
        obtain ⟨heK, he3⟩ := hdK e (Nat.prime_of_mem_primeFactors he)
          (Nat.dvd_of_mem_primeFactors he)
        by_cases he0 : e ∈ K0
        · simp only [hK0, Finset.mem_insert, Finset.mem_singleton] at he0 ⊢
          omega
        · have := hKd e heK he0
          simp [this]
      refine ⟨ht2, hsupp, ?_⟩
      by_contra hlt
      rw [not_or, not_le] at hlt
      have hV0 : 0 < phi3 t := by unfold phi3; omega
      have hrep := eq_four_pow hV0.ne' (by norm_num) (by norm_num) (by omega) (by norm_num)
        (by omega) (by omega) hsupp
      have hc7 := cap7 t ht htK0
      have dv1 : d ^ (phi3 t).factorization d ∣ phi3 t := by
        conv_rhs => rw [hrep]
        exact Dvd.intro_left _ rfl
      have dv2 : 13 ^ (phi3 t).factorization 13 ∣ phi3 t := by
        conv_rhs => rw [hrep]
        exact ⟨7 ^ (phi3 t).factorization 7 * 19 ^ (phi3 t).factorization 19 *
          d ^ (phi3 t).factorization d, by ring⟩
      have dv3 : 19 ^ (phi3 t).factorization 19 ∣ phi3 t := by
        conv_rhs => rw [hrep]
        exact ⟨7 ^ (phi3 t).factorization 7 * 13 ^ (phi3 t).factorization 13 *
          d ^ (phi3 t).factorization d, by ring⟩
      have hl : (phi3 t).factorization d < 1 :=
        exp_lt_of_pow (by omega) hV0 dv1 hlt.1 (by simpa using hd)
      have hj : (phi3 t).factorization 13 < 11 :=
        exp_lt_of_pow (by norm_num) hV0 dv2 hlt.1 (by norm_num)
      have hk : (phi3 t).factorization 19 < 10 :=
        exp_lt_of_pow (by norm_num) hV0 dv3 hlt.1 (by norm_num)
      have hl0 : (phi3 t).factorization d = 0 := by omega
      rw [hl0, pow_zero, mul_one] at hrep
      have hmem := ok_sound (box_13_19_t _ (by rw [Nat.factorization_def _ (by norm_num)]; omega)
        _ hj _ hk (hrep ▸ hlt.1)) hrep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd htp (by norm_num)
      · exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors ht)
      · exact htK0 (by simp [hK0])
      · exact absurd htp (by norm_num)
      · have e11 := ht2
        exact Cert.check_sound
          (s := [.exact 3 2, .exact 7 2, .exact 11 2, .powDvd 19 2, .powDvd 13 1])
          (c := .abundant [(3, 2), (7, 2), (11, 2), (19, 2), (13, 1)]) (by decide +kernel) N h
          (by simp [Cert.State.Holds, Cert.Fact.Holds, e3, e7, e11, h13,
            show 361 ∣ N by simpa using h19sq])
      · exact absurd htp (by norm_num)
      · exact hlt.2 rfl
    have hC : ∀ p ∈ insert 653 K, p ∈ N.primeFactors →
        abundancy (p ^ N.factorization p) ≤ c p := by
      intro p hp hpN
      have hpp := Nat.prime_of_mem_primeFactors hpN
      by_cases hp0 : p ∈ K0
      · simp only [hc, if_pos hp0]
        exact abundancy_le_cbound hpp (hsq p hpN)
      · rw [hord0 p hpN hp0, abundancy_sq hpp]
        by_cases hp6 : p = 653
        · subst hp6; simp only [hc, if_neg hp0, if_pos rfl]; exact le_rfl
        · simp only [hc, if_neg hp0, if_neg hp6]
          rcases Finset.mem_insert.mp hp with h' | h'
          · exact absurd h' hp6
          · exact fval_le_of_large (hKd p h' hp0 ▸ hd)
    have hc1 : ∀ p ∉ K0, 1 ≤ c p := by
      intro p hp0
      by_cases hp6 : p = 653
      · subst hp6; simp only [hc, if_neg hp0, if_pos rfl]; norm_num [fval]
      · simp only [hc, if_neg hp0, if_neg hp6]; norm_num
    have hfinal : ∀ K' : Finset ℕ, K' ⊆ insert 653 (insert d K0) → K0 ⊆ K' →
        ∏ p ∈ K', c p < 2 * (1 - 2 * (1 / 1000 * (1 / (1 - 13 / 20) * (1 / (1 - 53 / 100)) *
          (1 / (1 - 12 / 25)) * (1 / (1 - 1 / 1000))))) := by
      intro K' hsub hK0K'
      have h653 : (653 : ℕ) ∉ insert d K0 := by
        simp only [hK0, Finset.mem_insert, Finset.mem_singleton]; omega
      have hcK0 : ∏ p ∈ K0, c p = ∏ p ∈ K0, cbound 13 19 p :=
        Finset.prod_congr rfl fun p hp => by simp only [hc, if_pos hp]
      have hc0 : ∀ p ∈ insert 653 (insert d K0), 0 ≤ c p := by
        intro p hp
        by_cases hp0 : p ∈ K0
        · rw [show c p = cbound 13 19 p by simp only [hc, if_pos hp0]]
          simp only [hK0, Finset.mem_insert, Finset.mem_singleton] at hp0
          rcases hp0 with rfl | rfl | rfl | rfl <;> norm_num [cbound, fval]
        · exact le_trans zero_le_one (hc1 p hp0)
      calc ∏ p ∈ K', c p ≤ ∏ p ∈ insert 653 (insert d K0), c p :=
            Finset.prod_le_prod_of_subset_of_one_le hsub (fun p hp => hc0 p (hsub hp)) (fun p _ hpK =>
              hc1 p (fun hm => hpK (hK0K' hm)))
        _ = c 653 * (c d * ∏ p ∈ K0, cbound 13 19 p) := by
            rw [Finset.prod_insert h653, Finset.prod_insert hdK0, hcK0]
        _ < _ := by
          rw [show c 653 = fval 653 by simp only [hc]; norm_num [hK0],
            show c d = 1 + 1 / 10 ^ 11 by simp only [hc, if_neg hdK0, if_neg hd653],
            hK0, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
            Finset.prod_insert (by decide), Finset.prod_singleton]
          norm_num [cbound, fval]
    have hsubK : K ⊆ insert 653 (insert d K0) := fun p hp => by
      by_cases hp0 : p ∈ K0
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp0)
      · rw [hKd p hp hp0]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self d K0)
    by_cases h653 : 653 ∣ N
    · have hK' : insert 653 K ⊆ N.primeFactors :=
        Finset.insert_subset (mem_pf h (by norm_num) h653) hKsub
      refine close_leaf h (insert 653 K) hK' c (fun p hp => hC p hp (hK' hp))
        (a := 7) (b := 13) (c' := 19) (d := d) (B := 10 ^ 12)
        (α₁ := 13 / 20) (α₂ := 53 / 100) (α₃ := 12 / 25) (α₄ := 1 / 1000) (β := 1 / 1000)
        (by norm_num) (by norm_num) (by omega) (by norm_num) (by omega) (by omega)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num) ?_
        (hfinal _ (Finset.insert_subset (Finset.mem_insert_self _ _) hsubK)
          (fun p hp => Finset.mem_insert_of_mem (hK0K hp)))
      intro t ht htK
      have htK1 : t ∉ K := fun hm => htK (Finset.mem_insert_of_mem hm)
      have ht653 : t ≠ 653 := fun e => htK (e ▸ Finset.mem_insert_self 653 K)
      obtain ⟨a1, a2, a3⟩ := hT0 t ht htK1
      exact ⟨a1, a2, a3.resolve_right ht653⟩
    · refine close_leaf h K hKsub c (fun p hp => hC p (Finset.mem_insert_of_mem hp) (hKsub hp))
        (a := 7) (b := 13) (c' := 19) (d := d) (B := 10 ^ 12)
        (α₁ := 13 / 20) (α₂ := 53 / 100) (α₃ := 12 / 25) (α₄ := 1 / 1000) (β := 1 / 1000)
        (by norm_num) (by norm_num) (by omega) (by norm_num) (by omega) (by omega)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num) ?_
        (hfinal K hsubK hK0K)
      intro t ht htK
      obtain ⟨a1, a2, a3⟩ := hT0 t ht htK
      refine ⟨a1, a2, a3.resolve_right ?_⟩
      rintro rfl
      exact h653 (Nat.dvd_of_mem_primeFactors ht)
  by_cases hxin : x ∈ N.primeFactors ∧ x ∉ K0 ∧ x % 3 = 1
  · obtain ⟨hxN, hxK0, hx1⟩ := hxin
    have hxp := Nat.prime_of_mem_primeFactors hxN
    have hx2 := hord0 x hxN hxK0
    have hbig : 10 ^ 24 ≤ phi3 x := by
      by_contra hlt
      rw [not_le] at hlt
      have hV0 : 0 < phi3 x := by unfold phi3; omega
      have hsupp : (phi3 x).primeFactors ⊆ {3, 7, 13, 19} := by
        intro e he
        have hep := Nat.prime_of_mem_primeFactors he
        have hed := Nat.dvd_of_mem_primeFactors he
        have heN : e ∣ N := OPNStarter.force_prime h.perfect hxp hx2 hep
          (by rintro rfl; exact absurd hed (by
            have := phi3_odd x; rw [Nat.odd_iff] at this; omega))
          (by rw [sigma_prime_sq hxp]; exact hed)
        have hex : e ≠ x := by
          rintro rfl
          have := Nat.Coprime.eq_one_of_dvd (phi3_coprime_self e).symm hed
          exact hep.one_lt.ne' this
        by_cases he3 : e = 3
        · simp [he3]
        have he1 := prime_dvd_phi3_mod_three hep he3 hed
        by_contra heK
        exact hex (hx e (mem_pf h hep heN) (by simpa [hK0] using heK) he1)
      have hrep := eq_four_pow hV0.ne' (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hsupp
      have c7 := cap7 x hxN hxK0
      have hmem := search (I := 2) (J := 2) (K := 22) (L := 19) (by norm_num) (by norm_num)
        box_13_19_x hrep (by rw [factorization_three_phi3]; split_ifs <;> omega)
        (by rw [Nat.factorization_def _ (by norm_num)]; omega) (by norm_num) (by norm_num) hlt
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (omega)
        | (exact absurd hxp (by decide))
        | (apply hxK0; simp [hK0])
    refine core x (insert x K0) (large_of_phi3 hbig)
      (Finset.insert_subset hxN hK0sub) (Finset.subset_insert x K0) (fun p hp hp0 => ?_) ?_
    · rcases Finset.mem_insert.mp hp with rfl | h'
      · rfl
      · exact absurd h' hp0
    · intro s hs hsK
      have hsK0 : s ∉ K0 := fun hm => hsK (Finset.mem_insert_of_mem hm)
      have hsp := Nat.prime_of_mem_primeFactors hs
      have hs3 : s ≠ 3 := by rintro rfl; exact hsK0 (by simp [hK0])
      have : s % 3 ≠ 0 := fun h0 => hs3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hsp).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
      have : s % 3 ≠ 1 := fun h1 => hsK (by rw [hx s hs hsK0 h1]; exact Finset.mem_insert_self x K0)
      omega
  · refine core (10 ^ 12) K0 le_rfl hK0sub subset_rfl (fun p hp hp0 => absurd hp hp0) ?_
    intro s hs hsK0
    have hsp := Nat.prime_of_mem_primeFactors hs
    have hs3 : s ≠ 3 := by rintro rfl; exact hsK0 (by simp [hK0])
    have : s % 3 ≠ 0 := fun h0 => hs3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hsp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
    have : s % 3 ≠ 1 := fun h1 => by
      have := hx s hs hsK0 h1
      subst this
      exact hxin ⟨hs, hsK0, h1⟩
    omega

/-- With exceptional prime `3`, `7 ∤ N`: the chain `7 → 19 → 127 → 5419 → {31, 313, 1009}`,
`31 → 331 → 7`, then a split on whether `313` or `181` is the special prime. -/
private theorem not_seven_of_exception_three {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → N.factorization p = 2)
    (h4 : 4 ≤ N.factorization 3) : ¬ 7 ∣ N := by
  intro h7
  have hq4 := (special_mod_four h hq hodd).1
  have ne4 : ∀ {p : ℕ}, p % 4 = 3 → p ≠ q := fun hp e => by rw [e] at hp; omega
  have frc : ∀ {p t : ℕ}, p.Prime → N.factorization p = 2 → t.Prime → t ≠ 2 →
      t ∣ phi3 p → t ∣ N := fun hp he ht ht2 hd =>
    OPNStarter.force_prime h.perfect hp he ht ht2 (by rw [sigma_prime_sq hp]; exact hd)
  have e7 := hsq 7 (mem_pf h (by norm_num) h7) (ne4 (by norm_num)) (by norm_num)
  have d19 := frc (t := 19) (by norm_num) e7 (by norm_num) (by norm_num) (by decide)
  have e19 := hsq 19 (mem_pf h (by norm_num) d19) (ne4 (by norm_num)) (by norm_num)
  have d127 := frc (t := 127) (by norm_num) e19 (by norm_num) (by norm_num) (by decide)
  have e127 := hsq 127 (mem_pf h (by norm_num) d127) (ne4 (by norm_num)) (by norm_num)
  have d5419 := frc (t := 5419) (by norm_num) e127 (by norm_num) (by norm_num) (by decide)
  have e5419 := hsq 5419 (mem_pf h (by norm_num) d5419) (ne4 (by norm_num)) (by norm_num)
  have d31 := frc (t := 31) (by norm_num) e5419 (by norm_num) (by norm_num) (by decide)
  have d313 := frc (t := 313) (by norm_num) e5419 (by norm_num) (by norm_num) (by decide)
  have d1009 := frc (t := 1009) (by norm_num) e5419 (by norm_num) (by norm_num) (by decide)
  have e31 := hsq 31 (mem_pf h (by norm_num) d31) (ne4 (by norm_num)) (by norm_num)
  have d331 := frc (t := 331) (by norm_num) e31 (by norm_num) (by norm_num) (by decide)
  have e331 := hsq 331 (mem_pf h (by norm_num) d331) (ne4 (by norm_num)) (by norm_num)
  by_cases h313 : 313 = q
  · subst h313
    have e1009 := hsq 1009 (mem_pf h (by norm_num) d1009) (by norm_num) (by norm_num)
    have d37 := frc (t := 37) (by norm_num) e1009 (by norm_num) (by norm_num) (by decide)
    have e37 := hsq 37 (mem_pf h (by norm_num) d37) (by norm_num) (by norm_num)
    have d67 := frc (t := 67) (by norm_num) e37 (by norm_num) (by norm_num) (by decide)
    have e67 := hsq 67 (mem_pf h (by norm_num) d67) (by norm_num) (by norm_num)
    exact Cert.check_sound (s := [.exact 7 2, .exact 331 2, .exact 37 2, .exact 67 2])
      (c := .overflow 7 2 [(331, 2, 1), (37, 2, 1), (67, 2, 2)]) (by decide +kernel) N h
      (by simp [Cert.State.Holds, Cert.Fact.Holds, e7, e331, e37, e67])
  · have e313 := hsq 313 (mem_pf h (by norm_num) d313) h313
      (by norm_num)
    have d181 := frc (t := 181) (by norm_num) e313 (by norm_num) (by norm_num) (by decide)
    by_cases h181 : 181 = q
    · subst h181
      have d13 : 13 ∣ N := OPNStarter.force_prime h.perfect hq rfl (by norm_num) (by norm_num)
        ((by norm_num : 13 ∣ 181 + 1).trans (succ_dvd_sigma_special hq hodd))
      have e13 := hsq 13 (mem_pf h (by norm_num) d13) (by norm_num) (by norm_num)
      have h34 : 3 ^ 4 ∣ N := (Nat.prime_three.pow_dvd_iff_le_factorization h.ne_zero).mpr h4
      have h81 : 81 ∣ N := by simpa using h34
      exact Cert.check_sound
        (s := [.powDvd 3 4, .exact 7 2, .exact 19 2, .exact 31 2, .exact 13 2])
        (c := .abundant [(3, 4), (7, 2), (19, 2), (31, 2), (13, 2)]) (by decide +kernel) N h
        (by simp [Cert.State.Holds, Cert.Fact.Holds, h81, e7, e19, e31, e13])
    · have e181 := hsq 181 (mem_pf h (by norm_num) d181) h181
        (by norm_num)
      have d79 := frc (t := 79) (by norm_num) e181 (by norm_num) (by norm_num) (by decide)
      have e79 := hsq 79 (mem_pf h (by norm_num) d79) (ne4 (by norm_num)) (by norm_num)
      exact Cert.check_sound (s := [.exact 7 2, .exact 331 2, .exact 79 2])
        (c := .overflow 7 2 [(331, 2, 1), (79, 2, 2)]) (by decide +kernel) N h
        (by simp [Cert.State.Holds, Cert.Fact.Holds, e7, e331, e79])

end Restrained

open Restrained

/-- **Restrained, `3` ordinary.** Let `N` be an odd perfect number with special prime `q`,
let `r ≠ q` be a prime, and suppose every prime factor other than `q` and `r` has exponent
exactly 2. If moreover `3^2 ∥ N`, then the pair `(q, r)` is one of four configurations. -/
theorem restrained_three_sq_cases {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (h3 : N.factorization 3 = 2) :
    r = 13 ∨ (q = 13 ∧ r = 7) ∨ (r = 61 ∧ N.factorization 13 = 2) ∨
      (r = 97 ∧ N.factorization 13 = 2 ∧ N.factorization 61 = 2) := by
  have h3N : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have ord : ∀ {p}, p.Prime → p ∣ N → p ≠ q → p ≠ r → N.factorization p = 2 :=
    fun hp hd h1 h2 => hsq _ (mem_pf h hp hd) h1 h2
  have force2 : ∀ {p t}, p.Prime → N.factorization p = 2 → t.Prime → t ≠ 2 → t ∣ phi3 p →
      t ∣ N := fun hp he ht ht2 hd =>
    OPNStarter.force_prime h.perfect hp he ht ht2 (by rw [sigma_prime_sq hp]; exact hd)
  have forceq : ∀ {t}, t.Prime → t ≠ 2 → t ∣ q + 1 → t ∣ N := fun ht ht2 hd =>
    OPNStarter.force_prime h.perfect hq rfl ht ht2 (hd.trans (succ_dvd_sigma_special hq hodd))
  have d13 : 13 ∣ N := force2 Nat.prime_three h3 (by norm_num) (by norm_num) (by decide)
  by_cases hr13 : r = 13
  · exact Or.inl hr13
  by_cases hq13 : q = 13
  · subst hq13
    have d7 : 7 ∣ N := forceq (by norm_num) (by norm_num) (by norm_num)
    by_cases hr7 : r = 7
    · exact Or.inr (Or.inl ⟨rfl, hr7⟩)
    have e7 := ord (by norm_num) d7 (by norm_num) (Ne.symm hr7)
    have d19 : 19 ∣ N := force2 (by norm_num) e7 (by norm_num) (by norm_num) (by decide)
    by_cases hr19 : r = 19
    · subst hr19
      exact (leaf_13_19 h hodd hsq h3N d7 d19).elim
    have e19 := ord (by norm_num) d19 (by norm_num) (Ne.symm hr19)
    have d127 : 127 ∣ N := force2 (by norm_num) e19 (by norm_num) (by norm_num) (by decide)
    by_cases hr127 : r = 127
    · subst hr127
      exact (leaf_13_127 h hodd hsq h3N d7 d19 d127).elim
    have e127 := ord (by norm_num) d127 (by norm_num) (Ne.symm hr127)
    exact (three_sq_overflow h h3 (p₁ := 7) (p₂ := 19) (p₃ := 127) (by norm_num)
      (by norm_num) (by norm_num) e7 e19 e127 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).elim
  have e13 := ord (by norm_num) d13 (Ne.symm hq13) (Ne.symm hr13)
  have d61 : 61 ∣ N := force2 (by norm_num) e13 (by norm_num) (by norm_num) (by decide)
  by_cases hr61 : r = 61
  · exact Or.inr (Or.inr (Or.inl ⟨hr61, e13⟩))
  by_cases hq61 : q = 61
  · subst hq61
    have d31 : 31 ∣ N := forceq (by norm_num) (by norm_num) (by norm_num)
    by_cases hr31 : r = 31
    · subst hr31
      exact (leaf_61_31 h hodd hsq h3N d13).elim
    have e31 := ord (by norm_num) d31 (by norm_num) (Ne.symm hr31)
    have d331 : 331 ∣ N := force2 (by norm_num) e31 (by norm_num) (by norm_num) (by decide)
    by_cases hr331 : r = 331
    · subst hr331
      exact (leaf_61_331 h hodd hsq h3N d13 d31 d331).elim
    have e331 := ord (by norm_num) d331 (by norm_num) (Ne.symm hr331)
    exact (three_sq_overflow h h3 (p₁ := 13) (p₂ := 31) (p₃ := 331) (by norm_num)
      (by norm_num) (by norm_num) e13 e31 e331 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).elim
  have e61 := ord (by norm_num) d61 (Ne.symm hq61) (Ne.symm hr61)
  have d97 : 97 ∣ N := force2 (by norm_num) e61 (by norm_num) (by norm_num) (by decide)
  by_cases hr97 : r = 97
  · exact Or.inr (Or.inr (Or.inr ⟨hr97, e13, e61⟩))
  by_cases hq97 : q = 97
  · subst hq97
    have d7 : 7 ∣ N := forceq (by norm_num) (by norm_num) (by norm_num)
    by_cases hr7 : r = 7
    · subst hr7
      exact (leaf_97_7 h hodd hsq h3N d13 d61).elim
    have e7 := ord (by norm_num) d7 (by norm_num) (Ne.symm hr7)
    exact (three_sq_overflow h h3 (p₁ := 13) (p₂ := 61) (p₃ := 7) (by norm_num)
      (by norm_num) (by norm_num) e13 e61 e7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).elim
  have e97 := ord (by norm_num) d97 (Ne.symm hq97) (Ne.symm hr97)
  exact (three_sq_overflow h h3 (p₁ := 13) (p₂ := 61) (p₃ := 97) (by norm_num)
    (by norm_num) (by norm_num) e13 e61 e97 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).elim

/-- **Restrained, `r = 3`.** If the exceptional prime is `3`, then `v_3(N)` is even and at
least `4`, the special prime is `1 (mod 3)`, `5 ∤ N` and `7 ∤ N`. -/
theorem restrained_exception_three {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → N.factorization p = 2) :
    4 ≤ N.factorization 3 ∧ Even (N.factorization 3) ∧ q % 3 = 1 ∧ ¬ 5 ∣ N ∧ ¬ 7 ∣ N := by
  have hq4 := (special_mod_four h hq hodd).1
  have hq3 : (3 : ℕ) ≠ q := by rintro rfl; norm_num at hq4
  have h3N : 3 ∣ N := three_dvd_of_one_exception h hq hodd Nat.prime_three hq3 hsq
  have hev : Even (N.factorization 3) :=
    even_factorization_of_ne h hq hodd Nat.prime_three hq3
  have hne2 : N.factorization 3 ≠ 2 := by
    intro h2
    exact steuerwald h hq hodd fun p hp hpq => by
      by_cases hp3 : p = 3
      · subst hp3; exact h2
      · exact hsq p hp hpq hp3
  have hpos : 1 ≤ N.factorization 3 :=
    (Nat.prime_three.dvd_iff_one_le_factorization h.ne_zero).mp h3N
  have h4 : 4 ≤ N.factorization 3 := by obtain ⟨j, hj⟩ := hev; omega
  have hqmod : q % 3 = 1 := by
    by_contra hc
    have hq2 : q % 3 = 2 := by
      have : q % 3 ≠ 0 := fun h0 =>
        hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp (Nat.dvd_of_mod_eq_zero h0))
      omega
    have hbal := factorization_eq_sum_erase h.perfect hq (by omega : q ≠ 2)
    have hzero : ∀ p ∈ N.primeFactors.erase q, p ≠ 3 →
        padicValNat q (σ 1 (p ^ N.factorization p)) = 0 := by
      intro p hp hp3
      obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hpN
      rw [hsq p hpN hpq hp3, sigma_prime_sq hpp]
      refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
      have := prime_dvd_phi3_mod_three hq (Ne.symm hq3) hd
      omega
    have h3d : q ∣ σ 1 (3 ^ N.factorization 3) := by
      by_contra hnd
      have h0 : padicValNat q (σ 1 (3 ^ N.factorization 3)) = 0 :=
        padicValNat.eq_zero_of_not_dvd hnd
      have hs : ∑ p ∈ N.primeFactors.erase q, padicValNat q (σ 1 (p ^ N.factorization p)) =
          0 := Finset.sum_eq_zero fun p hp => by
        by_cases hp3 : p = 3
        · subst hp3; exact h0
        · exact hzero p hp hp3
      have := hodd.pos
      omega
    have := Fact.mk hq
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hL := legendreSym_eq_one_of_dvd_sigma_even (r := q) Nat.prime_three hev h3d
    have hqr := legendreSym.quadratic_reciprocity_one_mod_four (p := q) (q := 3) hq4
      (by norm_num)
    rw [← hqr, legendreSym.mod 3 (q : ℤ)] at hL
    have hm : (q : ℤ) % ((3 : ℕ) : ℤ) = 2 := by push_cast; omega
    rw [hm, legendreSym.at_two (by norm_num), ZMod.χ₈_nat_eq_if_mod_eight] at hL
    norm_num at hL
  refine ⟨h4, hev, hqmod, fun h5 => ?_, not_seven_of_exception_three h hq hodd hsq h4⟩
  have ne4 : ∀ {p : ℕ}, p % 4 = 3 → p ≠ q := fun hp e => by rw [e] at hp; omega
  have e5 : N.factorization 5 = 2 := hsq 5 (mem_pf h (by norm_num) h5)
    (fun e => by rw [← e] at hqmod; norm_num at hqmod) (by norm_num)
  have d31 : 31 ∣ N := OPNStarter.force_prime h.perfect (by norm_num) e5 (by norm_num)
    (by norm_num) (by rw [sigma_prime_sq (by norm_num)]; decide)
  have e31 : N.factorization 31 = 2 :=
    hsq 31 (mem_pf h (by norm_num) d31) (ne4 (by norm_num)) (by norm_num)
  have d331 : 331 ∣ N := OPNStarter.force_prime h.perfect (by norm_num) e31 (by norm_num)
    (by norm_num) (by rw [sigma_prime_sq (by norm_num)]; decide)
  have e331 : N.factorization 331 = 2 :=
    hsq 331 (mem_pf h (by norm_num) d331) (ne4 (by norm_num)) (by norm_num)
  have d7 : 7 ∣ N := OPNStarter.force_prime h.perfect (by norm_num) e331 (by norm_num)
    (by norm_num) (by rw [sigma_prime_sq (by norm_num)]; decide)
  have e7 : N.factorization 7 = 2 :=
    hsq 7 (mem_pf h (by norm_num) d7) (ne4 (by norm_num)) (by norm_num)
  have h34 : 3 ^ 4 ∣ N := (Nat.prime_three.pow_dvd_iff_le_factorization h.ne_zero).mpr h4
  have h81 : 81 ∣ N := by simpa using h34
  exact Cert.check_sound (s := [.powDvd 3 4, .exact 5 2, .exact 7 2])
    (c := .abundant [(3, 4), (5, 2), (7, 2)]) (by decide +kernel) N h
    (by simp [Cert.State.Holds, Cert.Fact.Holds, h81, e5, e7])

/-- **Restrained odd perfect numbers.** With the hypotheses of `three_dvd_of_one_exception`,
either the exceptional prime is `3` (with `v_3(N)` even, at least `4`, `q ≡ 1 (mod 3)`,
`5 ∤ N` and `7 ∤ N`), or `3^2 ∥ N` and `(q, r)` is one of the four configurations of
`restrained_three_sq_cases`. -/
theorem restrained_cases {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (r = 3 ∧ 4 ≤ N.factorization 3 ∧ Even (N.factorization 3) ∧ q % 3 = 1 ∧ ¬ 5 ∣ N ∧
      ¬ 7 ∣ N) ∨
    (N.factorization 3 = 2 ∧ (r = 13 ∨ (q = 13 ∧ r = 7) ∨
      (r = 61 ∧ N.factorization 13 = 2) ∨
      (r = 97 ∧ N.factorization 13 = 2 ∧ N.factorization 61 = 2))) := by
  by_cases hr3 : r = 3
  · subst hr3
    exact Or.inl ⟨rfl, restrained_exception_three h hq hodd hsq⟩
  · have hq4 := (special_mod_four h hq hodd).1
    have hq3 : (3 : ℕ) ≠ q := by rintro rfl; norm_num at hq4
    have h3N := three_dvd_of_one_exception h hq hodd hr hrq hsq
    have h3 := hsq 3 (mem_pf h Nat.prime_three h3N) hq3 (Ne.symm hr3)
    exact Or.inr ⟨h3, restrained_three_sq_cases h hq hodd hr hrq hsq h3⟩

end OddPerfect

#print axioms OddPerfect.restrained_three_sq_cases
#print axioms OddPerfect.restrained_exception_three
#print axioms OddPerfect.restrained_cases
