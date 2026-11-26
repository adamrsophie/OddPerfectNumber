import OddPerfect.RestrainedFour

/-!
# A general Rankin tail bound

Let `T` be a finite set of numbers `t ≥ x ≥ 2` such that every prime factor of
`phi3 t = t^2 + t + 1` lies in `K ∪ U`. Here `K` is a finite set of known generators with
weights `α g` satisfying `α g ^ k * g ≥ 1`, and `U` is a set of at most `u` unknown generators,
each at least `x`, all sharing one weight `αx` with `αx ^ k * x ≥ 1`. When no element of `U`
divides `phi3 t`, the row satisfies `phi3 t ≥ M`.

`rankin_tail_general` bounds `∑ (σ(t^2)/t^2 - 1)` over `T` by Rankin's trick with exponent `1/k`:
the rows divisible by an element of `U` are weighted with `mL`, a rational with
`mL^(2k) (x^2 + x + 1)^(k - 2) ≥ 1`, and the other rows with `mM`, where
`mM^(2k) M^(k - 2) ≥ 1`. `prod_fv_le_of_rankin_tail_general` gives the product form
`∏ σ(t^2)/t^2 ≤ 1/(1 - S)`, and `rankin_tail_general_example` is a numerical instance.

These are tool lemmas. They make no claim about odd perfect numbers by themselves.
-/

namespace OddPerfect

open RestrainedFour (fv)

namespace RankinTailGeneral

/-- `σ(t^2)/t^2 - 1 = (t + 1)/t^2` is at most `((x + 1)/x)^2/(t + 1)` once `t ≥ x ≥ 1`. -/
private theorem fv_sub_le_gen {x t : ℕ} (hx : 1 ≤ x) (hxt : x ≤ t) :
    fv t - 1 ≤ ((x + 1 : ℚ) / x) ^ 2 * (1 / ((t : ℚ) + 1)) := by
  have hx' : (1 : ℚ) ≤ x := by exact_mod_cast hx
  have hxt' : (x : ℚ) ≤ t := by exact_mod_cast hxt
  have ht0 : (0 : ℚ) < t := by linarith
  unfold fv
  rw [div_sub_one (pow_pos ht0 2).ne', div_pow, mul_one_div, div_div,
    div_le_div_iff₀ (pow_pos ht0 2) (by positivity)]
  have h : (x : ℚ) * (t + 1) ≤ t * (x + 1) := by nlinarith
  nlinarith [mul_le_mul h h (by positivity) (by positivity)]

private theorem fv_sub_one_nonneg {t : ℕ} (ht : 1 ≤ t) : 0 ≤ fv t - 1 := by
  have ht0 : (0 : ℚ) < t := by exact_mod_cast ht
  unfold fv
  rw [div_sub_one (pow_pos ht0 2).ne']
  have : (t : ℚ) ^ 2 + t + 1 - t ^ 2 = t + 1 := by ring
  rw [this]
  positivity

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

/-- Rankin step with exponent `1/k`, `k = j + 2`: if `B ≤ n < (t + 1)^2`, `w^k n ≥ 1` and
`m^(2k) B^(k - 2) ≥ 1`, then `1/(t + 1) ≤ m w`. -/
private theorem rankin_step {t n B j : ℕ} {m w : ℚ} (hm : 0 ≤ m) (hw : 0 ≤ w)
    (hwn : 1 ≤ w ^ (j + 2) * n) (hmB : 1 ≤ m ^ (2 * (j + 2)) * (B : ℚ) ^ j)
    (hB : B ≤ n) (hn : n < (t + 1) ^ 2) : 1 / ((t : ℚ) + 1) ≤ m * w := by
  have hBn : (B : ℚ) ≤ n := by exact_mod_cast hB
  have hnt : (n : ℚ) < ((t : ℚ) + 1) ^ 2 := by exact_mod_cast hn
  have hn0 : (0 : ℚ) ≤ n := by positivity
  have hB0 : (0 : ℚ) ≤ B := by positivity
  have ht0 : (0 : ℚ) < (t : ℚ) + 1 := by positivity
  have hm2 : 0 ≤ m ^ (2 * (j + 2)) := by positivity
  have key : 1 ≤ (m * w * ((t : ℚ) + 1)) ^ (2 * (j + 2)) := by
    have e1 : (m * w * ((t : ℚ) + 1)) ^ (2 * (j + 2)) =
        m ^ (2 * (j + 2)) * ((w ^ (j + 2)) ^ 2 * (((t : ℚ) + 1) ^ 2) ^ (j + 2)) := by
      generalize j + 2 = E
      rw [pow_mul (m * w * ((t : ℚ) + 1)) 2 E, pow_mul m 2 E,
        show (m * w * ((t : ℚ) + 1)) ^ 2 = m ^ 2 * w ^ 2 * ((t : ℚ) + 1) ^ 2 by ring,
        mul_pow, mul_pow, ← pow_mul w E 2, mul_comm E 2, pow_mul w 2 E]
      ring
    have e2 : m ^ (2 * (j + 2)) * (B : ℚ) ^ j ≤
        m ^ (2 * (j + 2)) * ((w ^ (j + 2)) ^ 2 * (n : ℚ) ^ (j + 2)) := by
      apply mul_le_mul_of_nonneg_left _ hm2
      have e : (w ^ (j + 2)) ^ 2 * (n : ℚ) ^ (j + 2) = (w ^ (j + 2) * n) ^ 2 * (n : ℚ) ^ j := by
        ring
      rw [e]
      have h1 : 1 ≤ (w ^ (j + 2) * n) ^ 2 := one_le_pow₀ hwn
      have h2 : (B : ℚ) ^ j ≤ (n : ℚ) ^ j := pow_le_pow_left₀ hB0 hBn j
      calc (B : ℚ) ^ j = 1 * (B : ℚ) ^ j := (one_mul _).symm
        _ ≤ (w ^ (j + 2) * n) ^ 2 * (n : ℚ) ^ j :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
    have e3 : m ^ (2 * (j + 2)) * ((w ^ (j + 2)) ^ 2 * (n : ℚ) ^ (j + 2)) ≤
        (m * w * ((t : ℚ) + 1)) ^ (2 * (j + 2)) := by
      rw [e1]
      apply mul_le_mul_of_nonneg_left _ hm2
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ hn0 hnt.le _
    linarith
  have hy0 : 0 ≤ m * w * ((t : ℚ) + 1) := by positivity
  have hy1 : 1 ≤ m * w * ((t : ℚ) + 1) := by
    by_contra hc
    rw [not_le] at hc
    have := pow_lt_one₀ hy0 hc (by omega : 2 * (j + 2) ≠ 0)
    linarith
  rw [div_le_iff₀ ht0]
  linarith

/-- A product of weights against the matching product of powers. -/
private theorem one_le_prod_pow {P : Finset ℕ} {c : ℕ → ℚ} (f : ℕ → ℕ) (k : ℕ)
    (h : ∀ g ∈ P, 1 ≤ c g ^ k * g) :
    1 ≤ (∏ g ∈ P, c g ^ f g) ^ k * ((∏ g ∈ P, g ^ f g : ℕ) : ℚ) := by
  rw [← Finset.prod_pow, Nat.cast_prod, ← Finset.prod_mul_distrib]
  calc (1 : ℚ) = ∏ g ∈ P, (1 : ℚ) := by simp
    _ ≤ _ := by
      refine Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun g hg => ?_
      have e : (c g ^ f g) ^ k * ((g ^ f g : ℕ) : ℚ) = (c g ^ k * g) ^ f g := by
        push_cast; ring
      rw [e]
      exact one_le_pow₀ (h g hg)

/-- A nonzero number whose prime factors lie in `P` is the product of its prime powers over
`P`. -/
private theorem eq_prod_pow {V : ℕ} (hV : V ≠ 0) {P : Finset ℕ} (h : V.primeFactors ⊆ P) :
    V = ∏ g ∈ P, g ^ V.factorization g := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hV]
  exact Finsupp.prod_of_support_subset _ (by rwa [Nat.support_factorization]) _
    (fun _ _ => pow_zero _)

/-- Stripping the elements of `U` (each at least 2) from a nonzero number one at a time. -/
private theorem split_pow (U : Finset ℕ) (hU : ∀ g ∈ U, 2 ≤ g) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ → ℕ, ∃ r : ℕ, n = (∏ g ∈ U, g ^ e g) * r ∧ ∀ g ∈ U, ¬ g ∣ r := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, n, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨e, r, hr, hdv⟩ := ih fun g hg => hU g (Finset.mem_insert_of_mem hg)
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact hn hr
    have ha2 := hU a (Finset.mem_insert_self a s)
    obtain ⟨i, r', hr', hrr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr0 a (by omega)
    refine ⟨Function.update e a i, r', ?_, ?_⟩
    · have hs : ∏ g ∈ s, g ^ Function.update e a i g = ∏ g ∈ s, g ^ e g :=
        Finset.prod_congr rfl fun g hg => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hg ha)]
      rw [Finset.prod_insert ha, Function.update_self, hs, hr, hrr]
      ring
    · intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hr'
      · exact fun h => hdv g hg (h.trans (Dvd.intro_left _ hrr.symm))

/-- Summing a nonnegative function over an injective image inside a finite box. -/
private theorem sum_le_of_injOn {β : Type*} [DecidableEq β] {T : Finset ℕ} {B : Finset β}
    (π : ℕ → β) (G : β → ℚ) (hmap : ∀ t ∈ T, π t ∈ B) (hinj : Set.InjOn π T)
    (hG : ∀ b, 0 ≤ G b) : ∑ t ∈ T, G (π t) ≤ ∑ b ∈ B, G b := by
  rw [← Finset.sum_image fun x hx y hy h => hinj hx hy h]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hG b
  intro b hb
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
  exact hmap t ht

end RankinTailGeneral

open RankinTailGeneral

/-- General Rankin tail bound with exponent `1/k`. Let every `t ∈ T` satisfy `t ≥ x ≥ 2`, let the
prime factors of `phi3 t` lie in `K ∪ U`, and let `phi3 t ≥ M` whenever no element of `U` divides
`phi3 t`. Known generators `g ∈ K` carry weights `0 ≤ α g < 1` with `α g ^ k * g ≥ 1`; the at most
`u` unknown generators in `U` are at least `x` and share the weight `0 ≤ αx < 1` with
`αx ^ k * x ≥ 1`. With `mL^(2k) (x^2 + x + 1)^(k - 2) ≥ 1` and `mM^(2k) M^(k - 2) ≥ 1`,
`∑ (σ(t^2)/t^2 - 1) ≤ ((x + 1)/x)^2 (mL G ((1/(1 - αx))^u - 1) + mM G)`, where
`G = ∏_{g ∈ K} 1/(1 - α g)`. This is Rankin's trick; the elements of `K` and `U` need not be
prime. -/
theorem rankin_tail_general (T K U : Finset ℕ) {x k M u : ℕ} {α : ℕ → ℚ} {αx mL mM : ℚ}
    (hx : 2 ≤ x) (hk : 3 ≤ k) (hKU : Disjoint K U) (hU : U.card ≤ u)
    (hα0 : ∀ g ∈ K, 0 ≤ α g) (hα1 : ∀ g ∈ K, α g < 1) (hαw : ∀ g ∈ K, 1 ≤ α g ^ k * g)
    (hax0 : 0 ≤ αx) (hax1 : αx < 1) (haxw : 1 ≤ αx ^ k * x) (hUx : ∀ g ∈ U, x ≤ g)
    (hmL0 : 0 ≤ mL) (hmL : 1 ≤ mL ^ (2 * k) * ((x ^ 2 + x + 1 : ℕ) : ℚ) ^ (k - 2))
    (hmM0 : 0 ≤ mM) (hmM : 1 ≤ mM ^ (2 * k) * (M : ℚ) ^ (k - 2))
    (hT : ∀ t ∈ T, x ≤ t ∧ (phi3 t).primeFactors ⊆ K ∪ U ∧
      ((∀ g ∈ U, ¬ g ∣ phi3 t) → M ≤ phi3 t)) :
    ∑ t ∈ T, (fv t - 1) ≤ ((x + 1 : ℚ) / x) ^ 2 *
      (mL * (∏ g ∈ K, 1 / (1 - α g)) * ((1 / (1 - αx)) ^ u - 1) +
        mM * ∏ g ∈ K, 1 / (1 - α g)) := by
  classical
  have _ := hKU
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [Nat.add_sub_cancel] at hmL hmM
  set c : ℚ := ((x + 1 : ℚ) / x) ^ 2 with hc
  set GK : ℚ := ∏ g ∈ K, 1 / (1 - α g) with hGK
  set Gx : ℚ := 1 / (1 - αx) with hGx
  have hc0 : 0 ≤ c := by positivity
  have hV0 : ∀ t, phi3 t ≠ 0 := fun t => by unfold phi3; omega
  have hU2 : ∀ g ∈ U, 2 ≤ g := fun g hg => le_trans hx (hUx g hg)
  have hlt : ∀ t ∈ T, phi3 t < (t + 1) ^ 2 := fun t ht =>
    phi3_lt_succ_sq (by have := (hT t ht).1; omega)
  have hfv : ∀ t ∈ T, fv t - 1 ≤ c * (1 / ((t : ℚ) + 1)) := fun t ht =>
    fv_sub_le_gen (by omega) (hT t ht).1
  have hxax : ∀ g ∈ U, 1 ≤ αx ^ (j + 2) * g := fun g hg => by
    have : (x : ℚ) ≤ g := by exact_mod_cast hUx g hg
    nlinarith [pow_nonneg hax0 (j + 2)]
  have hL : ∀ t ∈ T, x ^ 2 + x + 1 ≤ phi3 t := fun t ht =>
    phi3_strictMono.monotone (hT t ht).1
  -- the box of exponent vectors
  set N := T.sup phi3 + 1 with hN
  have hN0 : 0 < N := Nat.succ_pos _
  have hNt : ∀ t ∈ T, phi3 t < N := fun t ht => Nat.lt_succ_of_le (Finset.le_sup ht)
  set boxK := K.pi (fun _ => Finset.range N) with hboxK
  set boxU := U.pi (fun _ => Finset.range N) with hboxU
  set wK : (∀ a ∈ K, ℕ) → ℚ := fun f => ∏ y ∈ K.attach, α y.1 ^ f y.1 y.2 with hwK
  set wU : (∀ a ∈ U, ℕ) → ℚ := fun f => ∏ y ∈ U.attach, αx ^ f y.1 y.2 with hwU
  have wK0 : ∀ f, 0 ≤ wK f := fun f =>
    Finset.prod_nonneg fun y _ => pow_nonneg (hα0 y.1 y.2) _
  have wU0 : ∀ f, 0 ≤ wU f := fun f => Finset.prod_nonneg fun y _ => pow_nonneg hax0 _
  have sK : ∑ f ∈ boxK, wK f ≤ GK := by
    have e : ∑ f ∈ boxK, wK f = ∏ g ∈ K, ∑ i ∈ Finset.range N, α g ^ i :=
      (Finset.prod_sum K (fun _ => Finset.range N) (fun g i => α g ^ i)).symm
    rw [e]
    exact Finset.prod_le_prod₀
      (fun g hg => Finset.sum_nonneg fun i _ => pow_nonneg (hα0 g hg) i)
      (fun g hg => geom_partial_le (hα0 g hg) (hα1 g hg) N)
  have sK0 : 0 ≤ ∑ f ∈ boxK, wK f := Finset.sum_nonneg fun f _ => wK0 f
  have hSx1 : 1 ≤ ∑ i ∈ Finset.range N, αx ^ i := by
    have := Finset.single_le_sum (f := fun i => αx ^ i) (fun i _ => pow_nonneg hax0 i)
      (Finset.mem_range.mpr hN0)
    simpa using this
  have hSx := geom_partial_le hax0 hax1 N
  have h0U : (fun _ _ => 0 : ∀ a ∈ U, ℕ) ∈ boxU :=
    Finset.mem_pi.mpr fun _ _ => Finset.mem_range.mpr hN0
  have sU : ∑ f ∈ boxU.erase (fun _ _ => 0), wU f ≤ Gx ^ u - 1 := by
    have e : ∑ f ∈ boxU, wU f = (∑ i ∈ Finset.range N, αx ^ i) ^ U.card := by
      rw [← Finset.prod_const]
      exact (Finset.prod_sum U (fun _ => Finset.range N) (fun _ i => αx ^ i)).symm
    have e2 := Finset.sum_erase_add boxU wU h0U
    have w00 : wU (fun _ _ => 0) = 1 := by simp [hwU]
    have hG1 : 1 ≤ Gx := hSx1.trans hSx
    have : (∑ i ∈ Finset.range N, αx ^ i) ^ U.card ≤ Gx ^ u :=
      (pow_le_pow_left₀ (by linarith) hSx _).trans (pow_le_pow_right₀ hG1 hU)
    linarith
  have sU0 : 0 ≤ ∑ f ∈ boxU.erase (fun _ _ => 0), wU f :=
    Finset.sum_nonneg fun f _ => wU0 f
  -- the decomposition by the unknown generators
  choose e r hdec using fun t => split_pow U hU2 (hV0 t)
  have hr0 : ∀ t, r t ≠ 0 := fun t h => hV0 t (by rw [(hdec t).1, h, mul_zero])
  have hrdvd : ∀ t, r t ∣ phi3 t := fun t => Dvd.intro_left _ (hdec t).1.symm
  have hrK : ∀ t ∈ T, (r t).primeFactors ⊆ K := by
    intro t ht p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpn : p ∈ (phi3 t).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (hrdvd t), hV0 t⟩
    rcases Finset.mem_union.mp ((hT t ht).2.1 hpn) with h | h
    · exact h
    · exact absurd hpd ((hdec t).2 p h)
  have hrrep : ∀ t ∈ T, r t = ∏ g ∈ K, g ^ (r t).factorization g := fun t ht =>
    eq_prod_pow (hr0 t) (hrK t ht)
  set T1 := T.filter (fun t => ∃ g ∈ U, g ∣ phi3 t) with hT1
  set T2 := T.filter (fun t => ¬ ∃ g ∈ U, g ∣ phi3 t) with hT2
  -- rows divisible by an unknown generator
  set π1 : ℕ → (∀ a ∈ K, ℕ) × (∀ a ∈ U, ℕ) :=
    fun t => (fun g _ => (r t).factorization g, fun g _ => e t g) with hπ1
  have s1 : ∑ t ∈ T1, 1 / ((t : ℚ) + 1) ≤ mL * (GK * (Gx ^ u - 1)) := by
    have hrow : ∀ t ∈ T1, 1 / ((t : ℚ) + 1) ≤ mL * (wK (π1 t).1 * wU (π1 t).2) := by
      intro t ht
      have htT := (Finset.mem_filter.mp ht).1
      have eK : wK (π1 t).1 = ∏ g ∈ K, α g ^ (r t).factorization g :=
        Finset.prod_attach K (fun g => α g ^ (r t).factorization g)
      have eU : wU (π1 t).2 = ∏ g ∈ U, αx ^ e t g :=
        Finset.prod_attach U (fun g => αx ^ e t g)
      have hn : phi3 t = (∏ g ∈ U, g ^ e t g) * ∏ g ∈ K, g ^ (r t).factorization g := by
        rw [(hdec t).1]
        congr 1
        exact hrrep t htT
      refine rankin_step (n := phi3 t) (B := x ^ 2 + x + 1) hmL0
        (mul_nonneg (wK0 _) (wU0 _)) ?_ hmL (hL t htT) (hlt t htT)
      have a := one_le_prod_pow (P := K) (c := α) (r t).factorization (j + 2) hαw
      have b := one_le_prod_pow (P := U) (c := fun _ => αx) (e t) (j + 2) hxax
      beta_reduce at b
      rw [eK, eU, hn, Nat.cast_mul, mul_pow]
      calc (1 : ℚ) ≤ _ := one_le_mul_of_one_le_of_one_le a b
        _ = _ := by ring
    have hmap : ∀ t ∈ T1, π1 t ∈ boxK ×ˢ boxU.erase (fun _ _ => 0) := by
      intro t ht
      obtain ⟨htT, hex⟩ := Finset.mem_filter.mp ht
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
      · refine Finset.mem_pi.mpr fun g _ => Finset.mem_range.mpr ?_
        have h1 := Nat.factorization_lt g (hr0 t)
        have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (hV0 t)) (hrdvd t)
        have h3 := hNt t htT
        show (r t).factorization g < N
        omega
      · intro h
        obtain ⟨g, hg, hgd⟩ := hex
        have h0 : ∀ g ∈ U, e t g = 0 := fun g hg => congrFun (congrFun h g) hg
        have hpr : phi3 t = r t := by
          rw [(hdec t).1, Finset.prod_eq_one (fun g hg => by rw [h0 g hg, pow_zero]), one_mul]
        rw [hpr] at hgd
        exact (hdec t).2 g hg hgd
      · refine Finset.mem_pi.mpr fun g hg => Finset.mem_range.mpr ?_
        have h1 : g ^ e t g ∣ phi3 t :=
          (Finset.dvd_prod_of_mem (fun g => g ^ e t g) hg).trans (Dvd.intro _ (hdec t).1.symm)
        have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (hV0 t)) h1
        have h3 : e t g < g ^ e t g := Nat.lt_pow_self (by have := hU2 g hg; omega)
        have h4 := hNt t htT
        show e t g < N
        omega
    have hinj : Set.InjOn π1 T1 := by
      intro s hs t ht hst
      have hsT := (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).1
      have htT := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1
      have h1 : ∀ g ∈ K, (r s).factorization g = (r t).factorization g := fun g hg =>
        congrFun (congrFun (congrArg Prod.fst hst) g) hg
      have h2 : ∀ g ∈ U, e s g = e t g := fun g hg =>
        congrFun (congrFun (congrArg Prod.snd hst) g) hg
      have hr : r s = r t := by
        rw [hrrep s hsT, hrrep t htT]
        exact Finset.prod_congr rfl fun g hg => by rw [h1 g hg]
      have hu : ∏ g ∈ U, g ^ e s g = ∏ g ∈ U, g ^ e t g :=
        Finset.prod_congr rfl fun g hg => by rw [h2 g hg]
      apply phi3_strictMono.injective
      rw [(hdec s).1, (hdec t).1, hr, hu]
    calc ∑ t ∈ T1, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ T1, mL * (wK (π1 t).1 * wU (π1 t).2) :=
          Finset.sum_le_sum hrow
      _ = mL * ∑ t ∈ T1, (fun p => wK p.1 * wU p.2) (π1 t) := by rw [Finset.mul_sum]
      _ ≤ mL * ∑ p ∈ boxK ×ˢ boxU.erase (fun _ _ => 0), (fun p => wK p.1 * wU p.2) p :=
          mul_le_mul_of_nonneg_left (sum_le_of_injOn π1 _ hmap hinj
            (fun p => mul_nonneg (wK0 _) (wU0 _))) hmL0
      _ = mL * ((∑ f ∈ boxK, wK f) * ∑ f ∈ boxU.erase (fun _ _ => 0), wU f) := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ mL * (GK * (Gx ^ u - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul sK sU sU0 (sK0.trans sK)) hmL0
  -- rows free of the unknown generators
  set π2 : ℕ → (∀ a ∈ K, ℕ) := fun t => fun g _ => (phi3 t).factorization g with hπ2
  have hK2 : ∀ t ∈ T2, (phi3 t).primeFactors ⊆ K := by
    intro t ht p hp
    obtain ⟨htT, hno⟩ := Finset.mem_filter.mp ht
    rcases Finset.mem_union.mp ((hT t htT).2.1 hp) with h | h
    · exact h
    · exact absurd ⟨p, h, Nat.dvd_of_mem_primeFactors hp⟩ hno
  have s2 : ∑ t ∈ T2, 1 / ((t : ℚ) + 1) ≤ mM * GK := by
    have hrow : ∀ t ∈ T2, 1 / ((t : ℚ) + 1) ≤ mM * wK (π2 t) := by
      intro t ht
      obtain ⟨htT, hno⟩ := Finset.mem_filter.mp ht
      have eK : wK (π2 t) = ∏ g ∈ K, α g ^ (phi3 t).factorization g :=
        Finset.prod_attach K (fun g => α g ^ (phi3 t).factorization g)
      have hM : M ≤ phi3 t := (hT t htT).2.2 fun g hg hgd => hno ⟨g, hg, hgd⟩
      refine rankin_step (n := phi3 t) (B := M) hmM0 (wK0 _) ?_ hmM hM (hlt t htT)
      have a := one_le_prod_pow (P := K) (c := α) (phi3 t).factorization (j + 2) hαw
      rw [← eq_prod_pow (hV0 t) (hK2 t ht)] at a
      rw [eK]
      exact a
    have hmap : ∀ t ∈ T2, π2 t ∈ boxK := by
      intro t ht
      refine Finset.mem_pi.mpr fun g _ => Finset.mem_range.mpr ?_
      have h1 := Nat.factorization_lt g (hV0 t)
      have h3 := hNt t (Finset.mem_filter.mp ht).1
      show (phi3 t).factorization g < N
      omega
    have hinj : Set.InjOn π2 T2 := by
      intro s hs t ht hst
      have h1 : ∀ g ∈ K, (phi3 s).factorization g = (phi3 t).factorization g := fun g hg =>
        congrFun (congrFun hst g) hg
      apply phi3_strictMono.injective
      rw [eq_prod_pow (hV0 s) (hK2 s (Finset.mem_coe.mp hs)),
        eq_prod_pow (hV0 t) (hK2 t (Finset.mem_coe.mp ht))]
      exact Finset.prod_congr rfl fun g hg => by rw [h1 g hg]
    calc ∑ t ∈ T2, 1 / ((t : ℚ) + 1) ≤ ∑ t ∈ T2, mM * wK (π2 t) := Finset.sum_le_sum hrow
      _ = mM * ∑ t ∈ T2, wK (π2 t) := by rw [Finset.mul_sum]
      _ ≤ mM * ∑ f ∈ boxK, wK f :=
          mul_le_mul_of_nonneg_left (sum_le_of_injOn π2 wK hmap hinj wK0) hmM0
      _ ≤ mM * GK := mul_le_mul_of_nonneg_left sK hmM0
  -- assembly
  have split : ∑ t ∈ T1, (fv t - 1) + ∑ t ∈ T2, (fv t - 1) = ∑ t ∈ T, (fv t - 1) :=
    Finset.sum_filter_add_sum_filter_not T _ _
  have e1 : ∑ t ∈ T1, (fv t - 1) ≤ c * ∑ t ∈ T1, 1 / ((t : ℚ) + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht => hfv t (Finset.mem_filter.mp ht).1
  have e2 : ∑ t ∈ T2, (fv t - 1) ≤ c * ∑ t ∈ T2, 1 / ((t : ℚ) + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht => hfv t (Finset.mem_filter.mp ht).1
  have k1 := mul_le_mul_of_nonneg_left s1 hc0
  have k2 := mul_le_mul_of_nonneg_left s2 hc0
  have ex : c * (mL * GK * (Gx ^ u - 1) + mM * GK) =
      c * (mL * (GK * (Gx ^ u - 1))) + c * (mM * GK) := by ring
  rw [← split, ex]
  linarith

/-- Product form of `rankin_tail_general`: under the same hypotheses, if the bound is at most
`S < 1`, then `∏ σ(t^2)/t^2 ≤ 1/(1 - S)` over `T`. -/
theorem prod_fv_le_of_rankin_tail_general (T K U : Finset ℕ) {x k M u : ℕ} {α : ℕ → ℚ}
    {αx mL mM : ℚ}
    (hx : 2 ≤ x) (hk : 3 ≤ k) (hKU : Disjoint K U) (hU : U.card ≤ u)
    (hα0 : ∀ g ∈ K, 0 ≤ α g) (hα1 : ∀ g ∈ K, α g < 1) (hαw : ∀ g ∈ K, 1 ≤ α g ^ k * g)
    (hax0 : 0 ≤ αx) (hax1 : αx < 1) (haxw : 1 ≤ αx ^ k * x) (hUx : ∀ g ∈ U, x ≤ g)
    (hmL0 : 0 ≤ mL) (hmL : 1 ≤ mL ^ (2 * k) * ((x ^ 2 + x + 1 : ℕ) : ℚ) ^ (k - 2))
    (hmM0 : 0 ≤ mM) (hmM : 1 ≤ mM ^ (2 * k) * (M : ℚ) ^ (k - 2))
    (hT : ∀ t ∈ T, x ≤ t ∧ (phi3 t).primeFactors ⊆ K ∪ U ∧
      ((∀ g ∈ U, ¬ g ∣ phi3 t) → M ≤ phi3 t)) {S : ℚ}
    (hS : ((x + 1 : ℚ) / x) ^ 2 *
      (mL * (∏ g ∈ K, 1 / (1 - α g)) * ((1 / (1 - αx)) ^ u - 1) +
        mM * ∏ g ∈ K, 1 / (1 - α g)) ≤ S) (hS1 : S < 1) :
    ∏ t ∈ T, fv t ≤ 1 / (1 - S) := by
  have hsum := (rankin_tail_general T K U hx hk hKU hU hα0 hα1 hαw hax0 hax1 haxw hUx hmL0 hmL
    hmM0 hmM hT).trans hS
  have hnn : ∀ t ∈ T, 0 ≤ fv t - 1 := fun t ht =>
    fv_sub_one_nonneg (by have := (hT t ht).1; omega)
  have hP := prod_mul_one_sub_le T (fun t => fv t - 1) hnn
  have e : ∏ t ∈ T, (1 + (fv t - 1)) = ∏ t ∈ T, fv t :=
    Finset.prod_congr rfl fun t _ => by ring
  rw [e] at hP
  have hP0 : 0 ≤ ∏ t ∈ T, fv t := Finset.prod_nonneg fun t ht => by linarith [hnn t ht]
  rw [le_div_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left (by linarith : 1 - S ≤ 1 - ∑ t ∈ T, (fv t - 1)) hP0
  linarith

/-- A numerical instance with `K = {97}`, one unknown prime `q ≥ 53`, `x = 53`, `k = 4`,
`M = 10^30`: if every `t ∈ T` is at least `53`, `phi3 t` has prime factors in `{97, q}`, and
`phi3 t ≥ 10^30` when `q ∤ phi3 t`, then `∑ (σ(t^2)/t^2 - 1) ≤ 3/20`. The witnesses are
`α 97 = 10^6/3138288`, `αx = 10^6/2698167`, `mL = 8/53` and `mM = 31622777/10^15`; the
resulting bound is about `0.13542`. When `q = 97` the lemma is applied with `K` empty. -/
theorem rankin_tail_general_example (T : Finset ℕ) {q : ℕ} (hq : q.Prime) (hq53 : 53 ≤ q)
    (hT : ∀ t ∈ T, 53 ≤ t ∧ (phi3 t).primeFactors ⊆ {97, q} ∧
      (¬ q ∣ phi3 t → 10 ^ 30 ≤ phi3 t)) :
    ∑ t ∈ T, (fv t - 1) ≤ 3 / 20 := by
  have hUx : ∀ g ∈ ({q} : Finset ℕ), 53 ≤ g := fun g hg => by
    rw [Finset.mem_singleton.mp hg]; exact hq53
  have hT' : ∀ K : Finset ℕ, (({97, q} : Finset ℕ) ⊆ K ∪ {q}) → ∀ t ∈ T, 53 ≤ t ∧
      (phi3 t).primeFactors ⊆ K ∪ {q} ∧
      ((∀ g ∈ ({q} : Finset ℕ), ¬ g ∣ phi3 t) → 10 ^ 30 ≤ phi3 t) := fun K hK t ht =>
    ⟨(hT t ht).1, (hT t ht).2.1.trans hK,
      fun h => (hT t ht).2.2 (h q (Finset.mem_singleton_self q))⟩
  by_cases h97 : q = 97
  · subst h97
    have h := rankin_tail_general T ∅ {97} (x := 53) (k := 4) (M := 10 ^ 30) (u := 1)
      (α := fun _ => 0) (αx := 10 ^ 6 / 2698167) (mL := 8 / 53) (mM := 31622777 / 10 ^ 15)
      (by norm_num) (by norm_num) (Finset.disjoint_empty_left _) (by simp)
      (by simp) (by simp) (by simp) (by norm_num) (by norm_num) (by norm_num) hUx
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hT' ∅ (by intro a ha; simp_all))
    refine h.trans ?_
    norm_num
  · have h := rankin_tail_general T {97} {q} (x := 53) (k := 4) (M := 10 ^ 30) (u := 1)
      (α := fun _ => 10 ^ 6 / 3138288) (αx := 10 ^ 6 / 2698167) (mL := 8 / 53)
      (mM := 31622777 / 10 ^ 15)
      (by norm_num) (by norm_num) (Finset.disjoint_singleton.mpr (Ne.symm h97)) (by simp)
      (fun _ _ => by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hUx
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hT' {97} (by intro a ha; simp_all))
    refine h.trans ?_
    norm_num

end OddPerfect

#print axioms OddPerfect.rankin_tail_general
#print axioms OddPerfect.prod_fv_le_of_rankin_tail_general
#print axioms OddPerfect.rankin_tail_general_example
