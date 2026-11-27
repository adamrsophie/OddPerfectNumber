import OddPerfect.AbundancyGap

/-!
# A gap below 2 for abundancy products of few odd prime powers of Euler form

For a finite set `C` of odd primes with at most `s` elements, write
`V = ∏ c ∈ C, σ(c ^ e_c) / c ^ e_c`. The theorem `exists_abundancy_gap_general` gives, for every
`s`, a rational `ε > 0` such that `V < 2` forces `V < 2 - ε` whenever the exponents have Euler
form: `e_c` is even for every `c ≠ q`, and `q % 4 = 1`, `e_q % 4 = 1` when `q ∈ C`. The even
exponents are arbitrary (zero is allowed). This generalizes `exists_abundancy_gap`, where every
exponent except that of `q` was at least a bound `B`.

Argument. Write `H(c) = c / (c - 1)` and `h(c, e) = σ(c ^ e) / c ^ e`. A state is a finite set
`F` of odd primes split into large elements `L ⊆ F` and exact elements `F \ L` with exponents
`a`; every exact exponent is even except at most one, which is `1` modulo 4 at a prime that is
`1` modulo 4. Its ideal value is `I = (∏ exact, h(c, a_c)) * (∏ large, H(c))`. A parity
argument shows `I ≠ 2` when some element is large. By induction on the number `k` of primes
outside `F`, every state has a bound `B` (for the large elements) and an `ε > 0`: when `I ≥ 2`
the hypothesis `V < 2` fails for a large `B`; when `I < 2` either the least new prime is large
(and the product stays below `(I + 2) / 2`) or it is one of finitely many small primes, which
are added to the state, as a large element or with each of finitely many exact exponents.

The gap `ε` is not explicit: the proof gives no value.

A statement on finite sets of odd prime powers of Euler form; no published source was checked;
novelty not verified. The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace AbundancyGapGeneral

open AbundancyGap

/-- The ideal value of a state: exact factors on `F \ L` times `H` on the large set `L`. -/
def gideal (F L : Finset ℕ) (a : ℕ → ℕ) : ℚ :=
  (∏ c ∈ F \ L, hv c (a c)) * ∏ c ∈ L, Hv c

/-- A valid state: odd primes, `L ⊆ F`, exact exponents of Euler form with at most one odd. -/
def GValid (F L : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  (∀ c ∈ F, c.Prime ∧ c ≠ 2) ∧ L ⊆ F ∧
    (∀ c ∈ F \ L, Even (a c) ∨ (c % 4 = 1 ∧ a c % 4 = 1)) ∧
    (∀ c ∈ F \ L, ∀ d ∈ F \ L, ¬ Even (a c) → ¬ Even (a d) → c = d)

/-- The hypotheses on an extension `C` of a state, with exceptional prime `q`. -/
def GHyp (B : ℕ) (F L : Finset ℕ) (a : ℕ → ℕ) (C : Finset ℕ) (e : ℕ → ℕ) (q : ℕ) : Prop :=
  (∀ c ∈ F \ L, e c = a c) ∧ (∀ c ∈ L, B ≤ e c) ∧
    (∀ c ∈ C, c ≠ q → Even (e c)) ∧ (q ∈ C → q % 4 = 1 ∧ e q % 4 = 1)

/-- The gap property of a state for extensions by at most `k` primes. -/
def GGood (k : ℕ) (F L : Finset ℕ) (a : ℕ → ℕ) (B : ℕ) (ε : ℚ) : Prop :=
  ∀ (C : Finset ℕ) (e : ℕ → ℕ) (q : ℕ), F ⊆ C → (C \ F).card ≤ k →
    (∀ c ∈ C, c.Prime ∧ c ≠ 2) → GHyp B F L a C e q →
    ∏ c ∈ C, hv c (e c) < 2 → ∏ c ∈ C, hv c (e c) < 2 - ε

theorem sigma_mod_two {c : ℕ} (hc : c.Prime) (hc2 : c % 2 = 1) (a : ℕ) :
    σ 1 (c ^ a) % 2 = (a + 1) % 2 := by
  rw [sigma_one_apply_prime_pow hc, Finset.sum_nat_mod]
  have h : ∀ i ∈ Finset.range (a + 1), c ^ i % 2 = 1 := by
    intro i _
    rw [Nat.pow_mod, hc2]
    simp
  rw [Finset.sum_congr rfl h]
  simp

theorem prod_mod_two_gen (G : Finset ℕ) (f : ℕ → ℕ) (h : ∀ c ∈ G, f c % 2 = 1) :
    (∏ c ∈ G, f c) % 2 = 1 := by
  rw [Finset.prod_nat_mod, Finset.prod_congr rfl h]
  simp

/-- Parity: the ideal value of a valid state with a large element is never 2. -/
theorem gideal_ne_two {F L : Finset ℕ} {a : ℕ → ℕ} (hval : GValid F L a)
    (hL : L.Nonempty) : gideal F L a ≠ 2 := by
  obtain ⟨hF, hLF, heul, huniq⟩ := hval
  have hp : ∀ c ∈ F, c.Prime ∧ c ≠ 2 := hF
  have h3 : ∀ c ∈ F, 3 ≤ c := by
    intro c hc
    have := (hp c hc).1.two_le
    have := (hp c hc).2
    omega
  have hodd : ∀ c ∈ F, c % 2 = 1 :=
    fun c hc => Nat.odd_iff.mp ((hp c hc).1.odd_of_ne_two (hp c hc).2)
  have hX : ∀ c ∈ F \ L, c ∈ F := fun c hc => (Finset.mem_sdiff.mp hc).1
  intro h2
  unfold gideal at h2
  have hprodX : ∏ c ∈ F \ L, hv c (a c) =
      ((∏ c ∈ F \ L, σ 1 (c ^ a c) : ℕ) : ℚ) / ((∏ c ∈ F \ L, c ^ a c : ℕ) : ℚ) := by
    rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [hv, Nat.cast_pow]
  have hprodL : ∏ c ∈ L, Hv c =
      ((∏ c ∈ L, c : ℕ) : ℚ) / ((∏ c ∈ L, (c - 1) : ℕ) : ℚ) := by
    rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun c hc => ?_
    have := h3 c (hLF hc)
    rw [Hv, Nat.cast_sub (by omega), Nat.cast_one]
  have hQ0 : ((∏ c ∈ L, (c - 1) : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.prod_ne_zero_iff]
    intro c hc
    have := h3 c (hLF hc)
    omega
  have hP0 : ((∏ c ∈ F \ L, c ^ a c : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.prod_ne_zero_iff]
    intro c hc
    exact pow_ne_zero _ (hp c (hX c hc)).1.ne_zero
  rw [hprodX, hprodL, div_mul_div_comm, div_eq_iff (mul_ne_zero hP0 hQ0)] at h2
  have hnat : (∏ c ∈ F \ L, σ 1 (c ^ a c)) * (∏ c ∈ L, c) =
      2 * ((∏ c ∈ F \ L, c ^ a c) * ∏ c ∈ L, (c - 1)) := by
    exact_mod_cast h2
  obtain ⟨d, hd⟩ := hL
  have hQ2 : 2 ∣ ∏ c ∈ L, (c - 1) := by
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun c => c - 1) hd)
    have := hodd d (hLF hd)
    have := h3 d (hLF hd)
    omega
  obtain ⟨w, hw⟩ := hQ2
  rw [hw, show 2 * ((∏ c ∈ F \ L, c ^ a c) * (2 * w)) =
    4 * ((∏ c ∈ F \ L, c ^ a c) * w) by ring] at hnat
  have hPL : (∏ c ∈ L, c) % 2 = 1 :=
    prod_mod_two_gen L (fun c => c) fun c hc => hodd c (hLF hc)
  have hsig_even : ∀ c ∈ F \ L, Even (a c) → σ 1 (c ^ a c) % 2 = 1 := by
    intro c hc he
    rw [sigma_mod_two (hp c (hX c hc)).1 (hodd c (hX c hc))]
    have := Nat.even_iff.mp he
    omega
  -- the left side is odd or `2` modulo 4
  have hS : (∏ c ∈ F \ L, σ 1 (c ^ a c)) % 2 = 1 ∨
      (∏ c ∈ F \ L, σ 1 (c ^ a c)) % 4 = 2 := by
    by_cases hall : ∀ c ∈ F \ L, Even (a c)
    · exact Or.inl (prod_mod_two_gen _ _ fun c hc => hsig_even c hc (hall c hc))
    obtain ⟨c0, hc0, hne⟩ : ∃ c0 ∈ F \ L, ¬ Even (a c0) := by
      by_contra h
      push Not at h
      exact hall h
    right
    have hc04 := (heul c0 hc0).resolve_left hne
    rw [← Finset.mul_prod_erase _ _ hc0]
    have hrest : (∏ c ∈ (F \ L).erase c0, σ 1 (c ^ a c)) % 2 = 1 := by
      refine prod_mod_two_gen _ _ fun c hc => hsig_even c (Finset.mem_of_mem_erase hc) ?_
      by_contra hce
      exact Finset.ne_of_mem_erase hc (huniq c (Finset.mem_of_mem_erase hc) c0 hc0 hce hne)
    have h4 : σ 1 (c0 ^ a c0) % 4 = 2 := by
      rw [sigma_mod_four (hp c0 (hX c0 hc0)).1 hc04.1]
      omega
    rw [Nat.mul_mod, h4]
    have : (∏ c ∈ (F \ L).erase c0, σ 1 (c ^ a c)) % 4 = 1 ∨
        (∏ c ∈ (F \ L).erase c0, σ 1 (c ^ a c)) % 4 = 3 := by omega
    rcases this with h | h <;> rw [h]
  have hm2 := Nat.mul_mod (∏ c ∈ F \ L, σ 1 (c ^ a c)) (∏ c ∈ L, c) 2
  have hm4 := Nat.mul_mod (∏ c ∈ F \ L, σ 1 (c ^ a c)) (∏ c ∈ L, c) 4
  rw [hnat] at hm2 hm4
  rcases hS with hS | hS
  · rw [hS, hPL] at hm2
    omega
  · rw [hS] at hm4
    have : (∏ c ∈ L, c) % 4 = 1 ∨ (∏ c ∈ L, c) % 4 = 3 := by omega
    rcases this with h | h <;> rw [h] at hm4 <;> omega

theorem gideal_nonneg {F L : Finset ℕ} {a : ℕ → ℕ} (hval : GValid F L a) :
    0 ≤ gideal F L a := by
  unfold gideal
  refine mul_nonneg (Finset.prod_nonneg fun _ _ => hv_nonneg _ _)
    (Finset.prod_nonneg fun c hc => ?_)
  exact le_trans zero_le_one (one_le_Hv (hval.1 c (hval.2.1 hc)).1.two_le)

/-- Two sided bounds for the product over the known primes of a state. -/
theorem gknown_bounds {B : ℕ} {F L : Finset ℕ} {a : ℕ → ℕ} {C : Finset ℕ} {e : ℕ → ℕ}
    {q : ℕ} (hval : GValid F L a) (hyp : GHyp B F L a C e q) :
    gideal F L a * (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ^ L.card ≤ ∏ c ∈ F, hv c (e c) ∧
      ∏ c ∈ F, hv c (e c) ≤ gideal F L a := by
  obtain ⟨hF, hLF, -, -⟩ := hval
  obtain ⟨hex, hB, -, -⟩ := hyp
  have hτ0 : 0 ≤ ((3 : ℚ) ^ (B + 1))⁻¹ := by positivity
  have hτ1 : ((3 : ℚ) ^ (B + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hsplit : ∏ c ∈ F, hv c (e c) = (∏ c ∈ F \ L, hv c (a c)) * ∏ c ∈ L, hv c (e c) := by
    rw [← Finset.prod_sdiff hLF, Finset.prod_congr rfl fun c hc => by rw [hex c hc]]
  have hLp : ∀ c ∈ L, c.Prime ∧ c ≠ 2 := fun c hc => hF c (hLF hc)
  have hHn : ∀ c ∈ L, 0 ≤ Hv c :=
    fun c hc => le_trans zero_le_one (one_le_Hv (hLp c hc).1.two_le)
  have hup : ∏ c ∈ L, hv c (e c) ≤ ∏ c ∈ L, Hv c :=
    Finset.prod_le_prod₀ (fun c _ => hv_nonneg _ _) (fun c hc => (hv_lt_Hv (hLp c hc).1 _).le)
  have hlow : ∏ c ∈ L, (Hv c * (1 - ((3 : ℚ) ^ (B + 1))⁻¹)) ≤ ∏ c ∈ L, hv c (e c) :=
    Finset.prod_le_prod₀ (fun c hc => mul_nonneg (hHn c hc) (by linarith))
      (fun c hc => Hv_mul_le_hv (hLp c hc).1 (hLp c hc).2 (hB c hc))
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hlow
  have hX : 0 ≤ ∏ c ∈ F \ L, hv c (a c) := Finset.prod_nonneg fun _ _ => hv_nonneg _ _
  rw [hsplit]
  unfold gideal
  constructor
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hlow hX
  · exact mul_le_mul_of_nonneg_left hup hX

theorem gle_ideal_of_empty {B : ℕ} {F L : Finset ℕ} {a : ℕ → ℕ} {C : Finset ℕ} {e : ℕ → ℕ}
    {q : ℕ} (hval : GValid F L a) (hFC : F ⊆ C) (hyp : GHyp B F L a C e q)
    (hemp : C \ F = ∅) : ∏ c ∈ C, hv c (e c) ≤ gideal F L a := by
  rw [← Finset.prod_sdiff hFC, hemp, Finset.prod_empty, one_mul]
  exact (gknown_bounds hval hyp).2

theorem ggood_of_two_le {k : ℕ} {F L : Finset ℕ} {a : ℕ → ℕ} (hval : GValid F L a)
    (hI : 2 ≤ gideal F L a) : ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ GGood k F L a B ε := by
  have hB : ∃ B : ℕ, 2 ≤ gideal F L a * (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ^ L.card := by
    rcases hI.lt_or_eq with hI | hI
    · obtain ⟨B, hB⟩ := exists_B_big _ hI L.card
      exact ⟨B, hB.le⟩
    · have hL : L = ∅ := by
        by_contra hne
        exact gideal_ne_two hval (Finset.nonempty_iff_ne_empty.mpr hne) hI.symm
      subst hL
      exact ⟨0, by rw [Finset.card_empty, pow_zero, mul_one]; exact hI.le⟩
  obtain ⟨B, hB⟩ := hB
  refine ⟨B, 1, one_pos, ?_⟩
  intro C e q hFC _ hC hyp hV
  exfalso
  have hlow := (gknown_bounds hval hyp).1
  have hr1 := one_le_rest (F := F) (e := e) hC
  rw [← Finset.prod_sdiff hFC] at hV
  have hVF : 0 ≤ ∏ c ∈ F, hv c (e c) := by linarith
  have := mul_le_mul_of_nonneg_right hr1 hVF
  linarith

theorem ggood_zero {F L : Finset ℕ} {a : ℕ → ℕ} (hval : GValid F L a) :
    ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ GGood 0 F L a B ε := by
  rcases lt_or_ge (gideal F L a) 2 with hI | hI
  · refine ⟨0, (2 - gideal F L a) / 2, by linarith, ?_⟩
    intro C e q hFC hcard _ hyp _
    have := gle_ideal_of_empty hval hFC hyp (Finset.card_eq_zero.mp (by omega))
    linarith
  · exact ggood_of_two_le hval hI

theorem ggood_succ {k : ℕ}
    (ih : ∀ (F L : Finset ℕ) (a : ℕ → ℕ), GValid F L a →
      ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ GGood k F L a B ε)
    {F L : Finset ℕ} {a : ℕ → ℕ} (hval : GValid F L a) :
    ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ GGood (k + 1) F L a B ε := by
  classical
  rcases lt_or_ge (gideal F L a) 2 with hI | hI
  swap
  · exact ggood_of_two_le hval hI
  have hI0 := gideal_nonneg hval
  obtain ⟨hF, hLF, heul, huniq⟩ := hval
  obtain ⟨N, hN⟩ := exists_nat_gt ((gideal F L a + 2) * ((k : ℚ) + 1) / (2 - gideal F L a))
  set P := (Finset.range (max N 3)).filter (fun c => c.Prime ∧ c ≠ 2) with hPdef
  have hval1 : ∀ c ∈ P, GValid (insert c F) (insert c L) a := by
    intro c hc
    have hc' := (Finset.mem_filter.mp hc).2
    have hsub : ∀ d ∈ insert c F \ insert c L, d ∈ F \ L := by
      intro d hd
      obtain ⟨hd1, hd2⟩ := Finset.mem_sdiff.mp hd
      have hdc : d ≠ c := fun h => hd2 (h ▸ Finset.mem_insert_self _ _)
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_insert.mp hd1).resolve_left hdc,
        fun h => hd2 (Finset.mem_insert_of_mem h)⟩
    refine ⟨fun d hd => ?_, Finset.insert_subset_insert c hLF, fun d hd => heul d (hsub d hd),
      fun d hd d' hd' => huniq d (hsub d hd) d' (hsub d' hd')⟩
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hc'
    · exact hF d hd
  have hfam1 : ∀ c ∈ P, ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ GGood k (insert c F) (insert c L) a B ε :=
    fun c hc => ih _ _ _ (hval1 c hc)
  choose! B1 ε1 hε1 hG1 using hfam1
  set P2 := (P ×ˢ Finset.range (P.sup B1)).filter (fun p => p.1 ∉ F ∧
    (Even p.2 ∨ (p.1 % 4 = 1 ∧ p.2 % 4 = 1 ∧ ∀ d ∈ F \ L, Even (a d)))) with hP2def
  have hval2 : ∀ p ∈ P2, GValid (insert p.1 F) L (Function.update a p.1 p.2) := by
    intro p hp
    obtain ⟨hpP, hpF, hadm⟩ := Finset.mem_filter.mp hp
    have hp1 := (Finset.mem_filter.mp (Finset.mem_product.mp hpP).1).2
    have hpL : p.1 ∉ L := fun h => hpF (hLF h)
    have hmem : ∀ d ∈ insert p.1 F \ L, d = p.1 ∨ (d ≠ p.1 ∧ d ∈ F \ L) := by
      intro d hd
      obtain ⟨hd1, hd2⟩ := Finset.mem_sdiff.mp hd
      by_cases hdc : d = p.1
      · exact Or.inl hdc
      · exact Or.inr ⟨hdc, Finset.mem_sdiff.mpr
          ⟨(Finset.mem_insert.mp hd1).resolve_left hdc, hd2⟩⟩
    refine ⟨fun d hd => ?_, hLF.trans (Finset.subset_insert _ _), fun d hd => ?_,
      fun d hd d' hd' hodd hodd' => ?_⟩
    · rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hp1
      · exact hF d hd
    · rcases hmem d hd with rfl | ⟨hdc, hdX⟩
      · rw [Function.update_self]
        rcases hadm with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, h.2.1⟩
      · rw [Function.update_of_ne hdc]
        exact heul d hdX
    · rcases hmem d hd with rfl | ⟨hdc, hdX⟩ <;> rcases hmem d' hd' with rfl | ⟨hdc', hdX'⟩
      · rfl
      · rw [Function.update_self] at hodd
        rw [Function.update_of_ne hdc'] at hodd'
        exact absurd ((hadm.resolve_left hodd).2.2 d' hdX') hodd'
      · rw [Function.update_self] at hodd'
        rw [Function.update_of_ne hdc] at hodd
        exact absurd ((hadm.resolve_left hodd').2.2 d hdX) hodd
      · rw [Function.update_of_ne hdc] at hodd
        rw [Function.update_of_ne hdc'] at hodd'
        exact huniq d hdX d' hdX' hodd hodd'
  have hfam2 : ∀ p ∈ P2, ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧
      GGood k (insert p.1 F) L (Function.update a p.1 p.2) B ε :=
    fun p hp => ih _ _ _ (hval2 p hp)
  choose! B2 ε2 hε2 hG2 using hfam2
  obtain ⟨εa, hεa, hεa0, hεa1⟩ :=
    exists_eps_le P ε1 hε1 ((2 - gideal F L a) / 2) (by linarith)
  obtain ⟨ε, hε, hεεa, hεb⟩ := exists_eps_le P2 ε2 hε2 εa hεa
  have hval : GValid F L a := ⟨hF, hLF, heul, huniq⟩
  refine ⟨max (P.sup B1) (P2.sup B2), ε, hε, ?_⟩
  intro C e q hFC hcard hC hyp hV
  obtain ⟨hex, hB, hev, hq4⟩ := hyp
  by_cases hemp : C \ F = ∅
  · have := gle_ideal_of_empty hval hFC ⟨hex, hB, hev, hq4⟩ hemp
    linarith
  obtain ⟨c, hcmem, hmin⟩ :=
    (C \ F).exists_min_image id (Finset.nonempty_iff_ne_empty.mpr hemp)
  simp only [id] at hmin
  have hcC : c ∈ C := (Finset.mem_sdiff.mp hcmem).1
  have hcF : c ∉ F := (Finset.mem_sdiff.mp hcmem).2
  have hcp := hC c hcC
  have hc3 : 3 ≤ c := by
    have := hcp.1.two_le
    have := hcp.2
    omega
  by_cases hcbig : max N 3 ≤ c
  · obtain ⟨-, hup⟩ := gknown_bounds hval ⟨hex, hB, hev, hq4⟩
    have hr := rest_le (F := F) (e := e) hC (by omega) hmin hcard
    have hNc : (N : ℚ) ≤ c := by exact_mod_cast (le_max_left N 3).trans hcbig
    have hcI : (gideal F L a + 2) * (((k + 1 : ℕ) : ℚ)) < (2 - gideal F L a) * c := by
      rw [div_lt_iff₀ (by linarith)] at hN
      have := mul_le_mul_of_nonneg_left hNc (by linarith : (0 : ℚ) ≤ 2 - gideal F L a)
      push_cast
      nlinarith
    have ht := small_tail (gideal F L a) hI0 (k + 1) c (by omega) hcI
    rw [← Finset.prod_sdiff hFC]
    have hVF0 : 0 ≤ ∏ d ∈ F, hv d (e d) := Finset.prod_nonneg fun _ _ => hv_nonneg _ _
    have hHp : 0 ≤ Hv c ^ (k + 1) :=
      pow_nonneg (le_trans zero_le_one (one_le_Hv (by omega))) _
    have := mul_le_mul hr hup hVF0 hHp
    linarith
  have hcP : c ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcp⟩
  have hcard' : (C \ insert c F).card ≤ k := by
    rw [Finset.sdiff_insert, Finset.card_erase_of_mem hcmem]
    omega
  have hsub : insert c F ⊆ C := Finset.insert_subset hcC hFC
  have hcL : c ∉ L := fun h => hcF (hLF h)
  have hB1c : B1 c ≤ max (P.sup B1) (P2.sup B2) :=
    (Finset.le_sup (f := B1) hcP).trans (le_max_left _ _)
  by_cases hlarge : B1 c ≤ e c
  · have hgood := hG1 c hcP C e q hsub hcard' hC ?_ hV
    · have := hεa1 c hcP
      linarith
    refine ⟨fun d hd => ?_, fun d hd => ?_, hev, hq4⟩
    · obtain ⟨hd1, hd2⟩ := Finset.mem_sdiff.mp hd
      have hdc : d ≠ c := fun h => hd2 (h ▸ Finset.mem_insert_self _ _)
      exact hex d (Finset.mem_sdiff.mpr ⟨(Finset.mem_insert.mp hd1).resolve_left hdc,
        fun h => hd2 (Finset.mem_insert_of_mem h)⟩)
    · rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hlarge
      · exact hB1c.trans (hB d hd)
  push Not at hlarge
  have hadm : Even (e c) ∨ (c % 4 = 1 ∧ e c % 4 = 1 ∧ ∀ d ∈ F \ L, Even (a d)) := by
    by_cases hcq : c = q
    · subst hcq
      obtain ⟨h1, h2⟩ := hq4 hcC
      refine Or.inr ⟨h1, h2, fun d hd => ?_⟩
      have hdF := (Finset.mem_sdiff.mp hd).1
      rw [← hex d hd]
      exact hev d (hFC hdF) fun h => hcF (h ▸ hdF)
    · exact Or.inl (hev c hcC hcq)
  have hp2 : (c, e c) ∈ P2 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hcP, Finset.mem_range.mpr ?_⟩,
      hcF, hadm⟩
    exact lt_of_lt_of_le hlarge (Finset.le_sup (f := B1) hcP)
  have hB2c : B2 (c, e c) ≤ max (P.sup B1) (P2.sup B2) :=
    (Finset.le_sup (f := B2) hp2).trans (le_max_right _ _)
  have hgood := hG2 (c, e c) hp2 C e q hsub hcard' hC ?_ hV
  · have := hεb _ hp2
    linarith
  refine ⟨fun d hd => ?_, fun d hd => hB2c.trans (hB d hd), hev, hq4⟩
  obtain ⟨hd1, hd2⟩ := Finset.mem_sdiff.mp hd
  by_cases hdc : d = c
  · rw [hdc]
    exact (Function.update_self c (e c) a).symm
  · show e d = Function.update a c (e c) d
    rw [Function.update_of_ne hdc]
    exact hex d (Finset.mem_sdiff.mpr ⟨(Finset.mem_insert.mp hd1).resolve_left hdc, hd2⟩)

theorem gclaim (k : ℕ) : ∀ (F L : Finset ℕ) (a : ℕ → ℕ), GValid F L a →
    ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ GGood k F L a B ε := by
  induction k with
  | zero => exact fun F L a h => ggood_zero h
  | succ k ih => exact fun F L a h => ggood_succ ih h

end AbundancyGapGeneral

/-- A gap below 2 for at most `s` odd prime powers of Euler form: if `e c` is even for every
`c ≠ q`, and `q % 4 = 1`, `e q % 4 = 1` when `q ∈ C`, then a product
`∏ σ(c ^ e_c) / c ^ e_c` below 2 is below `2 - ε`. A statement on finite sets of odd prime
powers of Euler form; the gap `ε` is not explicit (the proof gives no value); no published
source was checked; novelty not verified; the odd perfect number conjecture remains open. -/
theorem exists_abundancy_gap_general (s : ℕ) :
    ∃ ε : ℚ, 0 < ε ∧
      ∀ (C : Finset ℕ) (e : ℕ → ℕ) (q : ℕ), C.card ≤ s → (∀ c ∈ C, c.Prime ∧ c ≠ 2) →
        (∀ c ∈ C, c ≠ q → Even (e c)) → (q ∈ C → q % 4 = 1 ∧ e q % 4 = 1) →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) < 2 →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) < 2 - ε := by
  obtain ⟨B, ε, hε, hG⟩ := AbundancyGapGeneral.gclaim s ∅ ∅ (fun _ => 0)
    ⟨by simp, subset_rfl, by simp, by simp⟩
  refine ⟨ε, hε, ?_⟩
  intro C e q hcard hC hev hq hV
  exact hG C e q (Finset.empty_subset _) (by simpa using hcard) hC
    ⟨by simp, by simp, hev, hq⟩ hV

end OddPerfect

#print axioms OddPerfect.exists_abundancy_gap_general
