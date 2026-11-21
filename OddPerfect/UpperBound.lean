import OddPerfect.Abundancy

/-!
# An explicit upper bound for odd perfect numbers

Following Heath-Brown (1994), Cook (1999) and Nielsen (2003), an odd perfect number `N` with
`k` distinct prime factors satisfies `N < 2^(4^k)` (`lt_two_pow_four_pow`), and hence
`N < 4^(4^k)` (`lt_four_pow_four_pow`). More generally an odd `N` with `σ(N)/N = n/d`
satisfies `d N < (d + 1)^(4^k)` (`mul_lt_succ_pow_four_pow`).

The key input is Cook's lemma (`UpperBound.cook_lemma`): for integers `2 ≤ x_1 < ... < x_r`
with `∏_{i ≤ r} (1 - 1/x_i) ≤ a/b < ∏_{i < r} (1 - 1/x_i)` one has
`a ∏ x_i < (a + 1)^(2^r)`. It is proved by strong induction on `r`; when no initial segment
is small enough to apply the induction hypothesis, a weak majorization argument (Abel
summation with the concavity of `t ↦ log (1 - e^{-t})`) compares the `x_i` with the
extremal sequence `(a + 1)^(2^i) + 1` and gives a contradiction.

The main theorem then follows Heath-Brown's algorithm as sharpened by Nielsen: from a set `S`
of known primes, Cook's lemma is applied first to new primes and then to prime power
components `p^(e+1)`, which splits off a coprime factor `V` of `N`; the cofactor `N/V` is again
odd with rational abundancy, with denominator `d σ(V)`, and the induction runs on the number of
prime factors. Odd parity is used only to rule out `∏_{p ∈ R} (1 - 1/p) = d/n`.
-/

open Finset

namespace OddPerfect.UpperBound

/-- Tangent line inequality for the concave function `t ↦ log (1 - e^{-t})`. -/
private theorem log_step {x n : ℝ} (hx : 1 < x) (hn : 1 < n) :
    Real.log (1 - 1 / n) - Real.log (1 - 1 / x) ≤ (Real.log n - Real.log x) / (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hn0 : 0 < n := by linarith
  have hxm : 0 < x - 1 := by linarith
  have h1x : 0 < 1 - 1 / x := by
    have : 1 / x < 1 := (div_lt_one hx0).mpr hx
    linarith
  have h1n : 0 < 1 - 1 / n := by
    have : 1 / n < 1 := (div_lt_one hn0).mpr hn
    linarith
  rw [← Real.log_div h1n.ne' h1x.ne']
  have h2 := Real.log_le_sub_one_of_pos (div_pos h1n h1x)
  have h3 := Real.log_le_sub_one_of_pos (div_pos hx0 hn0)
  rw [Real.log_div hx0.ne' hn0.ne'] at h3
  have e1 : (1 - 1 / n) / (1 - 1 / x) - 1 = (n - x) / n / (x - 1) := by
    field_simp
    ring
  have e2 : (n - x) / n ≤ Real.log n - Real.log x := by
    have : (n - x) / n = 1 - x / n := by field_simp
    linarith
  calc _ ≤ (1 - 1 / n) / (1 - 1 / x) - 1 := h2
    _ = (n - x) / n / (x - 1) := e1
    _ ≤ _ := div_le_div_of_nonneg_right e2 hxm.le

/-- Weak majorization for `log (1 - 1/x)` over a finset, in Abel summation form. -/
private theorem maj (n : ℕ → ℝ) (hn : ∀ i, 1 < n i) (s : Finset ℕ) (hs2 : ∀ x ∈ s, 2 ≤ x)
    (hdom : ∀ y ∈ s, ∑ i ∈ range (s.filter (· ≤ y)).card, Real.log (n i) ≤
      ∑ x ∈ s.filter (· ≤ y), Real.log x) :
    ∀ g : ℝ, 0 ≤ g → (∀ x ∈ s, g ≤ 1 / ((x : ℝ) - 1)) →
      g * (∑ x ∈ s, Real.log x - ∑ i ∈ range s.card, Real.log (n i)) ≤
        ∑ x ∈ s, Real.log (1 - 1 / (x : ℝ)) - ∑ i ∈ range s.card, Real.log (1 - 1 / n i) := by
  induction s using Finset.induction_on_max with
  | empty => intro g _ _; simp
  | insert z s hz ih =>
    intro g hg0 hg
    have hzs : z ∉ s := fun h => lt_irrefl z (hz z h)
    have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hs2 z (mem_insert_self z s)
    have hz1 : (1 : ℝ) < z := by linarith
    set g' : ℝ := 1 / ((z : ℝ) - 1) with hg'
    have hg'0 : 0 ≤ g' := by rw [hg']; exact (one_div_pos.mpr (by linarith)).le
    have hfilt : ∀ y ∈ s, (insert z s).filter (· ≤ y) = s.filter (· ≤ y) := by
      intro y hy
      rw [filter_insert, if_neg (by have := hz y hy; omega)]
    have ih' := ih (fun x hx => hs2 x (mem_insert_of_mem hx))
      (fun y hy => by rw [← hfilt y hy]; exact hdom y (mem_insert_of_mem hy)) g' hg'0
      (fun x hx => by
        have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hs2 x (mem_insert_of_mem hx)
        have hxz : (x : ℝ) < z := by exact_mod_cast hz x hx
        rw [hg']
        exact one_div_le_one_div_of_le (by linarith) (by linarith))
    have hstep := log_step hz1 (hn s.card)
    have hD : 0 ≤ ∑ x ∈ insert z s, Real.log x - ∑ i ∈ range (insert z s).card, Real.log (n i) := by
      have h := hdom z (mem_insert_self z s)
      rw [filter_true_of_mem (fun x hx => by
        rcases mem_insert.mp hx with rfl | hx
        · exact le_refl _
        · exact (hz x hx).le)] at h
      linarith
    have hgg : g ≤ g' := hg z (mem_insert_self z s)
    rw [card_insert_of_notMem hzs, sum_insert hzs, sum_insert hzs, sum_range_succ,
      sum_range_succ] at *
    have key : g' * (Real.log z - Real.log (n s.card)) ≤
        Real.log (1 - 1 / (z : ℝ)) - Real.log (1 - 1 / n s.card) := by
      have : g' * (Real.log z - Real.log (n s.card)) =
          -((Real.log (n s.card) - Real.log z) / ((z : ℝ) - 1)) := by
        rw [hg']; field_simp; ring
      rw [this]; linarith
    have := mul_le_mul_of_nonneg_right hgg hD
    nlinarith

private theorem prod_pow_two_add_one (A : ℝ) (r : ℕ) :
    (A - 1) * ∏ i ∈ range r, (A ^ (2 ^ i) + 1) = A ^ (2 ^ r) - 1 := by
  induction r with
  | zero => simp
  | succ r ih => rw [prod_range_succ, ← mul_assoc, ih, pow_succ, pow_mul]; ring

private theorem prod_pow_two (A : ℝ) (r : ℕ) :
    (∏ i ∈ range r, A ^ (2 ^ i)) * A = A ^ (2 ^ r) := by
  induction r with
  | zero => simp
  | succ r ih => rw [prod_range_succ, mul_right_comm, ih, pow_succ, pow_mul]; ring

private theorem one_sub_inv_pos {x : ℕ} (hx : 2 ≤ x) : 0 < 1 - 1 / (x : ℚ) := by
  have : (2 : ℚ) ≤ x := by exact_mod_cast hx
  have : 1 / (x : ℚ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
  linarith

private theorem one_sub_inv_le_one (x : ℕ) : 1 - 1 / (x : ℚ) ≤ 1 := by
  have : 0 ≤ 1 / (x : ℚ) := by positivity
  linarith

private theorem prod_one_sub_inv_eq {H : Finset ℕ} (h2 : ∀ x ∈ H, 2 ≤ x) :
    ∏ x ∈ H, (1 - 1 / (x : ℚ)) = ((∏ x ∈ H, (x - 1) : ℕ) : ℚ) / ((∏ x ∈ H, x : ℕ) : ℚ) := by
  rw [Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
  refine prod_congr rfl (fun x hx => ?_)
  have hx := h2 x hx
  have hx0 : (x : ℚ) ≠ 0 := by positivity
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  field_simp

/-- Cook's lemma, by strong induction on the number of factors. -/
private theorem lemma1 : ∀ (r : ℕ) (G : Finset ℕ) (a b m : ℕ), G.card = r → 0 < a →
    (∀ x ∈ G, 2 ≤ x) → m ∈ G → (∀ x ∈ G, x ≤ m) →
    ∏ x ∈ G, (1 - 1 / (x : ℚ)) ≤ a / b →
    (a : ℚ) / b < ∏ x ∈ G.erase m, (1 - 1 / (x : ℚ)) →
    a * ∏ x ∈ G, x < (a + 1) ^ (2 ^ G.card) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r IH =>
  intro G a b m hr ha h2 hm hmax hle hlt
  have hpos : ∀ T ⊆ G, 0 < ∏ x ∈ T, (1 - 1 / (x : ℚ)) :=
    fun T hT => prod_pos (fun x hx => one_sub_inv_pos (h2 x (hT hx)))
  have hle1 : ∀ T ⊆ G, ∏ x ∈ T, (1 - 1 / (x : ℚ)) ≤ 1 := fun T hT =>
    prod_le_one (fun x hx => (one_sub_inv_pos (h2 x (hT hx))).le)
      (fun x _ => one_sub_inv_le_one x)
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · have := hpos G subset_rfl
      rw [h, Nat.cast_zero, div_zero] at hle; linarith
    · exact h
  have hab : a < b := by
    have h1 := hle1 (G.erase m) (erase_subset m G)
    have : (a : ℚ) / b < 1 := lt_of_lt_of_le hlt h1
    rw [div_lt_one (by exact_mod_cast hb)] at this
    exact_mod_cast this
  by_cases hgood : ∃ y ∈ G, a * ∏ x ∈ G.filter (· ≤ y), x + 1 ≤
      (a + 1) ^ (2 ^ (G.filter (· ≤ y)).card)
  · obtain ⟨y, hyG, hy⟩ := hgood
    by_cases hym : m ≤ y
    · rw [filter_true_of_mem (fun x hx => le_trans (hmax x hx) hym)] at hy
      omega
    push Not at hym
    set H := G.filter (· ≤ y) with hH
    set K := G.filter (fun x => ¬ x ≤ y) with hK
    have hcard : H.card + K.card = G.card := card_filter_add_card_filter_not (· ≤ y)
    have hyH : y ∈ H := mem_filter.mpr ⟨hyG, le_rfl⟩
    have hHpos : 0 < H.card := card_pos.mpr ⟨y, hyH⟩
    have hKlt : K.card < r := by omega
    have hmK : m ∈ K := mem_filter.mpr ⟨hm, by omega⟩
    have hmH : m ∉ H := fun h => by have := (mem_filter.mp h).2; omega
    have hKG : K ⊆ G := filter_subset _ _
    have hHG : H ⊆ G := filter_subset _ _
    have h2H : ∀ x ∈ H, 2 ≤ x := fun x hx => h2 x (hHG hx)
    have hUH : 0 < ∏ x ∈ H, (x - 1) := prod_pos (fun x hx => by have := h2H x hx; omega)
    have hPH : 0 < ∏ x ∈ H, x := prod_pos (fun x hx => by have := h2H x hx; omega)
    have cH := prod_one_sub_inv_eq h2H
    have cHpos : 0 < ∏ x ∈ H, (1 - 1 / (x : ℚ)) := hpos H hHG
    have hG : ∏ x ∈ G, (1 - 1 / (x : ℚ)) =
        (∏ x ∈ H, (1 - 1 / (x : ℚ))) * ∏ x ∈ K, (1 - 1 / (x : ℚ)) :=
      (prod_filter_mul_prod_filter_not G (· ≤ y) _).symm
    have hGe : ∏ x ∈ G.erase m, (1 - 1 / (x : ℚ)) =
        (∏ x ∈ H, (1 - 1 / (x : ℚ))) * ∏ x ∈ K.erase m, (1 - 1 / (x : ℚ)) := by
      rw [← prod_filter_mul_prod_filter_not (G.erase m) (· ≤ y), filter_erase, filter_erase,
        ← hH, ← hK, erase_eq_of_notMem hmH]
    have hfrac : (((a * ∏ x ∈ H, x : ℕ) : ℚ) / ((b * ∏ x ∈ H, (x - 1) : ℕ) : ℚ)) =
        ((a : ℚ) / b) / ∏ x ∈ H, (1 - 1 / (x : ℚ)) := by
      rw [cH]
      have : ((∏ x ∈ H, (x - 1) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hUH.ne'
      have : ((∏ x ∈ H, x : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hPH.ne'
      have : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
      push_cast
      field_simp
    have hIH := IH K.card hKlt K (a * ∏ x ∈ H, x) (b * ∏ x ∈ H, (x - 1)) m rfl
      (Nat.mul_pos ha hPH) (fun x hx => h2 x (hKG hx)) hmK
      (fun x hx => hmax x (hKG hx))
      (by rw [hfrac, le_div_iff₀ cHpos, mul_comm, ← hG]; exact hle)
      (by rw [hfrac, div_lt_iff₀ cHpos, mul_comm, ← hGe]; exact hlt)
    have hsplit : a * ∏ x ∈ G, x = (a * ∏ x ∈ H, x) * ∏ x ∈ K, x := by
      rw [mul_assoc, prod_filter_mul_prod_filter_not]
    rw [hsplit]
    calc _ < (a * ∏ x ∈ H, x + 1) ^ (2 ^ K.card) := hIH
      _ ≤ ((a + 1) ^ (2 ^ H.card)) ^ (2 ^ K.card) := Nat.pow_le_pow_left hy _
      _ = (a + 1) ^ (2 ^ G.card) := by rw [← pow_mul, ← pow_add, hcard]
  · push Not at hgood
    exfalso
    set A : ℝ := (a : ℝ) + 1 with hA
    have hA2 : (2 : ℝ) ≤ A := by
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha
      linarith
    set n : ℕ → ℝ := fun i => A ^ (2 ^ i) + 1 with hn
    have hn1 : ∀ i, 1 < n i := fun i => by
      have : 0 < A ^ (2 ^ i) := by positivity
      simp only [hn]; linarith
    have hn0 : ∀ i, n i ≠ 0 := fun i => by have := hn1 i; positivity
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    have hdom : ∀ y ∈ G, ∑ i ∈ range (G.filter (· ≤ y)).card, Real.log (n i) ≤
        ∑ x ∈ G.filter (· ≤ y), Real.log x := by
      intro y hy
      have hg := hgood y hy
      set H := G.filter (· ≤ y)
      have hH0 : ∀ x ∈ H, (x : ℝ) ≠ 0 := fun x hx => by
        have := h2 x (filter_subset _ _ hx); positivity
      rw [← Real.log_prod (fun i _ => hn0 i), ← Real.log_prod hH0]
      apply Real.log_le_log (prod_pos (fun i _ => by have := hn1 i; linarith))
      have e := prod_pow_two_add_one A H.card
      have hg' : A ^ (2 ^ H.card) < (a : ℝ) * ∏ x ∈ H, (x : ℝ) + 1 := by
        have := (Nat.cast_lt (α := ℝ)).mpr hg
        push_cast at this
        exact this
      have hAa : A - 1 = a := by rw [hA]; ring
      rw [hAa] at e
      have : (a : ℝ) * ∏ i ∈ range H.card, n i < (a : ℝ) * ∏ x ∈ H, (x : ℝ) := by
        simp only [hn]; linarith
      exact (lt_of_mul_lt_mul_left this ha0.le).le
    have M := maj n hn1 G h2 hdom 0 le_rfl (fun x hx => by
      have : (2 : ℝ) ≤ x := by exact_mod_cast h2 x hx
      exact (one_div_pos.mpr (by linarith)).le)
    rw [zero_mul] at M
    have hG0 : ∀ x ∈ G, (1 - 1 / (x : ℝ)) ≠ 0 := fun x hx => by
      have : (2 : ℝ) ≤ x := by exact_mod_cast h2 x hx
      have : 1 / (x : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
      linarith
    have hn0' : ∀ i ∈ range G.card, (1 - 1 / n i) ≠ 0 := fun i _ => by
      have := hn1 i
      have : 1 / n i < 1 := (div_lt_one (by linarith)).mpr this
      linarith
    rw [← Real.log_prod hG0, ← Real.log_prod hn0', sub_nonneg] at M
    -- the extremal product exceeds a / (a + 1)
    have hext : (a : ℝ) / A < ∏ i ∈ range G.card, (1 - 1 / n i) := by
      have e1 : ∀ i, 1 - 1 / n i = A ^ (2 ^ i) / n i := fun i => by
        have := hn0 i
        field_simp
        simp only [hn]; ring
      simp_rw [e1]
      rw [prod_div_distrib]
      have hP := prod_pow_two_add_one A G.card
      have hQ := prod_pow_two A G.card
      have hPpos : 0 < ∏ i ∈ range G.card, n i := prod_pos (fun i _ => by have := hn1 i; linarith)
      rw [div_lt_div_iff₀ (by linarith) hPpos]
      have hAa : A - 1 = a := by rw [hA]; ring
      rw [hAa] at hP
      simp only [hn] at hPpos ⊢
      nlinarith
    have hprodpos : 0 < ∏ x ∈ G, (1 - 1 / (x : ℝ)) :=
      prod_pos (fun x hx => by
        have : (2 : ℝ) ≤ x := by exact_mod_cast h2 x hx
        have : 1 / (x : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
        linarith)
    have hlog := Real.log_le_log_iff (prod_pos (fun i hi => by
      have := hn0' i hi
      have h1 := hn1 i
      have : 1 / n i < 1 := (div_lt_one (by linarith)).mpr h1
      linarith)) hprodpos |>.mp M
    have hreal : ∏ x ∈ G, (1 - 1 / (x : ℝ)) ≤ (a : ℝ) / b := by
      have := (Rat.cast_le (K := ℝ)).mpr hle
      push_cast at this
      exact this
    have hbA : (a : ℝ) / b ≤ (a : ℝ) / A := by
      apply div_le_div_of_nonneg_left ha0.le (by linarith)
      have : ((a + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hab
      push_cast at this; linarith
    linarith

/-- Cook's lemma (Nielsen 2003, Lemma 1). Let `G` be a finset of integers `x ≥ 2` with
largest element `m`, and let `a > 0`. If `∏_{x ∈ G} (1 - 1/x) ≤ a/b < ∏_{x ∈ G, x ≠ m} (1 - 1/x)`
then `a ∏_{x ∈ G} x < (a + 1)^(2^|G|)`. -/
theorem cook_lemma {G : Finset ℕ} {a b m : ℕ} (ha : 0 < a) (h2 : ∀ x ∈ G, 2 ≤ x) (hm : m ∈ G)
    (hmax : ∀ x ∈ G, x ≤ m) (hle : ∏ x ∈ G, (1 - 1 / (x : ℚ)) ≤ a / b)
    (hlt : (a : ℚ) / b < ∏ x ∈ G.erase m, (1 - 1 / (x : ℚ))) :
    a * ∏ x ∈ G, x < (a + 1) ^ (2 ^ G.card) :=
  lemma1 _ G a b m rfl ha h2 hm hmax hle hlt

/-- Selection form of Cook's lemma: if `∏_{x ∈ F} (1 - 1/x) ≤ a/b` for a finset `F` of
integers `x ≥ 2` and `a > 0`, then some subset `G ⊆ F` (an initial segment of `F`) satisfies
`∏_{x ∈ G} (1 - 1/x) ≤ a/b` and `a ∏_{x ∈ G} x < (a + 1)^(2^|G|)`. -/
theorem select {F : Finset ℕ} {a b : ℕ} (ha : 0 < a) (h2 : ∀ x ∈ F, 2 ≤ x)
    (hF : ∏ x ∈ F, (1 - 1 / (x : ℚ)) ≤ a / b) :
    ∃ G ⊆ F, ∏ x ∈ G, (1 - 1 / (x : ℚ)) ≤ a / b ∧ a * ∏ x ∈ G, x < (a + 1) ^ (2 ^ G.card) := by
  by_cases h1 : (1 : ℚ) ≤ a / b
  · exact ⟨∅, empty_subset _, by simpa using h1, by simp⟩
  push Not at h1
  have hex : ∃ t, ∏ x ∈ F.filter (· ≤ t), (1 - 1 / (x : ℚ)) ≤ a / b :=
    ⟨F.sup id, by
      have hl : ∀ x ∈ F, x ≤ F.sup id := fun x hx => le_sup (f := id) hx
      rw [filter_true_of_mem hl]; exact hF⟩
  classical
  have hpt := Nat.find_spec hex
  have ht0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, filter_false_of_mem (fun x hx => by have := h2 x hx; omega), prod_empty] at hpt
    linarith
  obtain ⟨s, hs⟩ : ∃ s, Nat.find hex = s + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hns : ¬ ∏ x ∈ F.filter (· ≤ s), (1 - 1 / (x : ℚ)) ≤ a / b :=
    Nat.find_min hex (by omega)
  rw [hs] at hpt
  push Not at hns
  have htF : s + 1 ∈ F := by
    by_contra hc
    apply (not_lt.mpr hpt)
    convert hns using 2
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hx, hxs⟩
      refine ⟨hx, ?_⟩
      rcases Nat.lt_or_ge x (s + 1) with h | h
      · omega
      · exact absurd (show x = s + 1 by omega ▸ hx) hc
    · rintro ⟨hx, hxs⟩; exact ⟨hx, by omega⟩
  set G := F.filter (· ≤ s + 1)
  have hmG : s + 1 ∈ G := mem_filter.mpr ⟨htF, le_rfl⟩
  have herase : G.erase (s + 1) = F.filter (· ≤ s) := by
    ext x
    simp only [G, mem_erase, mem_filter]
    constructor
    · rintro ⟨hne, hx, hle⟩; exact ⟨hx, by omega⟩
    · rintro ⟨hx, hle⟩; exact ⟨by omega, hx, by omega⟩
  refine ⟨G, filter_subset _ _, hpt, ?_⟩
  exact lemma1 _ G a b (s + 1) rfl ha (fun x hx => h2 x (filter_subset _ _ hx)) hmG
    (fun x hx => (mem_filter.mp hx).2) hpt (by rw [herase]; exact hns)

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem abundancy_mul_one_sub {p : ℕ} (hp : p.Prime) (k : ℕ) :
    abundancy (p ^ k) * (1 - 1 / (p : ℚ)) = 1 - 1 / ((p ^ (k + 1) : ℕ) : ℚ) := by
  rw [abundancy_prime_pow hp, one_div, geom_sum_mul_neg]
  push_cast
  rw [one_div, inv_pow]

private theorem sigma_mul_sub_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (σ 1 (p ^ k) : ℚ) * ((p : ℚ) - 1) = (p : ℚ) ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul _ _

private theorem succ_le_sigma {N : ℕ} (hN : 1 < N) : N + 1 ≤ σ 1 N := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have : 1 ≤ ∑ i ∈ N.properDivisors, i :=
    single_le_sum (f := id) (fun _ _ => Nat.zero_le _)
      (Nat.one_mem_properDivisors_iff_one_lt.mpr hN)
  omega

section Step

variable {N d n : ℕ}

private theorem two_le_of_mem {N p : ℕ} (hp : p ∈ N.primeFactors) : 2 ≤ p :=
  (Nat.prime_of_mem_primeFactors hp).two_le

private theorem n_pos (hN : 0 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N) : 0 < n := by
  have : 0 < σ 1 N := by
    have := ArithmeticFunction.sigma_pos 1 N hN.ne'
    exact this
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, zero_mul] at hσ
    exact absurd hσ (Nat.mul_pos hd this).ne'
  · exact h

private theorem abundancy_eq (hN : 0 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N) :
    abundancy N = n / d := by
  rw [abundancy, div_eq_div_iff (by exact_mod_cast hN.ne') (by exact_mod_cast hd.ne')]
  have : ((d * σ 1 N : ℕ) : ℚ) = ((n * N : ℕ) : ℚ) := by rw [hσ]
  push_cast at this
  linarith

/-- The product of `1 - 1/p` over all prime factors is below `d/n`. -/
private theorem prod_lt_d_div_n (hN1 : 1 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N) :
    ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ)) < d / n := by
  have hn := n_pos (by omega) hd hσ
  have hab := abundancy_eq (by omega) hd hσ
  rw [abundancy_eq_prod_primeFactors (by omega)] at hab
  have key : (∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ))) * (n / d) < 1 := by
    rw [← hab, ← prod_mul_distrib]
    have : ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ)) * abundancy (p ^ N.factorization p) =
        ∏ p ∈ N.primeFactors, (1 - 1 / ((p ^ (N.factorization p + 1) : ℕ) : ℚ)) :=
      prod_congr rfl (fun p hp => by
        rw [mul_comm, abundancy_mul_one_sub (Nat.prime_of_mem_primeFactors hp)])
    rw [this]
    calc _ < ∏ p ∈ N.primeFactors, (1 : ℚ) := by
          apply prod_lt_prod_of_nonempty
          · intro p hp
            exact one_sub_inv_pos (le_trans (two_le_of_mem hp)
              (Nat.le_self_pow (by omega) p))
          · intro p hp
            have : (0 : ℚ) < ((p ^ (N.factorization p + 1) : ℕ) : ℚ) := by
              have := two_le_of_mem hp; positivity
            have : 0 < 1 / ((p ^ (N.factorization p + 1) : ℕ) : ℚ) := by positivity
            linarith
          · exact Nat.nonempty_primeFactors.mpr hN1
      _ = 1 := prod_const_one
  have hnd : (0 : ℚ) < n / d := by
    have : (0 : ℚ) < n := by exact_mod_cast hn
    have : (0 : ℚ) < d := by exact_mod_cast hd
    positivity
  rw [← lt_div_iff₀ hnd, one_div_div] at key
  exact key

/-- Prime power components over a subset of the prime factors. -/
private theorem prod_pp_le (hN : 0 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N) {R : Finset ℕ}
    (hR : R ⊆ N.primeFactors) :
    ∏ p ∈ R, (1 - 1 / ((p ^ (N.factorization p + 1) : ℕ) : ℚ)) ≤
      (n / d) * ∏ p ∈ R, (1 - 1 / (p : ℚ)) := by
  have hab := abundancy_eq hN hd hσ
  rw [abundancy_eq_prod_primeFactors (by omega)] at hab
  have e : ∏ p ∈ R, (1 - 1 / ((p ^ (N.factorization p + 1) : ℕ) : ℚ)) =
      (∏ p ∈ R, abundancy (p ^ N.factorization p)) * ∏ p ∈ R, (1 - 1 / (p : ℚ)) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun p hp => by
      rw [abundancy_mul_one_sub (Nat.prime_of_mem_primeFactors (hR hp))])
  rw [e, ← hab]
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun p hp =>
    (one_sub_inv_pos (two_le_of_mem (hR hp))).le))
  rw [← prod_sdiff hR]
  have h1 : ∀ p ∈ N.primeFactors, 1 ≤ abundancy (p ^ N.factorization p) := fun p hp => by
    have hp' := Nat.prime_of_mem_primeFactors hp
    have := one_add_inv_le_abundancy_prime_pow hp'
      (hp'.factorization_pos_of_dvd hN.ne' (Nat.dvd_of_mem_primeFactors hp))
    have : (0 : ℚ) ≤ (p : ℚ)⁻¹ := by positivity
    linarith
  have h0 : ∀ p ∈ N.primeFactors, 0 ≤ abundancy (p ^ N.factorization p) := fun p hp =>
    le_trans zero_le_one (h1 p hp)
  have : 1 ≤ ∏ p ∈ N.primeFactors \ R, abundancy (p ^ N.factorization p) := by
    calc (1 : ℚ) = ∏ p ∈ N.primeFactors \ R, (1 : ℚ) := prod_const_one.symm
      _ ≤ _ := prod_le_prod (fun _ _ => zero_le_one)
          (fun p hp => h1 p (sdiff_subset hp))
  have hpos : 0 ≤ ∏ p ∈ R, abundancy (p ^ N.factorization p) :=
    prod_nonneg (fun p hp => h0 p (hR hp))
  nlinarith

/-- Parity: no product of `1 - 1/p` over prime factors equals `d/n`. -/
private theorem prod_ne_d_div_n (hodd : Odd N) (hN1 : 1 < N) (hd : 0 < d)
    (hσ : d * σ 1 N = n * N)
    {R : Finset ℕ} (hR : R ⊆ N.primeFactors) :
    ∏ p ∈ R, (1 - 1 / (p : ℚ)) ≠ d / n := by
  intro h
  have hn := n_pos (by omega) hd hσ
  have h2R : ∀ p ∈ R, 2 ≤ p := fun p hp => two_le_of_mem (hR hp)
  rw [prod_one_sub_inv_eq h2R] at h
  have hPR : 0 < ∏ p ∈ R, p := prod_pos (fun p hp => by have := h2R p hp; omega)
  rw [div_eq_div_iff (by exact_mod_cast hPR.ne') (by exact_mod_cast hn.ne')] at h
  have hE : (∏ p ∈ R, (p - 1)) * n = d * ∏ p ∈ R, p := by exact_mod_cast h
  have hE2 : (∏ p ∈ R, (p - 1)) * σ 1 N = (∏ p ∈ R, p) * N := by
    apply Nat.eq_of_mul_eq_mul_left hd
    calc d * ((∏ p ∈ R, (p - 1)) * σ 1 N) = (∏ p ∈ R, (p - 1)) * (d * σ 1 N) := by ring
      _ = (∏ p ∈ R, (p - 1)) * n * N := by rw [hσ]; ring
      _ = d * ((∏ p ∈ R, p) * N) := by rw [hE]; ring
  have hNodd : ¬ 2 ∣ N := hodd.not_two_dvd_nat
  have hpodd : ∀ p ∈ R, ¬ 2 ∣ p := fun p hp h2 => by
    have hp' := Nat.prime_of_mem_primeFactors (hR hp)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp h2
    subst this
    exact hNodd (Nat.dvd_of_mem_primeFactors (hR hp))
  have hodd2 : ¬ 2 ∣ (∏ p ∈ R, p) * N := by
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · obtain ⟨p, hp, h2p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp h
      exact hpodd p hp h2p
    · exact hNodd h
  rcases R.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp only [prod_empty, one_mul] at hE2
    have := succ_le_sigma hN1
    omega
  · have h2p : 2 ∣ p - 1 := by have := hpodd p hp; omega
    exact hodd2 (hE2 ▸ dvd_mul_of_dvd_left (dvd_trans h2p (dvd_prod_of_mem (fun q => q - 1) hp)) _)

/-- One step of the Heath-Brown and Nielsen algorithm. -/
private theorem step (hodd : Odd N) (hN1 : 1 < N) (hd : 0 < d) (hσ : d * σ 1 N = n * N)
    {S : Finset ℕ} (hS : S ⊆ N.primeFactors) :
    ∃ W T : Finset ℕ, ∃ w : ℕ, W ⊆ N.primeFactors ∧ W.Nonempty ∧ T ⊆ N.primeFactors \ W ∧
      T.card + W.card = S.card + w ∧
      d * σ 1 (∏ p ∈ W, p ^ N.factorization p) * ∏ p ∈ T, p + 1 ≤
        (d * ∏ p ∈ S, p + 1) ^ (2 ^ (w + W.card)) := by
  classical
  have hN0 : 0 < N := by omega
  have hn := n_pos hN0 hd hσ
  have h2P : ∀ p ∈ N.primeFactors, 2 ≤ p := fun p hp => two_le_of_mem hp
  -- Step A: extend `S` by an initial segment of the remaining primes.
  have hPS : 0 < ∏ p ∈ S, p := prod_pos (fun p hp => by have := h2P p (hS hp); omega)
  have hUS : 0 < ∏ p ∈ S, (p - 1) := prod_pos (fun p hp => by have := h2P p (hS hp); omega)
  have hcS := prod_one_sub_inv_eq (fun p hp => h2P p (hS hp))
  have hcSpos : 0 < ∏ p ∈ S, (1 - 1 / (p : ℚ)) :=
    prod_pos (fun p hp => one_sub_inv_pos (h2P p (hS hp)))
  have hF3 := prod_lt_d_div_n hN1 hd hσ
  rw [← prod_sdiff hS] at hF3
  have hfrac1 : ((d * ∏ p ∈ S, p : ℕ) : ℚ) / ((n * ∏ p ∈ S, (p - 1) : ℕ) : ℚ) =
      ((d : ℚ) / n) / ∏ p ∈ S, (1 - 1 / (p : ℚ)) := by
    rw [hcS]
    have : ((∏ p ∈ S, (p - 1) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hUS.ne'
    have : ((∏ p ∈ S, p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hPS.ne'
    have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have hQ : ∏ p ∈ N.primeFactors \ S, (1 - 1 / (p : ℚ)) ≤
      ((d * ∏ p ∈ S, p : ℕ) : ℚ) / ((n * ∏ p ∈ S, (p - 1) : ℕ) : ℚ) := by
    rw [hfrac1, le_div_iff₀ hcSpos]; exact hF3.le
  obtain ⟨S', hS'sub, hS'le, hS'bd⟩ :=
    select (Nat.mul_pos hd hPS) (fun p hp => h2P p (sdiff_subset hp)) hQ
  rw [hfrac1, le_div_iff₀ hcSpos] at hS'le
  have hdisj : Disjoint S S' :=
    disjoint_left.mpr (fun p hpS hpS' => (mem_sdiff.mp (hS'sub hpS')).2 hpS)
  set R := S ∪ S' with hR
  have hRP : R ⊆ N.primeFactors := union_subset hS (fun p hp => sdiff_subset (hS'sub hp))
  have hRlt : ∏ p ∈ R, (1 - 1 / (p : ℚ)) < d / n :=
    lt_of_le_of_ne (by rw [prod_union hdisj, mul_comm]; exact hS'le)
      (prod_ne_d_div_n hodd hN1 hd hσ hRP)
  have hRbd : d * ∏ p ∈ R, p < (d * ∏ p ∈ S, p + 1) ^ (2 ^ S'.card) := by
    rw [prod_union hdisj, ← mul_assoc]; exact hS'bd
  -- Step B: select prime power components among the primes of `R`.
  have h2R : ∀ p ∈ R, 2 ≤ p := fun p hp => h2P p (hRP hp)
  have hPR : 0 < ∏ p ∈ R, p := prod_pos (fun p hp => by have := h2R p hp; omega)
  have hUR : 0 < ∏ p ∈ R, (p - 1) := prod_pos (fun p hp => by have := h2R p hp; omega)
  have hcR := prod_one_sub_inv_eq h2R
  set d'' := d * ∏ p ∈ R, p with hd''
  set n'' := n * ∏ p ∈ R, (p - 1) with hn''
  have hn''pos : 0 < n'' := Nat.mul_pos hn hUR
  have hd''pos : 0 < d'' := Nat.mul_pos hd hPR
  have hnd'' : n'' < d'' := by
    rw [hcR, div_lt_div_iff₀ (by exact_mod_cast hPR) (by exact_mod_cast hn)] at hRlt
    have : (∏ p ∈ R, (p - 1)) * n < d * ∏ p ∈ R, p := by exact_mod_cast hRlt
    rw [hn'', mul_comm]; exact this
  set f : ℕ → ℕ := fun p => p ^ (N.factorization p + 1) with hf
  have hinj : Set.InjOn f R := by
    intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors (hRP hp)
    have hq' := Nat.prime_of_mem_primeFactors (hRP hq)
    have : p ∣ q ^ (N.factorization q + 1) := by
      have h' : f p = f q := hpq
      simp only [hf] at h'
      rw [← h']; exact dvd_pow_self p (Nat.succ_ne_zero _)
    exact (Nat.prime_dvd_prime_iff_eq hp' hq').mp (hp'.dvd_of_dvd_pow this)
  have h2F : ∀ x ∈ R.image f, 2 ≤ x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    exact le_trans (h2R p hp) (Nat.le_self_pow (Nat.succ_ne_zero _) p)
  have hFle : ∏ x ∈ R.image f, (1 - 1 / (x : ℚ)) ≤ (n'' : ℚ) / d'' := by
    rw [prod_image hinj]
    refine le_trans (prod_pp_le hN0 hd hσ hRP) (le_of_eq ?_)
    rw [hcR, hn'', hd'']
    have : ((∏ p ∈ R, p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hPR.ne'
    have : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
  obtain ⟨G, hGF, hGle, hGbd⟩ := select hn''pos h2F hFle
  set W := R.filter (fun p => f p ∈ G) with hW
  have hWR : W ⊆ R := filter_subset _ _
  have hGW : G = W.image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := mem_image.mp (hGF hx)
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hx⟩, rfl⟩
    · intro hx
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hp).2
  have hinjW : Set.InjOn f W := hinj.mono (fun x hx => hWR hx)
  have hGcard : G.card = W.card := by rw [hGW]; exact card_image_of_injOn hinjW
  have hGprodQ : ∏ x ∈ G, (1 - 1 / (x : ℚ)) = ∏ p ∈ W, (1 - 1 / ((f p : ℕ) : ℚ)) := by
    rw [hGW]; exact prod_image hinjW
  have hGprodN : ∏ x ∈ G, x = ∏ p ∈ W, f p := by rw [hGW]; exact prod_image hinjW
  have hWne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with h | h
    · exfalso
      have hG0 : G = ∅ := by rw [hGW, h, image_empty]
      rw [hG0, prod_empty, le_div_iff₀ (by exact_mod_cast hd''pos), one_mul] at hGle
      have : (d'' : ℚ) ≤ n'' := hGle
      have : d'' ≤ n'' := by exact_mod_cast this
      omega
    · exact h
  -- Step C: the new denominator and the new set of known primes.
  have hσV : σ 1 (∏ p ∈ W, p ^ N.factorization p) = ∏ p ∈ W, σ 1 (p ^ N.factorization p) :=
    isMultiplicative_sigma.map_prod _ W (fun p hp q hq hpq =>
      Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors (hRP (hWR hp)))
        (Nat.prime_of_mem_primeFactors (hRP (hWR hq))) hpq)
  have hRsplit : (∏ p ∈ R, (p : ℚ)) = (∏ p ∈ R \ W, (p : ℚ)) * ∏ p ∈ W, (p : ℚ) :=
    (prod_sdiff hWR).symm
  have hW1 : (1 : ℚ) ≤ (∏ p ∈ W, (p : ℚ)) * ∏ p ∈ W, ((p : ℚ) - 1) := by
    rw [← prod_mul_distrib]
    calc (1 : ℚ) = ∏ p ∈ W, (1 : ℚ) := prod_const_one.symm
      _ ≤ _ := prod_le_prod (fun _ _ => zero_le_one) (fun p hp => by
          have : (2 : ℚ) ≤ p := by exact_mod_cast h2R p (hWR hp)
          nlinarith)
  have hsig2 : (∏ p ∈ W, ((σ 1 (p ^ N.factorization p) : ℕ) : ℚ)) * ∏ p ∈ W, ((p : ℚ) - 1) =
      (∏ p ∈ W, ((f p : ℕ) : ℚ)) * ∏ p ∈ W, (1 - 1 / ((f p : ℕ) : ℚ)) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl (fun p hp => ?_)
    rw [sigma_mul_sub_one (Nat.prime_of_mem_primeFactors (hRP (hWR hp)))]
    have : ((f p : ℕ) : ℚ) ≠ 0 := by
      have := h2R p (hWR hp)
      have : 0 < f p := by simp only [hf]; positivity
      exact_mod_cast this.ne'
    simp only [hf] at this ⊢
    push_cast at this ⊢
    field_simp
  have hGle' : ∏ p ∈ W, (1 - 1 / ((f p : ℕ) : ℚ)) ≤ (n'' : ℚ) / d'' := hGprodQ ▸ hGle
  have hkey : d * σ 1 (∏ p ∈ W, p ^ N.factorization p) * ∏ p ∈ R \ W, p ≤
      n'' * ∏ p ∈ W, f p := by
    have hd''Q : (d'' : ℚ) = d * ((∏ p ∈ R \ W, (p : ℚ)) * ∏ p ∈ W, (p : ℚ)) := by
      rw [hd'', ← hRsplit]; push_cast; ring
    have hd''0 : (0 : ℚ) < d'' := by exact_mod_cast hd''pos
    have h0 : (0 : ℚ) ≤ d * (∏ p ∈ W, ((σ 1 (p ^ N.factorization p) : ℕ) : ℚ)) *
        ∏ p ∈ R \ W, (p : ℚ) := by positivity
    have hX0 : (0 : ℚ) ≤ d'' * ∏ p ∈ W, ((f p : ℕ) : ℚ) := by positivity
    have : ((d * σ 1 (∏ p ∈ W, p ^ N.factorization p) * ∏ p ∈ R \ W, p : ℕ) : ℚ) ≤
        ((n'' * ∏ p ∈ W, f p : ℕ) : ℚ) := by
      rw [hσV]
      push_cast
      calc (d : ℚ) * (∏ p ∈ W, ((σ 1 (p ^ N.factorization p) : ℕ) : ℚ)) * ∏ p ∈ R \ W, (p : ℚ)
          ≤ (d : ℚ) * (∏ p ∈ W, ((σ 1 (p ^ N.factorization p) : ℕ) : ℚ)) *
              (∏ p ∈ R \ W, (p : ℚ)) * ((∏ p ∈ W, (p : ℚ)) * ∏ p ∈ W, ((p : ℚ) - 1)) :=
            le_mul_of_one_le_right h0 hW1
        _ = (d'' : ℚ) * ((∏ p ∈ W, ((σ 1 (p ^ N.factorization p) : ℕ) : ℚ)) *
              ∏ p ∈ W, ((p : ℚ) - 1)) := by rw [hd''Q]; ring
        _ = (d'' : ℚ) * (∏ p ∈ W, ((f p : ℕ) : ℚ)) * ∏ p ∈ W, (1 - 1 / ((f p : ℕ) : ℚ)) := by
            rw [hsig2]; ring
        _ ≤ (d'' : ℚ) * (∏ p ∈ W, ((f p : ℕ) : ℚ)) * ((n'' : ℚ) / d'') :=
            mul_le_mul_of_nonneg_left hGle' hX0
        _ = (n'' : ℚ) * ∏ p ∈ W, ((f p : ℕ) : ℚ) := by field_simp
    exact_mod_cast this
  have hGbd' : n'' * ∏ p ∈ W, f p < (n'' + 1) ^ (2 ^ W.card) := by
    rw [← hGprodN, ← hGcard]; exact hGbd
  refine ⟨W, R \ W, S'.card, hWR.trans hRP, hWne, fun p hp => ?_, ?_, ?_⟩
  · obtain ⟨hpR, hpW⟩ := mem_sdiff.mp hp
    exact mem_sdiff.mpr ⟨hRP hpR, hpW⟩
  · rw [card_sdiff_add_card_eq_card hWR, hR, card_union_of_disjoint hdisj]
  · calc _ ≤ (n'' + 1) ^ (2 ^ W.card) := by omega
      _ ≤ d'' ^ (2 ^ W.card) := Nat.pow_le_pow_left hnd'' _
      _ ≤ ((d * ∏ p ∈ S, p + 1) ^ (2 ^ S'.card)) ^ (2 ^ W.card) :=
          Nat.pow_le_pow_left hRbd.le _
      _ = _ := by rw [← pow_mul, ← pow_add]

end Step

/-- Nielsen's Theorem 1 in the form used for induction (Heath-Brown's algorithm): if `N` is odd
with `k` distinct prime factors, `d σ(N) = n N` with `d > 0`, and `S` is a set of prime factors
of `N`, then `d N < (d ∏_{p ∈ S} p + 1)^(2^(2k - |S|))`. -/
theorem general : ∀ (k N d n : ℕ) (S : Finset ℕ), N.primeFactors.card = k → Odd N → 0 < d →
    d * σ 1 N = n * N → S ⊆ N.primeFactors →
    d * N < (d * ∏ p ∈ S, p + 1) ^ (2 ^ (2 * k - S.card)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro N d n S hk hodd hd hσ hS
  classical
  have hN0 : 0 < N := hodd.pos
  rcases Nat.lt_or_ge 1 N with hN1 | hN1
  swap
  · have h1 : N = 1 := by omega
    subst h1
    have hS0 : S = ∅ := subset_empty.mp (by simpa using hS)
    subst hS0
    simp at hk
    subst hk
    simp
  obtain ⟨W, T, w, hWP, hWne, hTP, hcardT, hbd⟩ := step hodd hN1 hd hσ hS
  set P := N.primeFactors with hP
  set V := ∏ p ∈ W, p ^ N.factorization p with hV
  set U := ∏ p ∈ P \ W, p ^ N.factorization p with hU
  have hNVU : N = V * U := by
    rw [mul_comm, hV, hU, prod_sdiff hWP]
    exact Nat.prod_primeFactors_pow_factorization hN0.ne'
  have hcop : Nat.Coprime V U := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    have hpq : p ≠ q := fun h => (mem_sdiff.mp hq).2 (h ▸ hp)
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors (hWP hp))
      (Nat.prime_of_mem_primeFactors (sdiff_subset hq)) hpq
  have hU0 : U ≠ 0 := by
    rw [hU]
    exact prod_ne_zero_iff.mpr (fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (sdiff_subset hp)).ne_zero)
  have hUpf : U.primeFactors = P \ W := by
    ext p
    constructor
    · intro hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp'.prime _).mp
        (Nat.dvd_of_mem_primeFactors hp)
      have hq' := Nat.prime_of_mem_primeFactors (sdiff_subset hq)
      have := (Nat.prime_dvd_prime_iff_eq hp' hq').mp (hp'.dvd_of_dvd_pow hpq)
      exact this ▸ hq
    · intro hp
      have hpP := sdiff_subset hp
      have hp' := Nat.prime_of_mem_primeFactors hpP
      have he : N.factorization p ≠ 0 :=
        (hp'.factorization_pos_of_dvd hN0.ne' (Nat.dvd_of_mem_primeFactors hpP)).ne'
      exact Nat.mem_primeFactors.mpr ⟨hp', dvd_trans (dvd_pow_self p he)
        (dvd_prod_of_mem (fun q => q ^ N.factorization q) hp), hU0⟩
  have hoddU : Odd U := (Nat.odd_mul.mp (hNVU ▸ hodd)).2
  have hσN : σ 1 N = σ 1 V * σ 1 U := by
    rw [hNVU]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
  have hσU : (d * σ 1 V) * σ 1 U = (n * V) * U := by
    calc (d * σ 1 V) * σ 1 U = d * σ 1 N := by rw [hσN]; ring
      _ = n * N := hσ
      _ = (n * V) * U := by rw [hNVU]; ring
  have hV0 : V ≠ 0 := by
    intro h; rw [h, zero_mul] at hNVU; omega
  have hVσ : V ≤ σ 1 V := by
    rw [sigma_one_apply]
    exact single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self V hV0)
  have hδ : 0 < d * σ 1 V := Nat.mul_pos hd (lt_of_lt_of_le (Nat.pos_of_ne_zero hV0) hVσ)
  have hWcard : W.card ≤ k := hk ▸ card_le_card hWP
  have hWpos : 0 < W.card := card_pos.mpr hWne
  have hPW : (P \ W).card + W.card = k := by rw [card_sdiff_add_card_eq_card hWP, hk]
  have hTcard : T.card ≤ (P \ W).card := card_le_card hTP
  have hUcard : U.primeFactors.card = k - W.card := by rw [hUpf]; omega
  have hIH := IH (k - W.card) (by omega) U (d * σ 1 V) (n * V) T hUcard hoddU hδ hσU
    (hUpf ▸ hTP)
  have hexp : w + W.card + (2 * (k - W.card) - T.card) = 2 * k - S.card := by omega
  calc d * N = d * V * U := by rw [hNVU]; ring
    _ ≤ d * σ 1 V * U := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hVσ)
    _ < (d * σ 1 V * ∏ p ∈ T, p + 1) ^ (2 ^ (2 * (k - W.card) - T.card)) := hIH
    _ ≤ ((d * ∏ p ∈ S, p + 1) ^ (2 ^ (w + W.card))) ^ (2 ^ (2 * (k - W.card) - T.card)) :=
        Nat.pow_le_pow_left hbd _
    _ = _ := by rw [← pow_mul, ← pow_add, hexp]

end OddPerfect.UpperBound

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Nielsen 2003, Theorem 1: an odd number `N` with `σ(N)/N = n/d` and `k` distinct prime
factors satisfies `d N < (d + 1)^(4^k)`. -/
theorem mul_lt_succ_pow_four_pow {N d n : ℕ} (hodd : Odd N) (hd : 0 < d)
    (hσ : d * σ 1 N = n * N) : d * N < (d + 1) ^ (4 ^ N.primeFactors.card) := by
  have h := UpperBound.general _ N d n ∅ rfl hodd hd hσ (Finset.empty_subset _)
  simpa [pow_mul] using h

/-- Nielsen 2003: an odd perfect number with `k` distinct prime factors is below `2^(4^k)`. -/
theorem lt_two_pow_four_pow {N : ℕ} (h : OddPerfect N) :
    N < 2 ^ (4 ^ N.primeFactors.card) := by
  have := mul_lt_succ_pow_four_pow (n := 2) h.odd one_pos (by rw [h.sigma_eq]; ring)
  simpa using this

/-- Heath-Brown 1994: an odd perfect number with `k` distinct prime factors is below
`4^(4^k)`. -/
theorem lt_four_pow_four_pow {N : ℕ} (h : OddPerfect N) :
    N < 4 ^ (4 ^ N.primeFactors.card) :=
  lt_of_lt_of_le (lt_two_pow_four_pow h)
    (Nat.pow_le_pow_left (by norm_num) _)

end OddPerfect

#print axioms OddPerfect.UpperBound.cook_lemma
#print axioms OddPerfect.UpperBound.select
#print axioms OddPerfect.UpperBound.general
#print axioms OddPerfect.mul_lt_succ_pow_four_pow
#print axioms OddPerfect.lt_two_pow_four_pow
#print axioms OddPerfect.lt_four_pow_four_pow
