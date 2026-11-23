import OddPerfect.EisensteinInt

/-!
# A 2-adic uniqueness lemma for powers of an Eisenstein integer `z ≡ 1 (mod 4)`

We work in `QuadraticAlgebra ℤ (-1) (-1)`, the Eisenstein integers `a + b ω` with
`ω ^ 2 = -1 - ω`. For `z ≡ 1 (mod 4)`, `z ≠ 1`, and the linear form `L (a + b ω) = a + ℓ * b`,
the equation `L (z ^ n) = 1` has at most one solution `n ≥ 1`
(`eisenstein_pow_linear_eq_one_unique`). With even `ℓ`, `ℓ'`, solutions for `z` and for
`star z` exclude each other (`eisenstein_pow_linear_star_ne_one`).

Proof: write `z = 1 + 2 ^ h * w` with `h ≥ 2` and `w` not divisible by `2`, expand `z ^ n` by the
binomial theorem and compare 2-adic valuations of the terms.
-/

namespace OddPerfect

open Finset QuadraticAlgebra Polynomial

/-- The linear form `a + b ω ↦ a + ℓ * b`, as an additive map. -/
def eisLin (ℓ : ℤ) : Eis →+ ℤ where
  toFun x := x.re + ℓ * x.im
  map_zero' := by simp
  map_add' x y := by simp only [re_add, im_add]; ring

theorem eisLin_apply (ℓ : ℤ) (x : Eis) : eisLin ℓ x = x.re + ℓ * x.im := rfl

theorem eisLin_intCast_mul (ℓ c : ℤ) (x : Eis) : eisLin ℓ ((c : Eis) * x) = c * eisLin ℓ x := by
  simp only [eisLin_apply, re_mul, im_mul, re_intCast, im_intCast, Int.cast_id]; ring

theorem eisLin_one (ℓ : ℤ) : eisLin ℓ (1 : Eis) = 1 := by
  simp [eisLin_apply]

/-- Binomial expansion of `L ((1 + 2 ^ h * w) ^ n)`, padded to any range `N > n`. -/
private theorem eisLin_pow_expand (ℓ : ℤ) (h : ℕ) (w : Eis) {n N : ℕ} (hN : n < N) :
    eisLin ℓ ((1 + (((2 : ℤ) ^ h : ℤ) : Eis) * w) ^ n) =
      ∑ r ∈ range N, (n.choose r : ℤ) * 2 ^ (h * r) * eisLin ℓ (w ^ r) := by
  rw [add_comm, add_pow, map_sum]
  have hsub : range (n + 1) ⊆ range N := range_subset_range.2 (by omega)
  rw [sum_subset hsub]
  · refine sum_congr rfl fun r _ => ?_
    have : ((((2 : ℤ) ^ h : ℤ) : Eis) * w) ^ r * 1 ^ (n - r) * (n.choose r : Eis)
        = ((((n.choose r : ℤ) * 2 ^ (h * r) : ℤ)) : Eis) * w ^ r := by
      rw [one_pow, mul_one, mul_pow, ← Int.cast_pow, ← pow_mul]
      push_cast; ring
    rw [this, eisLin_intCast_mul]
  · intro r _ hr
    have : n < r := by simp only [mem_range] at hr; omega
    simp [Nat.choose_eq_zero_of_lt this]

/-- Cancel the odd part of `F`: if every power `2 ^ k` dividing `F` satisfies `k + K ≤ e`, and
`2 ^ v ∣ F * X`, then `2 ^ (v + K) ∣ 2 ^ e * X`. -/
private theorem two_pow_dvd_of_mul {F : ℕ} (hF : F ≠ 0) {K e v : ℕ}
    (hk : ∀ k, 2 ^ k ∣ F → k + K ≤ e)
    {X : ℤ} (hX : (2 : ℤ) ^ v ∣ (F : ℤ) * X) : (2 : ℤ) ^ (v + K) ∣ 2 ^ e * X := by
  obtain ⟨s, t, ht, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hF
  have hs := hk s (dvd_mul_right _ _)
  have hcop : IsCoprime ((2 : ℤ) ^ v) (t : ℤ) := by
    have : Nat.Coprime (2 ^ v) t := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 ht)
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  have h1 : (2 : ℤ) ^ v ∣ 2 ^ s * X := by
    refine hcop.dvd_of_dvd_mul_left ?_
    have : ((2 ^ s * t : ℕ) : ℤ) * X = (t : ℤ) * (2 ^ s * X) := by push_cast; ring
    rwa [this] at hX
  have h2 : (2 : ℤ) ^ (v + K) ∣ 2 ^ (s + K) * X := by
    have : (2 : ℤ) ^ (s + K) * X = 2 ^ K * (2 ^ s * X) := by rw [pow_add]; ring
    rw [this, pow_add, mul_comm ((2 : ℤ) ^ v)]
    exact mul_dvd_mul_left _ h1
  exact h2.trans (mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) X)

private theorem lt_of_two_pow_dvd_self {r k : ℕ} (hr : r ≠ 0) (hk : 2 ^ k ∣ r) : k < r := by
  have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hk
  by_contra hc
  have h2 : 2 ^ r ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : r < 2 ^ r := Nat.lt_two_pow_self
  omega

private theorem lt_of_two_pow_dvd_factorial {r k : ℕ} (hr : r ≠ 0)
    (hk : 2 ^ k ∣ r.factorial) : k < r := by
  have h1 := pow_dvd_iff_le_emultiplicity.1 hk
  have h2 := Nat.emultiplicity_two_factorial_lt hr
  exact_mod_cast h1.trans_lt h2

/-- Step 1 on integers: if `∑ C(n, r) 2 ^ (h r) t r = 1` with `t 0 = 1`, `h ≥ 2`, `n ≥ 1`, then
`t 1` is even. -/
private theorem step_one_core (h : ℕ) (hh : 2 ≤ h) (t : ℕ → ℤ) (ht0 : t 0 = 1) {n : ℕ} (hn : 1 ≤ n)
    (hsum : ∑ r ∈ range (n + 2), (n.choose r : ℤ) * 2 ^ (h * r) * t r = 1) : 2 ∣ t 1 := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, f = fun r => (n.choose r : ℤ) * 2 ^ (h * r) * t r := ⟨_, rfl⟩
  have hs : ∑ r ∈ range (n + 2), f r = 1 := by rw [hf]; exact hsum
  rw [sum_range_succ', sum_range_succ'] at hs
  have e0 : f 0 = 1 := by rw [hf]; simp [ht0]
  have e1 : f (0 + 1) = n * 2 ^ h * t 1 := by rw [hf]; simp
  rw [e0, e1] at hs
  obtain ⟨e, k, hk, hnk⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have htail : ∀ i ∈ range n, (2 : ℤ) ^ (e + (h + 1)) ∣ f (i + 1 + 1) := by
    intro i _
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hN : 2 ^ e ∣ (i + 2) * (n' + 1).choose (i + 2) := by
      have := Nat.add_one_mul_choose_eq n' (i + 1)
      refine (show 2 ^ e ∣ n' + 1 from ⟨k, hnk⟩).trans ?_
      rw [mul_comm]
      exact ⟨n'.choose (i + 1), this.symm⟩
    have hZ : (2 : ℤ) ^ e ∣ ((i + 2 : ℕ) : ℤ) * ((n' + 1).choose (i + 2) : ℤ) := by
      have := Int.natCast_dvd_natCast.2 hN
      push_cast at this ⊢
      exact this
    have hb := two_pow_dvd_of_mul (F := i + 2) (K := h + 1) (e := h * (i + 2)) (by omega)
      (fun k hk' => by
        have := lt_of_two_pow_dvd_self (by omega) hk'
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 2 := ⟨h - 2, by omega⟩
        nlinarith) hZ
    rw [hf]
    simp only
    rw [show i + 1 + 1 = i + 2 by ring]
    rw [show ((n' + 1).choose (i + 2) : ℤ) * 2 ^ (h * (i + 2)) * t (i + 2)
      = 2 ^ (h * (i + 2)) * ((n' + 1).choose (i + 2) : ℤ) * t (i + 2) by ring]
    exact dvd_mul_of_dvd_left hb _
  have hd : (2 : ℤ) ^ (e + (h + 1)) ∣ n * 2 ^ h * t 1 := by
    have h1 : (n : ℤ) * 2 ^ h * t 1 = -(∑ i ∈ range n, f (i + 1 + 1)) := by linarith
    rw [h1]
    exact (dvd_neg).2 (dvd_sum htail)
  have h2 : (n : ℤ) * 2 ^ h * t 1 = 2 ^ (e + h) * (k * t 1) := by
    rw [hnk]; push_cast; ring
  rw [h2, show e + (h + 1) = (e + h) + 1 by ring, pow_succ] at hd
  have h3 : (2 : ℤ) ∣ k * t 1 := (mul_dvd_mul_iff_left (by positivity)).1 hd
  rcases Int.prime_two.dvd_or_dvd h3 with h4 | h4
  · have := Int.natCast_dvd_natCast.1 h4
    obtain ⟨j, hj⟩ := hk
    omega
  · exact h4

/-- The identity `r ! * (n C(m, r) - m C(n, r)) = n m (Q m - Q n)` with
`Q = (descPochhammer ℤ j).comp (X - 1)` and `r = j + 1`. -/
private theorem factorial_mul_choose_diff (n m j : ℕ) :
    ((j + 1).factorial : ℤ) * ((n : ℤ) * m.choose (j + 1) - m * n.choose (j + 1)) =
      n * m * (((descPochhammer ℤ j).comp (X - 1)).eval (m : ℤ) -
        ((descPochhammer ℤ j).comp (X - 1)).eval (n : ℤ)) := by
  have hd : ∀ a : ℕ, ((j + 1).factorial : ℤ) * (a.choose (j + 1) : ℤ) =
      a * ((descPochhammer ℤ j).comp (X - 1)).eval (a : ℤ) := by
    intro a
    have := descPochhammer_eval_eq_descFactorial (R := ℤ) a (j + 1)
    rw [descPochhammer_succ_left, eval_mul, eval_X] at this
    rw [this, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  linear_combination (n : ℤ) * hd m - (m : ℤ) * hd n

/-- Step 2 on integers: if both sums for `n < m` equal `1`, with `t 0 = 1`, `h ≥ 2`, `n ≥ 1`,
then `t 2` is even. -/
private theorem step_two_core (h : ℕ) (hh : 2 ≤ h) (t : ℕ → ℤ) (ht0 : t 0 = 1) {n m : ℕ}
    (hn : 1 ≤ n) (hnm : n < m)
    (h1 : ∑ r ∈ range (m + 3), (n.choose r : ℤ) * 2 ^ (h * r) * t r = 1)
    (h2 : ∑ r ∈ range (m + 3), (m.choose r : ℤ) * 2 ^ (h * r) * t r = 1) : 2 ∣ t 2 := by
  obtain ⟨g, hgd⟩ : ∃ g : ℕ → ℤ,
      g = fun r => ((n : ℤ) * m.choose r - m * n.choose r) * 2 ^ (h * r) * t r := ⟨_, rfl⟩
  have hg : ∑ r ∈ range (m + 3), g r = n - m := by
    have : ∑ r ∈ range (m + 3), g r =
        (n : ℤ) * ∑ r ∈ range (m + 3), (m.choose r : ℤ) * 2 ^ (h * r) * t r -
          (m : ℤ) * ∑ r ∈ range (m + 3), (n.choose r : ℤ) * 2 ^ (h * r) * t r := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib, hgd]
      exact sum_congr rfl fun r _ => by ring
    rw [this, h1, h2]; ring
  rw [sum_range_succ', sum_range_succ', sum_range_succ'] at hg
  have e0 : g 0 = n - m := by rw [hgd]; simp [ht0]
  have e1 : g (0 + 1) = 0 := by rw [hgd]; simp only [zero_add, Nat.choose_one_right]; ring
  rw [e0, e1] at hg
  -- the integer `D = n m (m - n)`
  set D : ℕ := n * m * (m - n) with hD
  have hD0 : D ≠ 0 := by
    have : 0 < m - n := by omega
    rw [hD]; exact (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) this).ne'
  have hDZ : (D : ℤ) = n * m * ((m : ℤ) - n) := by
    rw [hD]; push_cast [Nat.cast_sub hnm.le]; ring
  obtain ⟨d, k, hk, hDk⟩ := Nat.exists_eq_two_pow_mul_odd hD0
  have h2D : (2 : ℤ) ^ d ∣ n * m * ((m : ℤ) - n) := by
    rw [← hDZ, hDk]; push_cast; exact dvd_mul_right _ _
  -- the term `r = 2`
  have e2 : g (0 + 1 + 1) * 2 = D * 2 ^ (2 * h) * t 2 := by
    have := factorial_mul_choose_diff n m 1
    simp only [descPochhammer_one, X_comp, eval_sub, eval_X, eval_one, Nat.reduceAdd,
      Nat.factorial_two, Nat.cast_ofNat] at this
    rw [hgd, hDZ]
    simp only [zero_add, Nat.reduceAdd]
    rw [show h * 2 = 2 * h by ring]
    linear_combination 2 ^ (2 * h) * t 2 * this
  -- the terms `r ≥ 3`
  have htail : ∀ i ∈ range m, (2 : ℤ) ^ (d + 2 * h) ∣ g (i + 1 + 1 + 1) := by
    intro i _
    have hX := factorial_mul_choose_diff n m (i + 2)
    have hdv : (2 : ℤ) ^ d ∣ ((i + 2 + 1).factorial : ℕ) *
        ((n : ℤ) * m.choose (i + 2 + 1) - m * n.choose (i + 2 + 1)) := by
      rw [hX]
      exact h2D.trans (mul_dvd_mul_left _ (sub_dvd_eval_sub _ _ _))
    have hb := two_pow_dvd_of_mul (F := (i + 2 + 1).factorial) (K := 2 * h) (e := h * (i + 2 + 1))
      (Nat.factorial_ne_zero _)
      (fun k hk' => by
        have := lt_of_two_pow_dvd_factorial (by omega) hk'
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 2 := ⟨h - 2, by omega⟩
        nlinarith) hdv
    rw [hgd]
    simp only
    rw [show i + 1 + 1 + 1 = i + 2 + 1 by ring]
    rw [show ((n : ℤ) * m.choose (i + 2 + 1) - m * n.choose (i + 2 + 1)) *
        2 ^ (h * (i + 2 + 1)) * t (i + 2 + 1) = 2 ^ (h * (i + 2 + 1)) *
        ((n : ℤ) * m.choose (i + 2 + 1) - m * n.choose (i + 2 + 1)) * t (i + 2 + 1) by ring]
    exact dvd_mul_of_dvd_left hb _
  have hsum := dvd_sum htail
  -- combine
  obtain ⟨c, hc⟩ : ∃ c, 2 * h = c + 1 := ⟨2 * h - 1, by omega⟩
  have hmain : (2 : ℤ) ^ (d + 2 * h) * 2 ∣ D * 2 ^ (2 * h) * t 2 := by
    rw [← e2]
    have : g (0 + 1 + 1) = -(∑ i ∈ range m, g (i + 1 + 1 + 1)) := by linarith
    rw [this]
    exact mul_dvd_mul_right ((dvd_neg).2 hsum) 2
  have h5 : (D : ℤ) * 2 ^ (2 * h) * t 2 = (2 ^ (d + 2 * h)) * (k * t 2) := by
    rw [hDk]; push_cast; ring
  rw [h5] at hmain
  have h3 : (2 : ℤ) ∣ k * t 2 := (mul_dvd_mul_iff_left (by positivity)).1 hmain
  rcases Int.prime_two.dvd_or_dvd h3 with h4 | h4
  · have := Int.natCast_dvd_natCast.1 h4
    obtain ⟨j, hj⟩ := hk
    omega
  · exact h4

/-- Step 1: if `L ((1 + 2 ^ h w) ^ n) = 1` with `h ≥ 2`, `n ≥ 1`, then `L w` is even. -/
private theorem step_one (ℓ : ℤ) (h : ℕ) (hh : 2 ≤ h) (w : Eis) {n : ℕ} (hn : 1 ≤ n)
    (h1 : eisLin ℓ ((1 + (((2 : ℤ) ^ h : ℤ) : Eis) * w) ^ n) = 1) : 2 ∣ eisLin ℓ w := by
  rw [eisLin_pow_expand ℓ h w (N := n + 2) (by omega)] at h1
  have := step_one_core h hh (fun r => eisLin ℓ (w ^ r)) (by simp [eisLin_one]) hn h1
  simpa using this

/-- Step 2: two solutions `n < m` of `L ((1 + 2 ^ h w) ^ n) = 1` force `L (w ^ 2)` even. -/
private theorem step_two (ℓ : ℤ) (h : ℕ) (hh : 2 ≤ h) (w : Eis) {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m)
    (h1 : eisLin ℓ ((1 + (((2 : ℤ) ^ h : ℤ) : Eis) * w) ^ n) = 1)
    (h2 : eisLin ℓ ((1 + (((2 : ℤ) ^ h : ℤ) : Eis) * w) ^ m) = 1) : 2 ∣ eisLin ℓ (w ^ 2) := by
  rw [eisLin_pow_expand ℓ h w (N := m + 3) (by omega)] at h1 h2
  exact step_two_core h hh (fun r => eisLin ℓ (w ^ r)) (by simp [eisLin_one]) hn hnm h1 h2

/-- Step 3: `L w` and `L (w ^ 2)` even force both coordinates of `w` even. -/
private theorem step_three (ℓ : ℤ) (w : Eis) (h1 : 2 ∣ eisLin ℓ w) (h2 : 2 ∣ eisLin ℓ (w ^ 2)) :
    2 ∣ w.re ∧ 2 ∣ w.im := by
  have hid : eisLin ℓ (w ^ 2) = (eisLin ℓ w) ^ 2 - (ℓ * (ℓ + 1) + 1) * w.im ^ 2 := by
    simp only [eisLin_apply, pow_two, re_mul, im_mul]; ring
  have h3 : (2 : ℤ) ∣ (ℓ * (ℓ + 1) + 1) * w.im ^ 2 := by
    have := dvd_sub (dvd_pow h1 two_ne_zero) h2
    rw [hid] at this
    simpa using this
  have hb : (2 : ℤ) ∣ w.im := by
    rcases Int.prime_two.dvd_or_dvd h3 with h4 | h4
    · exfalso
      obtain ⟨s, hs⟩ := Int.even_mul_succ_self ℓ
      generalize ℓ * (ℓ + 1) = u at hs h4
      omega
    · exact Int.prime_two.dvd_of_dvd_pow h4
  refine ⟨?_, hb⟩
  have := dvd_sub h1 (dvd_mul_of_dvd_right hb ℓ)
  rw [eisLin_apply] at this
  simpa using this

/-- Write `z ≡ 1 (mod 4)`, `z ≠ 1`, as `1 + 2 ^ h w` with `h ≥ 2` and `w` not divisible by `2`. -/
private theorem eis_decomp {z : Eis} (hz : z ≠ 1) (hre : (4 : ℤ) ∣ z.re - 1)
    (him : (4 : ℤ) ∣ z.im) :
    ∃ h, 2 ≤ h ∧ ∃ w : Eis, z = 1 + (((2 : ℤ) ^ h : ℤ) : Eis) * w ∧ ¬ (2 ∣ w.re ∧ 2 ∣ w.im) := by
  classical
  have key : ∀ x : ℤ, (∀ k : ℕ, (2 : ℤ) ^ k ∣ x) → x = 0 := by
    intro x hx
    by_contra hx0
    have h1 := Int.natAbs_dvd_natAbs.2 (hx x.natAbs)
    rw [Int.natAbs_pow] at h1
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hx0) h1
    have h3 : x.natAbs < 2 ^ x.natAbs := Nat.lt_two_pow_self
    simp at h2
    omega
  have hex : ∃ k : ℕ, ¬ ((2 : ℤ) ^ k ∣ z.re - 1 ∧ (2 : ℤ) ^ k ∣ z.im) := by
    by_contra hall
    push Not at hall
    apply hz
    have hr := key _ fun k => (hall k).1
    have hi := key _ fun k => (hall k).2
    ext
    · simp only [re_one]; omega
    · simpa using hi
  have hk0 := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, (2 : ℤ) ^ k ∣ z.re - 1 ∧ (2 : ℤ) ^ k ∣ z.im :=
    fun k hk => not_not.1 (Nat.find_min hex hk)
  have h3 : 3 ≤ Nat.find hex := by
    by_contra hc
    apply hk0
    have : (2 : ℤ) ^ Nat.find hex ∣ 4 := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    exact ⟨this.trans hre, this.trans him⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hmin (Nat.find hex - 1) (by omega)
  refine ⟨Nat.find hex - 1, by omega, ⟨a, b⟩, ?_, ?_⟩
  · ext
    · simp only [re_add, re_one, re_mul, re_intCast, im_intCast, Int.cast_id]; linarith
    · simp only [im_add, im_one, im_mul, re_intCast, im_intCast, Int.cast_id]; linarith
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    apply hk0
    have he : (2 : ℤ) ^ Nat.find hex = 2 ^ (Nat.find hex - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [he]
    simp only at hc hd
    exact ⟨⟨c, by linear_combination ha + 2 ^ (Nat.find hex - 1) * hc⟩,
      ⟨d, by linear_combination hb + 2 ^ (Nat.find hex - 1) * hd⟩⟩

/-- Let `z ≡ 1 (mod 4)`, `z ≠ 1`, and `L (a + b ω) = a + ℓ * b`. Then `L (z ^ n) = 1` holds for at
most one `n ≥ 1`. -/
theorem eisenstein_pow_linear_eq_one_unique {z : QuadraticAlgebra ℤ (-1) (-1)} (hz : z ≠ 1)
    (hre : (4 : ℤ) ∣ z.re - 1) (him : (4 : ℤ) ∣ z.im) (ℓ : ℤ) {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) (h1 : (z ^ n).re + ℓ * (z ^ n).im = 1)
    (h2 : (z ^ m).re + ℓ * (z ^ m).im = 1) : n = m := by
  obtain ⟨h, hh, w, rfl, hw⟩ := eis_decomp hz hre him
  have L1 : eisLin ℓ _ = 1 := h1
  have L2 : eisLin ℓ _ = 1 := h2
  have hLw := step_one ℓ h hh w hn L1
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact absurd (step_three ℓ w hLw (step_two ℓ h hh w hn hlt L1 L2)) hw
  · exact heq
  · exact absurd (step_three ℓ w hLw (step_two ℓ h hh w hm hgt L2 L1)) hw

/-- With even `ℓ`, `ℓ'`: if `L (z ^ n) = 1` for some `n ≥ 1`, then `L' ((star z) ^ m) = 1` holds
for no `m ≥ 1`. -/
theorem eisenstein_pow_linear_star_ne_one {z : QuadraticAlgebra ℤ (-1) (-1)} (hz : z ≠ 1)
    (hre : (4 : ℤ) ∣ z.re - 1) (him : (4 : ℤ) ∣ z.im) {ℓ ℓ' : ℤ} (hℓ : Even ℓ) (hℓ' : Even ℓ')
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (h1 : (z ^ n).re + ℓ * (z ^ n).im = 1) :
    ((star z) ^ m).re + ℓ' * ((star z) ^ m).im ≠ 1 := by
  obtain ⟨h, hh, w, rfl, hw⟩ := eis_decomp hz hre him
  have L1 : eisLin ℓ _ = 1 := h1
  have hLw := step_one ℓ h hh w hn L1
  rw [eisLin_apply] at hLw
  have ha : (2 : ℤ) ∣ w.re := by
    have := dvd_sub hLw (dvd_mul_of_dvd_left (even_iff_two_dvd.1 hℓ) w.im)
    simpa using this
  intro hc
  have hs : star (1 + (((2 : ℤ) ^ h : ℤ) : Eis) * w) = 1 + (((2 : ℤ) ^ h : ℤ) : Eis) * star w := by
    rw [star_add, star_one, star_mul, star_intCast, mul_comm]
  rw [hs] at hc
  have L2 : eisLin ℓ' _ = 1 := hc
  have hLs := step_one ℓ' h hh (star w) hm L2
  rw [eisLin_apply, re_star, im_star] at hLs
  apply hw
  refine ⟨ha, ?_⟩
  have := dvd_sub (dvd_sub ha hLs) (dvd_mul_of_dvd_left (even_iff_two_dvd.1 hℓ') w.im)
  have e : w.re - (w.re + -1 * w.im + ℓ' * -w.im) - ℓ' * w.im = w.im := by ring
  rwa [e] at this

/-- Public restatement of the binomial expansion of `L ((1 + 2 ^ h * w) ^ n)`. -/
theorem eisLin_pow_expand_range (ℓ : ℤ) (h : ℕ) (w : Eis) {n N : ℕ} (hN : n < N) :
    eisLin ℓ ((1 + (((2 : ℤ) ^ h : ℤ) : Eis) * w) ^ n) =
      ∑ r ∈ range N, (n.choose r : ℤ) * 2 ^ (h * r) * eisLin ℓ (w ^ r) :=
  eisLin_pow_expand ℓ h w hN

/-- Public restatement: cancel the odd part of `F` in a power of `2` dividing `F * X`. -/
theorem two_pow_dvd_of_mul_odd_part {F : ℕ} (hF : F ≠ 0) {K e v : ℕ}
    (hk : ∀ k, 2 ^ k ∣ F → k + K ≤ e)
    {X : ℤ} (hX : (2 : ℤ) ^ v ∣ (F : ℤ) * X) : (2 : ℤ) ^ (v + K) ∣ 2 ^ e * X :=
  two_pow_dvd_of_mul hF hk hX

/-- Public restatement: `z ≡ 1 (mod 4)`, `z ≠ 1`, is `1 + 2 ^ h w` with `h ≥ 2` and `w` not
divisible by `2`. -/
theorem eisenstein_decomp {z : Eis} (hz : z ≠ 1) (hre : (4 : ℤ) ∣ z.re - 1)
    (him : (4 : ℤ) ∣ z.im) :
    ∃ h, 2 ≤ h ∧ ∃ w : Eis, z = 1 + (((2 : ℤ) ^ h : ℤ) : Eis) * w ∧ ¬ (2 ∣ w.re ∧ 2 ∣ w.im) :=
  eis_decomp hz hre him

end OddPerfect

#print axioms OddPerfect.eisenstein_pow_linear_eq_one_unique
#print axioms OddPerfect.eisenstein_pow_linear_star_ne_one
#print axioms OddPerfect.eisLin_pow_expand_range
#print axioms OddPerfect.two_pow_dvd_of_mul_odd_part
#print axioms OddPerfect.eisenstein_decomp
