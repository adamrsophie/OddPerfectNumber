import OddPerfect.FiveExceptionData0
import OddPerfect.FiveExceptionData79
import OddPerfect.FiveExceptionDataT
import OddPerfect.FiveExceptionScan

/-!
# Five exceptional primes when the special prime is 13 and `19 · 31 ∣ N`

Let `N` be an odd perfect number with `3 ∤ N`, special prime 13, and `19 ∣ N`, `31 ∣ N`. Then
at least five prime factors `p ≠ 13` of `N` have an exponent `e` with `3 ∤ e + 1`
(`five_le_card_mod_exceptions_of_thirteen`). The result strengthens the three exception theorem
`four_le_card_mod_exceptions` of this library; whether it is new was not verified against the
literature.

Proof. With at most four such primes, they are `7, 19, 31` and one more prime `t`
(`inst_of_card`), and every other prime factor `s` is good: `1 + s + s^2` is a product of
powers of `7, 13, 19, 31` and, when `t ≡ 1 (mod 3)`, of `t`. Then
`2 ≤ ∏ p/(p - 1)` over `13, 7, 19, 31, t` and the good primes. The good primes whose
`1 + s + s^2` is prime to `t` contribute at most the four hits `5, 11, 191, 653` times
`1/(1 - X0)`, by the enumeration of `FiveExceptionData0` and a quarter power tail. The others
are bounded by the sender scan (`FiveExceptionScan`) for `37 ≤ t < 24500`, by a square root
tail for `t ≥ 24500`, and by two sided interval tables for `t = 17, 67, 79, 307`
(`FiveExceptionDataT`, `FiveExceptionData79`).
-/

open ArithmeticFunction

namespace OddPerfect

namespace FiveException

open ThreeFreeThree (rv one_le_rv)

variable {N t : ℕ}

/-! ## Small lemmas -/

private theorem rv_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ rv p :=
  zero_le_one.trans (one_le_rv hp)

private theorem rv_anti {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) : rv q ≤ rv p := by
  have h1 : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have h2 : (p : ℚ) ≤ q := by exact_mod_cast hpq
  unfold rv
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem abund_nonneg (n : ℕ) : 0 ≤ abundancy n := by unfold abundancy; positivity

private theorem geom_set_le {a : ℚ} (ha : 0 ≤ a) (ha1 : a < 1) (A : Finset ℕ) :
    ∑ k ∈ A, a ^ k ≤ 1 / (1 - a) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range (A.sup id + 1)) ?_
    fun k _ _ => pow_nonneg ha k) (geom_range_le ha ha1 _)
  intro k hk
  have : k ≤ A.sup id := Finset.le_sup (f := id) hk
  exact Finset.mem_range.mpr (by omega)

private theorem geom_set_pos_le {a : ℚ} (ha : 0 ≤ a) (ha1 : a < 1) (A : Finset ℕ)
    (hA : ∀ k ∈ A, 1 ≤ k) : ∑ k ∈ A, a ^ k ≤ a / (1 - a) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Ico 1 (A.sup id + 1)) ?_
    fun k _ _ => pow_nonneg ha k) (geom_Ico_le ha ha1 _)
  intro k hk
  have : k ≤ A.sup id := Finset.le_sup (f := id) hk
  exact Finset.mem_Ico.mpr ⟨hA k hk, by omega⟩

private theorem prod5_le {x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : ℚ} (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂)
    (h₃ : 0 ≤ x₃) (h₄ : 0 ≤ x₄) (h₅ : 0 ≤ x₅) (e₁ : x₁ ≤ y₁) (e₂ : x₂ ≤ y₂) (e₃ : x₃ ≤ y₃)
    (e₄ : x₄ ≤ y₄) (e₅ : x₅ ≤ y₅) : x₁ * x₂ * x₃ * x₄ * x₅ ≤ y₁ * y₂ * y₃ * y₄ * y₅ := by
  have a₁ := h₁.trans e₁
  have a₂ := h₂.trans e₂
  have a₃ := h₃.trans e₃
  have a₄ := h₄.trans e₄
  apply mul_le_mul _ e₅ h₅ (mul_nonneg (mul_nonneg (mul_nonneg a₁ a₂) a₃) a₄)
  apply mul_le_mul _ e₄ h₄ (mul_nonneg (mul_nonneg a₁ a₂) a₃)
  apply mul_le_mul _ e₃ h₃ (mul_nonneg a₁ a₂)
  exact mul_le_mul e₁ e₂ h₂ a₁

theorem Inst.good_two (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) : 2 ≤ s :=
  le_trans (by norm_num) (c.good_ge hs).1

/-- The upper bound `2 ≤ ∏ p/(p - 1)`. -/
theorem Inst.two_le (c : Inst N t) :
    2 ≤ rv 13 * rv 7 * rv 19 * rv 31 * rv t * ∏ s ∈ good N t, rv s := by
  rw [← c.abund]
  have ht2 : 2 ≤ t := (Nat.prime_of_mem_primeFactors c.ht).two_le
  have hP : ∏ s ∈ good N t, abundancy (s ^ N.factorization s) ≤ ∏ s ∈ good N t, rv s :=
    Finset.prod_le_prod₀ (fun s _ => abund_nonneg _) fun s hs =>
      (abundancy_prime_pow_lt (c.good_facts hs).1 _).le
  have l : ∀ p, p.Prime → ∀ k, abundancy (p ^ k) ≤ rv p := fun p hp k =>
    (abundancy_prime_pow_lt hp k).le
  have hP0 : 0 ≤ ∏ s ∈ good N t, abundancy (s ^ N.factorization s) :=
    Finset.prod_nonneg fun s _ => abund_nonneg _
  have r := fun (p : ℕ) (hp : 2 ≤ p) => rv_nonneg hp
  apply mul_le_mul _ hP hP0 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (r 13 (by norm_num))
    (r 7 (by norm_num))) (r 19 (by norm_num))) (r 31 (by norm_num))) (r t ht2))
  exact prod5_le (abund_nonneg _) (abund_nonneg _) (abund_nonneg _) (abund_nonneg _)
    (abund_nonneg _) (l 13 (by norm_num) _) (l 7 (by norm_num) _) (l 19 (by norm_num) _)
    (l 31 (by norm_num) _) (l t (Nat.prime_of_mem_primeFactors c.ht) _)

/-! ## Weight bounds -/

theorem Inst.inv_le4 (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) {a b c' d e K κ : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c') (hd : 0 ≤ d) (he : 0 ≤ e)
    (h7 : 1 ≤ a ^ 4 * 7) (h13 : 1 ≤ b ^ 4 * 13) (h19 : 1 ≤ c' ^ 4 * 19) (h31 : 1 ≤ d ^ 4 * 31)
    (ht : 1 ≤ e ^ 4 * t ∨ (vec t s).2.2.2.2 = 0) (hK : 0 < K)
    (hFK : K ^ 4 ≤ ((1 + s + s ^ 2 : ℕ) : ℚ)) (hκ : 0 ≤ κ)
    (hκF : ((1 + s + s ^ 2 : ℕ) : ℚ) ≤ κ ^ 2 * ((s : ℚ) - 1) ^ 2) :
    1 / ((s : ℚ) - 1) ≤ κ / K * wt5 a b c' d e (vec t s) := by
  have hW := wt5_pow_mul_ge (j := 4) (t := t) (vec t s) h7 h13 h19 h31 ht
  rw [← c.shape hs] at hW
  exact inv_le_of_w4 (c.good_two hs) (wt5_nonneg ha hb hc hd he _) hW hK hFK hκ hκF

theorem Inst.inv_le2 (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) {a b c' d e κ : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c') (hd : 0 ≤ d) (he : 0 ≤ e)
    (h7 : 1 ≤ a ^ 2 * 7) (h13 : 1 ≤ b ^ 2 * 13) (h19 : 1 ≤ c' ^ 2 * 19) (h31 : 1 ≤ d ^ 2 * 31)
    (ht : 1 ≤ e ^ 2 * t ∨ (vec t s).2.2.2.2 = 0) (hκ : 0 ≤ κ)
    (hκF : ((1 + s + s ^ 2 : ℕ) : ℚ) ≤ κ ^ 2 * ((s : ℚ) - 1) ^ 2) :
    1 / ((s : ℚ) - 1) ≤ κ * wt5 a b c' d e (vec t s) := by
  have hW := wt5_pow_mul_ge (j := 2) (t := t) (vec t s) h7 h13 h19 h31 ht
  rw [← c.shape hs] at hW
  exact inv_le_of_w2 (c.good_two hs) (wt5_nonneg ha hb hc hd he _) hW hκ hκF

/-- Sum over good primes whose exponent of `t` is 0. -/
theorem Inst.sum_geom0 (c : Inst N t) (G : Finset ℕ) (hG : G ⊆ good N t) {a b c' d κ : ℚ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hb1 : b < 1) (hc : 0 ≤ c') (hc1 : c' < 1)
    (hd : 0 ≤ d) (hd1 : d < 1) (hκ : 0 ≤ κ) (hz : ∀ s ∈ G, (vec t s).2.2.2.2 = 0)
    (hs : ∀ s ∈ G, 1 / ((s : ℚ) - 1) ≤ κ * wt5 a b c' d 0 (vec t s)) :
    ∑ s ∈ G, 1 / ((s : ℚ) - 1) ≤
      κ * (1 / (1 - a) * (1 / (1 - b)) * (1 / (1 - c')) * (1 / (1 - d)) * 1) := by
  refine le_trans (c.sum_le G hG ha hb hc hd le_rfl hκ hs (G.image fun s => (vec t s).1)
    (G.image fun s => (vec t s).2.1) (G.image fun s => (vec t s).2.2.1)
    (G.image fun s => (vec t s).2.2.2.1) {0} fun s hs => ⟨Finset.mem_image_of_mem _ hs,
      Finset.mem_image_of_mem _ hs, Finset.mem_image_of_mem _ hs, Finset.mem_image_of_mem _ hs,
      by rw [hz s hs]; exact Finset.mem_singleton_self 0⟩) ?_
  apply mul_le_mul_of_nonneg_left _ hκ
  apply prod5_le (Finset.sum_nonneg fun _ _ => pow_nonneg ha _)
    (Finset.sum_nonneg fun _ _ => pow_nonneg hb _) (Finset.sum_nonneg fun _ _ => pow_nonneg hc _)
    (Finset.sum_nonneg fun _ _ => pow_nonneg hd _) (by simp)
    (geom_set_le ha ha1 _) (geom_set_le hb hb1 _) (geom_set_le hc hc1 _) (geom_set_le hd hd1 _)
    (by simp)

/-- Sum over good primes whose exponent of `t` is positive. -/
theorem Inst.sum_geom1 (c : Inst N t) (G : Finset ℕ) (hG : G ⊆ good N t) {a b c' d e κ : ℚ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hb1 : b < 1) (hc : 0 ≤ c') (hc1 : c' < 1)
    (hd : 0 ≤ d) (hd1 : d < 1) (he : 0 ≤ e) (he1 : e < 1) (hκ : 0 ≤ κ)
    (hz : ∀ s ∈ G, 1 ≤ (vec t s).2.2.2.2)
    (hs : ∀ s ∈ G, 1 / ((s : ℚ) - 1) ≤ κ * wt5 a b c' d e (vec t s)) :
    ∑ s ∈ G, 1 / ((s : ℚ) - 1) ≤
      κ * (1 / (1 - a) * (1 / (1 - b)) * (1 / (1 - c')) * (1 / (1 - d)) * (e / (1 - e))) := by
  refine le_trans (c.sum_le G hG ha hb hc hd he hκ hs (G.image fun s => (vec t s).1)
    (G.image fun s => (vec t s).2.1) (G.image fun s => (vec t s).2.2.1)
    (G.image fun s => (vec t s).2.2.2.1) (G.image fun s => (vec t s).2.2.2.2)
    fun s hs => ⟨Finset.mem_image_of_mem _ hs, Finset.mem_image_of_mem _ hs,
      Finset.mem_image_of_mem _ hs, Finset.mem_image_of_mem _ hs,
      Finset.mem_image_of_mem _ hs⟩) ?_
  apply mul_le_mul_of_nonneg_left _ hκ
  apply prod5_le (Finset.sum_nonneg fun _ _ => pow_nonneg ha _)
    (Finset.sum_nonneg fun _ _ => pow_nonneg hb _) (Finset.sum_nonneg fun _ _ => pow_nonneg hc _)
    (Finset.sum_nonneg fun _ _ => pow_nonneg hd _) (Finset.sum_nonneg fun _ _ => pow_nonneg he _)
    (geom_set_le ha ha1 _) (geom_set_le hb hb1 _) (geom_set_le hc hc1 _) (geom_set_le hd hd1 _)
    (geom_set_pos_le he he1 _ fun k hk => by
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk; exact hz s hs)

/-! ## The good primes prime to `t` -/

/-- The tail constant of the receivers `7, 13, 19, 31`. -/
def X0 : ℚ := 2 / 10 ^ 7 * (1 / (1 - 6148 / 10000) * (1 / (1 - 5267 / 10000)) *
  (1 / (1 - 4790 / 10000)) * (1 / (1 - 4238 / 10000)) * 1)

private theorem cast_val4 (a b c d : ℕ) :
    ((7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d : ℕ) : ℚ) = 7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d := by
  push_cast; ring

theorem Inst.val_t0 (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) (hz : (vec t s).2.2.2.2 = 0) :
    1 + s + s ^ 2 = 1 * (7 ^ (vec t s).1 * 13 ^ (vec t s).2.1 * 19 ^ (vec t s).2.2.1 *
      31 ^ (vec t s).2.2.2.1) := by
  rw [c.shape hs, val5, hz]; ring

/-- The good primes prime to `t` outside the hits: `∑ 1/(s - 1) ≤ X0`. -/
theorem Inst.sumG0 (c : Inst N t) (G : Finset ℕ) (hG : G ⊆ good N t)
    (hz : ∀ s ∈ G, (vec t s).2.2.2.2 = 0) (hh : ∀ s ∈ G, s ∉ hits0) :
    ∑ s ∈ G, 1 / ((s : ℚ) - 1) ≤ X0 := by
  unfold X0
  refine c.sum_geom0 G hG (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hz fun s hs => ?_
  have hsg := hG hs
  obtain ⟨h5, h6⟩ := c.good_ge hsg
  have hF : (10 : ℕ) ^ 28 < 1 + s + s ^ 2 := by
    by_contra hle
    have hle' : 1 * (7 ^ (vec t s).1 * 13 ^ (vec t s).2.1 * 19 ^ (vec t s).2.2.1 *
        31 ^ (vec t s).2.2.2.1) ≤ 10 ^ 28 := by
      rw [← c.val_t0 hsg (hz s hs)]; exact not_lt.mp hle
    have := smoothOK4_sound g0_ok _ _ _ _ hle'
    rw [← c.val_t0 hsg (hz s hs)] at this
    exact hh s hs (sqOK_sound this h6 h5)
  have hF' : ((10 : ℚ) ^ 7) ^ 4 ≤ ((1 + s + s ^ 2 : ℕ) : ℚ) := by
    have : ((10 ^ 28 : ℕ) : ℚ) ≤ ((1 + s + s ^ 2 : ℕ) : ℚ) := by exact_mod_cast hF.le
    calc ((10 : ℚ) ^ 7) ^ 4 = ((10 ^ 28 : ℕ) : ℚ) := by norm_num
      _ ≤ _ := this
  exact c.inv_le4 hsg (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inr (hz s hs))
    (by norm_num : (0 : ℚ) < 10 ^ 7) hF' (by norm_num : (0 : ℚ) ≤ 2)
    (cyc_le_four (by omega))

/-- The good primes prime to `t`. -/
def G0 (N t : ℕ) : Finset ℕ := (good N t).filter fun s => (vec t s).2.2.2.2 = 0

/-- The good primes whose `1 + s + s^2` is divisible by `t`. -/
def G1 (N t : ℕ) : Finset ℕ := (good N t).filter fun s => ¬ (vec t s).2.2.2.2 = 0

theorem prod_good_split (N t : ℕ) (f : ℕ → ℚ) :
    ∏ s ∈ good N t, f s = (∏ s ∈ G0 N t, f s) * ∏ s ∈ G1 N t, f s :=
  (Finset.prod_filter_mul_prod_filter_not _ _ f).symm

/-- The product over the good primes prime to `t`. -/
theorem Inst.prodG0 (c : Inst N t) :
    ∏ s ∈ G0 N t, rv s ≤ (∏ s ∈ hits0.toFinset.erase t, rv s) * (1 / (1 - X0)) := by
  have hsub : G0 N t ⊆ good N t := Finset.filter_subset _ _
  rw [← Finset.prod_filter_mul_prod_filter_not (G0 N t) (fun s => s ∈ hits0)]
  have h2 : ∀ s ∈ G0 N t, 2 ≤ s := fun s hs => c.good_two (hsub hs)
  apply mul_le_mul _ _ (Finset.prod_nonneg fun s hs =>
    rv_nonneg (h2 s (Finset.mem_of_mem_filter s hs)))
    (Finset.prod_nonneg fun s hs => rv_nonneg (by
      have := Finset.mem_of_mem_erase hs
      simp [hits0] at this
      omega))
  · apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_erase.mpr ⟨(mem_good.mp (hsub hs1)).2.2.2.2.2, List.mem_toFinset.mpr hs2⟩
    · intro s hs
      exact rv_nonneg (h2 s (Finset.mem_of_mem_filter s hs))
    · intro s hs _
      have := Finset.mem_of_mem_erase hs
      simp [hits0] at this
      exact one_le_rv (by omega)
  · apply prod_rv_le _ (fun s hs => h2 s (Finset.mem_of_mem_filter s hs)) _ (by unfold X0; norm_num)
    apply c.sumG0 _ ((Finset.filter_subset _ _).trans hsub)
    · intro s hs; exact (Finset.mem_filter.mp (Finset.mem_of_mem_filter s hs)).2
    · intro s hs; exact (Finset.mem_filter.mp hs).2

/-! ## Assembling a one sided bound -/

private theorem close_of {A r P0 P1 r' B0 B1 : ℚ} (hA : 0 ≤ A) (hr : 0 ≤ r) (hP0 : 0 ≤ P0)
    (hP1 : 0 ≤ P1) (h2 : 2 ≤ A * r * (P0 * P1)) (hrr : r ≤ r') (h0 : P0 ≤ B0) (h1 : P1 ≤ B1)
    (hfin : A * r' * (B0 * B1) < 2) : False := by
  have hB0 : 0 ≤ B0 := hP0.trans h0
  have : A * r * (P0 * P1) ≤ A * r' * (B0 * B1) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hrr hA) (mul_le_mul h0 h1 hP1 hB0)
      (mul_nonneg hP0 hP1) (mul_nonneg hA (hr.trans hrr))
  linarith

theorem Inst.prodG0_nonneg (c : Inst N t) : 0 ≤ ∏ s ∈ G0 N t, rv s :=
  Finset.prod_nonneg fun s hs => rv_nonneg (c.good_two (Finset.mem_of_mem_filter s hs))

theorem Inst.prodG1_nonneg (c : Inst N t) : 0 ≤ ∏ s ∈ G1 N t, rv s :=
  Finset.prod_nonneg fun s hs => rv_nonneg (c.good_two (Finset.mem_of_mem_filter s hs))

/-- The common shape of the one sided cases. -/
theorem Inst.close1 (c : Inst N t) {r' B1 : ℚ} (hr : rv t ≤ r')
    (h1 : ∏ s ∈ G1 N t, rv s ≤ B1)
    (hfin : rv 13 * rv 7 * rv 19 * rv 31 * r' *
      ((∏ s ∈ hits0.toFinset.erase t, rv s) * (1 / (1 - X0)) * B1) < 2) : False := by
  have h2 := c.two_le
  rw [prod_good_split N t] at h2
  have ht2 : 2 ≤ t := (Nat.prime_of_mem_primeFactors c.ht).two_le
  exact close_of (by unfold rv; norm_num) (rv_nonneg ht2) c.prodG0_nonneg c.prodG1_nonneg h2 hr
    c.prodG0 h1 hfin

/-! ## The fourth prime `t ≡ 2 (mod 3)` -/

theorem Inst.G1_empty (c : Inst N t) (h2 : t % 3 = 2) : G1 N t = ∅ := by
  apply Finset.filter_false_of_mem
  intro s hs
  simp [c.vec_t_zero hs h2]

theorem hits_prod :
    ∏ s ∈ hits0.toFinset, rv s = 5 / 4 * (11 / 10) * (191 / 190) * (653 / 652) := by
  rw [show hits0.toFinset = {5, 11, 191, 653} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  unfold rv
  norm_num

theorem Inst.false_two_big (c : Inst N t) (h2 : t % 3 = 2) (h23 : 23 ≤ t) : False := by
  refine c.close1 (r' := 23 / 22) (B1 := 1) ?_ (by rw [c.G1_empty h2]; simp) ?_
  · have := rv_anti (by norm_num : 2 ≤ 23) h23
    calc rv t ≤ rv 23 := this
      _ = 23 / 22 := by unfold rv; norm_num
  · have hsub : ∏ s ∈ hits0.toFinset.erase t, rv s ≤ ∏ s ∈ hits0.toFinset, rv s :=
      Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.erase_subset _ _) (fun s hs => by
        have := Finset.mem_of_mem_erase hs
        simp [hits0] at this
        exact rv_nonneg (by omega)) fun s hs _ => by
        simp [hits0] at hs
        exact one_le_rv (by omega)
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsub (by unfold X0; norm_num)) zero_le_one)
      (by unfold rv; norm_num)) ?_
    rw [hits_prod]; unfold rv X0; norm_num

theorem Inst.false_five (c : Inst N 5) : False := by
  refine c.close1 (r' := rv 5) (B1 := 1) le_rfl (by rw [c.G1_empty (by norm_num)]; simp) ?_
  rw [show hits0.toFinset.erase 5 = {11, 191, 653} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  unfold rv X0
  norm_num

theorem Inst.false_eleven (c : Inst N 11) : False := by
  refine c.close1 (r' := rv 11) (B1 := 1) le_rfl (by rw [c.G1_empty (by norm_num)]; simp) ?_
  rw [show hits0.toFinset.erase 11 = {5, 191, 653} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  unfold rv X0
  norm_num

/-! ## Interval tables -/

/-- The factor of a hit `h`: its abundancy when `h` is good, else 1. -/
noncomputable def hf (N t h : ℕ) : ℚ :=
  if h ∈ good N t then abundancy (h ^ N.factorization h) else 1

theorem Inst.hit_opt (c : Inst N t) (h : ℕ) :
    ∃ ab ∈ hitOpts h, qv ab.1 ≤ hf N t h ∧ hf N t h ≤ qv ab.2 := by
  unfold hf
  split_ifs with hg
  · have hpr := (c.good_facts hg).1
    rcases c.good_exp hg with e | e
    · refine ⟨(hp h 2, hp h 2), by simp [hitOpts], ?_⟩
      rw [qv_hp hpr, e]
      exact ⟨le_rfl, le_rfl⟩
    · refine ⟨(hp h 8, (h, h - 1)), by simp [hitOpts], ?_⟩
      rw [qv_hp hpr, qv_rv hpr.two_le]
      exact ⟨abundancy_prime_pow_mono hpr e, (abundancy_prime_pow_lt hpr _).le⟩
  · exact ⟨((1, 1), (1, 1)), by simp [hitOpts], by simp [qv]⟩

theorem ge_opt {p e b : ℕ} (hpr : p.Prime) (he : b ≤ e) :
    ∃ ab ∈ geOpts p b, qv ab.1 ≤ abundancy (p ^ e) ∧ abundancy (p ^ e) ≤ qv ab.2 := by
  refine ⟨(hp p b, (p, p - 1)), by simp [geOpts], ?_⟩
  rw [qv_hp hpr, qv_rv hpr.two_le]
  exact ⟨abundancy_prime_pow_mono hpr he, (abundancy_prime_pow_lt hpr _).le⟩

theorem Inst.opt13 (c : Inst N t) : ∃ ab ∈ opts13, qv ab.1 ≤ abundancy (13 ^ N.factorization 13) ∧
    abundancy (13 ^ N.factorization 13) ≤ qv ab.2 := by
  have hpr : (13 : ℕ).Prime := by norm_num
  rcases c.exps.1 with e | e
  · refine ⟨(hp 13 1, hp 13 1), by simp [opts13], ?_⟩
    rw [qv_hp hpr, e]
    exact ⟨le_rfl, le_rfl⟩
  · refine ⟨(hp 13 5, (13, 12)), by simp [opts13], ?_⟩
    rw [qv_hp hpr, show ((13, 12) : ℕ × ℕ) = (13, 13 - 1) from rfl, qv_rv hpr.two_le]
    exact ⟨abundancy_prime_pow_mono hpr e, (abundancy_prime_pow_lt hpr _).le⟩

theorem Inst.opt7 (c : Inst N t) : ∃ ab ∈ opts7, qv ab.1 ≤ abundancy (7 ^ N.factorization 7) ∧
    abundancy (7 ^ N.factorization 7) ≤ qv ab.2 := by
  have hpr : (7 : ℕ).Prime := by norm_num
  rcases c.exps.2.1 with e | e
  · refine ⟨(hp 7 4, hp 7 4), by simp [opts7], ?_⟩
    rw [qv_hp hpr, e]
    exact ⟨le_rfl, le_rfl⟩
  · refine ⟨(hp 7 6, (7, 6)), by simp [opts7], ?_⟩
    rw [qv_hp hpr, show ((7, 6) : ℕ × ℕ) = (7, 7 - 1) from rfl, qv_rv hpr.two_le]
    exact ⟨abundancy_prime_pow_mono hpr e, (abundancy_prime_pow_lt hpr _).le⟩

/-- The product of the abundancies of the good primes outside `H`. -/
noncomputable def restP (N t : ℕ) (H : Finset ℕ) : ℚ :=
  ∏ s ∈ (good N t).filter (· ∉ H), abundancy (s ^ N.factorization s)

/-- A table for the fourth prime `t` with hits `hs` excludes the instance once the remaining good
primes are bounded by `R`. -/
theorem Inst.false_table (c : Inst N t) (hs : List ℕ) (hnd : hs.Nodup) (R : ℕ × ℕ)
    (hR : restP N t hs.toFinset ≤ qv R) (hok : ivOK (tabOf t hs R) (1, 1) (1, 1) = true) :
    False := by
  have ht := Nat.prime_of_mem_primeFactors c.ht
  have hy1 : 1 ≤ restP N t hs.toFinset := by
    have := Finset.prod_le_prod₀ (s := (good N t).filter (· ∉ hs.toFinset))
      (f := fun _ => (1 : ℚ)) (g := fun s => abundancy (s ^ N.factorization s)) (fun _ _ => zero_le_one)
      (fun s hs' => one_le_abundancy_pow (c.good_facts (Finset.mem_of_mem_filter s hs')).1 _)
    simpa [restP] using this
  have hF : List.Forall₂ (fun x o => ∃ ab ∈ o, qv ab.1 ≤ x ∧ x ≤ qv ab.2)
      ([abundancy (13 ^ N.factorization 13), abundancy (7 ^ N.factorization 7),
        abundancy (19 ^ N.factorization 19), abundancy (31 ^ N.factorization 31),
        abundancy (t ^ N.factorization t)] ++ hs.map (hf N t) ++ [restP N t hs.toFinset])
      (tabOf t hs R) := by
    unfold tabOf
    refine List.rel_append (List.rel_append ?_ ?_) ?_
    · refine List.Forall₂.cons c.opt13 (List.Forall₂.cons c.opt7 (List.Forall₂.cons
        (ge_opt (by norm_num) c.exps.2.2.1) (List.Forall₂.cons (ge_opt (by norm_num) c.exps.2.2.2.1)
        (List.Forall₂.cons (ge_opt ht c.exps.2.2.2.2) List.Forall₂.nil))))
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      exact fun h _ => c.hit_opt h
    · exact List.Forall₂.cons ⟨((1, 1), R), by simp, by simpa [qv] using hy1, hR⟩
        List.Forall₂.nil
  refine ivOK_sound _ _ _ hok _ hF 1 (by simp [qv]) (by simp [qv]) ?_
  have hsplit := Finset.prod_filter_mul_prod_filter_not (good N t) (· ∈ hs.toFinset)
    (fun s => abundancy (s ^ N.factorization s))
  have hin : ∏ s ∈ (good N t).filter (· ∈ hs.toFinset), abundancy (s ^ N.factorization s) =
      (hs.map (hf N t)).prod := by
    rw [← List.prod_toFinset _ hnd, Finset.filter_mem_eq_inter, Finset.inter_comm,
      ← Finset.prod_ite_mem]
    rfl
  rw [hin] at hsplit
  have := c.abund
  rw [← hsplit] at this
  simp only [List.prod_append, List.prod_cons, List.prod_nil, one_mul, mul_one]
  rw [← this, restP]
  ring

/-! ## Bounds for the good primes divisible by `t` -/

/-- The weights product of the quarter power tail. -/
def P4 : ℚ := 1 / (1 - 6148 / 10000) * (1 / (1 - 5267 / 10000)) * (1 / (1 - 4790 / 10000)) *
  (1 / (1 - 4238 / 10000))

theorem Inst.val_t1 (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) (hz : 1 ≤ (vec t s).2.2.2.2) :
    1 + s + s ^ 2 = t * t ^ ((vec t s).2.2.2.2 - 1) * (7 ^ (vec t s).1 * 13 ^ (vec t s).2.1 *
      19 ^ (vec t s).2.2.1 * 31 ^ (vec t s).2.2.2.1) := by
  rw [c.shape hs, val5]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hz
  rw [hk, Nat.add_sub_cancel_left]
  ring

/-- The good primes divisible by `t` outside the hits of an enumeration up to `K^4`. -/
theorem Inst.sumG1_pin (c : Inst N t) (G : Finset ℕ) (hG : G ⊆ good N t)
    (hz : ∀ s ∈ G, 1 ≤ (vec t s).2.2.2.2) (hs : List ℕ) (hh : ∀ s ∈ G, s ∉ hs) {K : ℕ}
    (hK0 : 0 < K) (hK : smoothOK (sqOK hs) (K ^ 4) [t, 7, 13, 19, 31] t = true) {u : ℚ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hut : 1 ≤ u ^ 4 * t) :
    ∑ s ∈ G, 1 / ((s : ℚ) - 1) ≤ 2 / K * (P4 * (u / (1 - u))) := by
  have ht1 : 1 ≤ t := (Nat.prime_of_mem_primeFactors c.ht).one_lt.le
  have key := c.sum_geom1 G hG (κ := 2 / K) (a := 6148 / 10000) (b := 5267 / 10000) (c' := 4790 / 10000) (d := 4238 / 10000)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu0 hu1
    (by positivity) hz fun s hs' => ?_
  · refine key.trans (le_of_eq ?_)
    unfold P4
    ring
  have hsg := hG hs'
  obtain ⟨h5, h6⟩ := c.good_ge hsg
  have hF : K ^ 4 < 1 + s + s ^ 2 := by
    by_contra hle
    rw [c.val_t1 hsg (hz s hs')] at hle
    have := smoothOK5_sound ht1 hK _ _ _ _ _ (not_lt.mp hle)
    rw [← c.val_t1 hsg (hz s hs')] at this
    exact hh s hs' (sqOK_sound this h6 h5)
  have hF' : ((K : ℚ)) ^ 4 ≤ ((1 + s + s ^ 2 : ℕ) : ℚ) := by exact_mod_cast hF.le
  exact c.inv_le4 hsg (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl hut)
    (by exact_mod_cast hK0) hF' (by norm_num) (cyc_le_four (by omega))

/-- The remaining good primes of a table, split by divisibility by `t`. -/
theorem Inst.restP_le (c : Inst N t) (H : Finset ℕ) (h0 : ∀ s ∈ hits0, s ∈ H) {X1 : ℚ}
    (hX1 : ∑ s ∈ ((good N t).filter (· ∉ H)).filter (fun s => ¬ (vec t s).2.2.2.2 = 0),
      1 / ((s : ℚ) - 1) ≤ X1) (hX11 : X1 < 1) :
    restP N t H ≤ 1 / (1 - X0) * (1 / (1 - X1)) := by
  have hsub : (good N t).filter (· ∉ H) ⊆ good N t := Finset.filter_subset _ _
  have h2 : ∀ s ∈ (good N t).filter (· ∉ H), 2 ≤ s := fun s hs => c.good_two (hsub hs)
  refine le_trans (Finset.prod_le_prod₀ (fun s _ => abund_nonneg _)
    fun s hs => (abundancy_prime_pow_lt (c.good_facts (hsub hs)).1 _).le) ?_
  rw [← Finset.prod_filter_mul_prod_filter_not ((good N t).filter (· ∉ H))
    (fun s => (vec t s).2.2.2.2 = 0)]
  apply mul_le_mul _ _ (Finset.prod_nonneg fun s hs =>
    rv_nonneg (h2 s (Finset.mem_of_mem_filter s hs))) (by
      have : X0 < 1 := by unfold X0; norm_num
      have : 0 < 1 - X0 := by linarith
      positivity)
  · refine prod_rv_le _ (fun s hs => h2 s (Finset.mem_of_mem_filter s hs)) ?_
      (by unfold X0; norm_num)
    refine c.sumG0 _ ((Finset.filter_subset _ _).trans hsub) (fun s hs => (Finset.mem_filter.mp hs).2)
      fun s hs hm => ?_
    exact (Finset.mem_filter.mp (Finset.mem_of_mem_filter s hs)).2 (h0 s hm)
  · exact prod_rv_le _ (fun s hs => h2 s (Finset.mem_of_mem_filter s hs)) hX1 hX11

/-- The pinned cases `t = 67, 79, 307`. -/
theorem Inst.false_pin (c : Inst N t) (hs hsT : List ℕ) (hnd : hsT.Nodup)
    (h0 : ∀ s ∈ hits0, s ∈ hsT) (h1 : ∀ s ∈ hs, s ∈ hsT) {K : ℕ} (hK0 : 0 < K)
    (hK : smoothOK (sqOK hs) (K ^ 4) [t, 7, 13, 19, 31] t = true) {u : ℚ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hut : 1 ≤ u ^ 4 * t) (R : ℕ × ℕ)
    (hX : 2 / (K : ℚ) * (P4 * (u / (1 - u))) < 1)
    (hR : 1 / (1 - X0) * (1 / (1 - 2 / (K : ℚ) * (P4 * (u / (1 - u))))) ≤ qv R)
    (hok : ivOK (tabOf t hsT R) (1, 1) (1, 1) = true) : False := by
  refine c.false_table hsT hnd R (le_trans (c.restP_le _ (fun s hs' => List.mem_toFinset.mpr
    (h0 s hs')) ?_ hX) hR) hok
  refine c.sumG1_pin _ ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    (fun s hs' => Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hs').2) hs
    (fun s hs' hm => ?_) hK0 hK hu0 hu1 hut
  exact (Finset.mem_filter.mp (Finset.mem_of_mem_filter s hs')).2
    (List.mem_toFinset.mpr (h1 s hm))

/-- The fourth prime 17: no good prime is divisible by 17. -/
theorem Inst.false_seventeen (c : Inst N 17) : False := by
  refine c.false_table hitsT17 (by decide) (6841380936879, 6841355936879) ?_ tab17_ok
  have := c.restP_le hitsT17.toFinset
    (fun s hs => List.mem_toFinset.mpr (by simpa [hits0, hitsT17] using hs)) (X1 := 0) (by
      rw [Finset.sum_eq_zero]
      intro s hs
      exact absurd (c.vec_t_zero ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _) hs)
        (by norm_num)) (Finset.mem_filter.mp hs).2) (by norm_num)
  refine this.trans (le_of_eq ?_)
  simp only [qv, X0]
  norm_num

theorem Inst.false_67 (c : Inst N 67) : False :=
  c.false_pin hits67 hitsT67 (by decide) (by decide) (by decide) (K := 100000) (by norm_num)
    g67_ok (u := 3496 / 10000) (by norm_num) (by norm_num) (by norm_num) _
    (by unfold P4; norm_num) (by unfold P4 X0; simp only [qv]; norm_num) tab67_ok

theorem Inst.false_79 (c : Inst N 79) : False :=
  c.false_pin hits79 hitsT79 (by decide) (by decide) (by decide) (K := 1000000) (by norm_num)
    g79_ok (u := 3355 / 10000) (by norm_num) (by norm_num) (by norm_num) _
    (by unfold P4; norm_num) (by unfold P4 X0; simp only [qv]; norm_num) tab79_ok

theorem Inst.false_307 (c : Inst N 307) : False :=
  c.false_pin hits307 hitsT307 (by decide) (by decide) (by decide) (K := 100000) (by norm_num)
    g307_ok (u := 2389 / 10000) (by norm_num) (by norm_num) (by norm_num) _
    (by unfold P4; norm_num) (by unfold P4 X0; simp only [qv]; norm_num) tab307_ok

/-! ## The sender scan -/

theorem scan_add (P k a b s s' : ℕ) (hk : k = a + b) (hs : s' = s + 6 * a) :
    scan P k s = scan P a s ++ scan P b s' := by
  subst hk hs
  induction a generalizing s with
  | zero => simp [scan]
  | succ a ih =>
    have e := ih (s + 6)
    rw [show s + 6 + 6 * a = s + 6 * (a + 1) by ring] at e
    rw [show a + 1 + b = (a + b) + 1 by ring]
    cases h : sender P s <;> simp [scan, h, e]

theorem scan_full : scan bigP 166666 5 = sendList.map (fun e => (e.1, e.2.1)) := by
  rw [sendList_eq,
    scan_add bigP 166666 10000 156666 5 60005 rfl rfl, scan0,
    scan_add bigP 156666 10000 146666 60005 120005 rfl rfl, scan1,
    scan_add bigP 146666 10000 136666 120005 180005 rfl rfl, scan2,
    scan_add bigP 136666 10000 126666 180005 240005 rfl rfl, scan3,
    scan_add bigP 126666 10000 116666 240005 300005 rfl rfl, scan4,
    scan_add bigP 116666 10000 106666 300005 360005 rfl rfl, scan5,
    scan_add bigP 106666 10000 96666 360005 420005 rfl rfl, scan6,
    scan_add bigP 96666 10000 86666 420005 480005 rfl rfl, scan7,
    scan_add bigP 86666 10000 76666 480005 540005 rfl rfl, scan8,
    scan_add bigP 76666 10000 66666 540005 600005 rfl rfl, scan9,
    scan_add bigP 66666 10000 56666 600005 660005 rfl rfl, scan10,
    scan_add bigP 56666 10000 46666 660005 720005 rfl rfl, scan11,
    scan_add bigP 46666 10000 36666 720005 780005 rfl rfl, scan12,
    scan_add bigP 36666 10000 26666 780005 840005 rfl rfl, scan13,
    scan_add bigP 26666 10000 16666 840005 900005 rfl rfl, scan14,
    scan_add bigP 16666 10000 6666 900005 960005 rfl rfl, scan15,
    scan16]
  simp only [List.append_assoc]

private theorem not_dvd_pow' {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ¬ p ∣ q ^ k := fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h))

private theorem ndvd_mul' {p x y : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y) :
    ¬ p ∣ x * y := fun h => (hp.dvd_mul.mp h).elim hx hy

private theorem exp_le40 {p k m F : ℕ} (hp : 2 ≤ p) (h : p ^ k * m ≤ F) (hm : 0 < m)
    (hF : F < 2 ^ 41) : k ≤ 40 := by
  by_contra hk
  have h1 : 2 ^ 41 ≤ p ^ k :=
    le_trans (Nat.pow_le_pow_left hp 41) (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : p ^ k ≤ p ^ k * m := Nat.le_mul_of_pos_right _ hm
  omega

theorem rem0_of {s a b c d e : ℕ} (ht : t.Prime) (h7 : t ≠ 7) (h13 : t ≠ 13) (h19 : t ≠ 19)
    (h31 : t ≠ 31) (hF : 1 + s + s ^ 2 = 7 ^ a * (13 ^ b * (19 ^ c * (31 ^ d * t ^ e))))
    (hlt : 1 + s + s ^ 2 < 2 ^ 41) : rem0 s = t ^ e := by
  have P7 : (7 : ℕ).Prime := by norm_num
  have P13 : (13 : ℕ).Prime := by norm_num
  have P19 : (19 : ℕ).Prime := by norm_num
  have P31 : (31 : ℕ).Prime := by norm_num
  have n7 : ¬ 7 ∣ 13 ^ b * (19 ^ c * (31 ^ d * t ^ e)) :=
    ndvd_mul' P7 (not_dvd_pow' P7 P13 (by norm_num)) (ndvd_mul' P7 (not_dvd_pow' P7 P19
      (by norm_num)) (ndvd_mul' P7 (not_dvd_pow' P7 P31 (by norm_num))
      (not_dvd_pow' P7 ht (Ne.symm h7))))
  have n13 : ¬ 13 ∣ 19 ^ c * (31 ^ d * t ^ e) :=
    ndvd_mul' P13 (not_dvd_pow' P13 P19 (by norm_num)) (ndvd_mul' P13 (not_dvd_pow' P13 P31
      (by norm_num)) (not_dvd_pow' P13 ht (Ne.symm h13)))
  have n19 : ¬ 19 ∣ 31 ^ d * t ^ e :=
    ndvd_mul' P19 (not_dvd_pow' P19 P31 (by norm_num)) (not_dvd_pow' P19 ht (Ne.symm h19))
  have n31 : ¬ 31 ∣ t ^ e := not_dvd_pow' P31 ht (Ne.symm h31)
  have q1 : 0 < 13 ^ b * (19 ^ c * (31 ^ d * t ^ e)) := by
    have := ht.pos; positivity
  have q2 : 0 < 19 ^ c * (31 ^ d * t ^ e) := by have := ht.pos; positivity
  have q3 : 0 < 31 ^ d * t ^ e := by have := ht.pos; positivity
  have q4 : 0 < t ^ e := by have := ht.pos; positivity
  have l7 : 7 ^ a * (13 ^ b * (19 ^ c * (31 ^ d * t ^ e))) ≤ 1 + s + s ^ 2 := hF.ge
  have l13 : 13 ^ b * (19 ^ c * (31 ^ d * t ^ e)) ≤ 1 + s + s ^ 2 :=
    le_trans (Nat.le_mul_of_pos_left _ (by positivity)) l7
  have l19 : 19 ^ c * (31 ^ d * t ^ e) ≤ 1 + s + s ^ 2 :=
    le_trans (Nat.le_mul_of_pos_left _ (by positivity)) l13
  have l31 : 31 ^ d * t ^ e ≤ 1 + s + s ^ 2 :=
    le_trans (Nat.le_mul_of_pos_left _ (by positivity)) l19
  unfold rem0
  rw [hF, stripF_spec (by norm_num) n7 a 40 (exp_le40 (by norm_num) l7 q1 hlt),
    stripF_spec (by norm_num) n13 b 40 (exp_le40 (by norm_num) l13 q2 hlt),
    stripF_spec (by norm_num) n19 c 40 (exp_le40 (by norm_num) l19 q3 hlt),
    stripF_spec (by norm_num) n31 d 40 (exp_le40 (by norm_num) l31 q4 hlt)]

/-- The sender bound of `t`: the sum of `⌈10^9/(s - 1)⌉` over its prime senders `s`. -/
def cfun (t : ℕ) : ℕ :=
  ((sendList.filter fun e => decide (e.2.1 = t) && decide (e.2.2 = 0)).map
    fun e => (10 ^ 9 + e.1 - 2) / (e.1 - 1)).sum

/-- The fourth primes whose senders are not covered by the uniform bound. -/
def special : List ℕ := [67, 79, 127, 307, 367, 409, 991, 1723, 3541, 5113, 8011, 10303, 17293]

/-- The checked facts about `bigP` and the senders, in one pass over `primesL`. -/
theorem primesL_ok : primesL.all (fun x => decide (bigP % (x * x) ≠ 0) &&
    (decide (x ∈ special) || decide (cfun x ≤ 6756757))) = true := by
  decide +kernel

theorem mem_primesP {p : ℕ} (hp : p.Prime) (h37 : 37 ≤ p) (hlt : p < 24500) (h1 : p % 3 = 1) :
    p ∈ primesP := by
  have h6 : p % 6 = 1 := by
    have := hp.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · have := this ⟨k, by omega⟩; omega
    · omega
  simp only [primesP, List.mem_filter, List.mem_range'_1, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h37, by omega⟩, h6, isPr_of_prime hp hlt⟩

theorem gcd_bigP {p e : ℕ} (hp : p.Prime) (hm : p ∈ primesP) (he : 1 ≤ e) :
    Nat.gcd (p ^ e) bigP = p := by
  have hok := List.all_eq_true.mp primesL_ok p (primesP_eq ▸ hm)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have hdvd : p ∣ bigP := primesP_prod ▸ List.dvd_prod hm
  obtain ⟨k, hk, hg⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ e) bigP)
  have h1 : p ∣ Nat.gcd (p ^ e) bigP := Nat.dvd_gcd (dvd_pow_self p (by omega)) hdvd
  rw [hg] at h1 ⊢
  have k1 : 1 ≤ k := by
    by_contra h0
    rw [show k = 0 by omega, pow_zero] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have k2 : k ≤ 1 := by
    by_contra h2
    have : p * p ∣ bigP := by
      have : p * p ∣ p ^ k := by
        rw [← pow_two]; exact pow_dvd_pow p (by omega)
      exact this.trans (by rw [← hg]; exact Nat.gcd_dvd_right _ _)
    exact hok.1 (Nat.mod_eq_zero_of_dvd this)
  rw [show k = 1 by omega, pow_one]

theorem Inst.sender_eq (c : Inst N t) (h37 : 37 ≤ t) (hlt : t < 24500) (h1 : t % 3 = 1)
    {s : ℕ} (hs : s ∈ good N t) (hz : 1 ≤ (vec t s).2.2.2.2) (hs6 : s < 1000000) :
    sender bigP s = some t := by
  have ht := Nat.prime_of_mem_primeFactors c.ht
  have hF : 1 + s + s ^ 2 < 2 ^ 41 := by
    have : s ^ 2 ≤ 999999 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hshape : 1 + s + s ^ 2 = 7 ^ (vec t s).1 * (13 ^ (vec t s).2.1 * (19 ^ (vec t s).2.2.1 *
      (31 ^ (vec t s).2.2.2.1 * t ^ (vec t s).2.2.2.2))) := by
    rw [c.shape hs, val5]; ring
  have hr := rem0_of ht c.ht7 c.ht13 c.ht19 c.ht31 hshape hF
  have hm := mem_primesP ht h37 hlt h1
  have hg := gcd_bigP ht hm hz
  have hte : t ^ (vec t s).2.2.2.2 < 2 ^ 41 := lt_of_le_of_lt (by
    rw [hshape]
    exact Nat.le_mul_of_pos_left _ (by positivity) |>.trans
      (Nat.le_mul_of_pos_left _ (by positivity)) |>.trans
      (Nat.le_mul_of_pos_left _ (by positivity)) |>.trans
      (Nat.le_mul_of_pos_left _ (by positivity))) hF
  have hlt45 : (vec t s).2.2.2.2 < 45 := by
    by_contra h
    have : 2 ^ 45 ≤ t ^ (vec t s).2.2.2.2 :=
      le_trans (Nat.pow_le_pow_left ht.two_le 45) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hne1 : t ^ (vec t s).2.2.2.2 ≠ 1 := (Nat.one_lt_pow (by omega) ht.one_lt).ne'
  simp only [sender, hr, hg, hne1, if_false, ht.one_lt.ne', show ¬ 24500 ≤ t by omega,
    powOf_spec ht.two_le _ _ hlt45, isPr_of_prime ht hlt, Bool.and_self, if_true]

/-! ## The fourth prime `t ≡ 1 (mod 3)`, `37 ≤ t < 24500` -/

private theorem list_sum_le {α : Type*} (l : List α) (f g : α → ℚ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

private theorem list_sum_div {α : Type*} (l : List α) (c : α → ℕ) :
    (l.map fun e => (c e : ℚ) / 10 ^ 9).sum = ((l.map c).sum : ℚ) / 10 ^ 9 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, add_div]

private theorem inv_le_ceil (s : ℕ) :
    1 / ((s : ℚ) - 1) ≤ (((10 ^ 9 + s - 2) / (s - 1) : ℕ) : ℚ) / 10 ^ 9 := by
  rcases lt_or_ge s 2 with hs | hs
  · have : (s : ℚ) - 1 ≤ 0 := by
      have : (s : ℚ) ≤ 1 := by exact_mod_cast (by omega : s ≤ 1)
      linarith
    exact le_trans (div_nonpos_of_nonneg_of_nonpos zero_le_one this) (by positivity)
  · have hb : 0 < s - 1 := by omega
    have h1 := Nat.div_add_mod (10 ^ 9 + s - 2) (s - 1)
    have h2 := Nat.mod_lt (10 ^ 9 + s - 2) hb
    have key : 10 ^ 9 ≤ (s - 1) * ((10 ^ 9 + s - 2) / (s - 1)) := by
      generalize (s - 1) * ((10 ^ 9 + s - 2) / (s - 1)) = m at h1 ⊢
      omega
    have hs1 : ((s - 1 : ℕ) : ℚ) = (s : ℚ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ s)]; ring
    have hpos : (0 : ℚ) < (s : ℚ) - 1 := by rw [← hs1]; exact_mod_cast hb
    rw [div_le_div_iff₀ hpos (by norm_num), one_mul, ← hs1, mul_comm]
    exact_mod_cast key

/-- The sender bound for the good primes below `10^6`. -/
theorem Inst.sum_small (c : Inst N t) (h37 : 37 ≤ t) (hlt : t < 24500) (h1 : t % 3 = 1) :
    ∑ s ∈ (G1 N t).filter (· < 1000000), 1 / ((s : ℚ) - 1) ≤ (cfun t : ℚ) / 10 ^ 9 := by
  set Lt := sendList.filter fun e => decide (e.2.1 = t) && decide (e.2.2 = 0)
  have hnd : (Lt.map fun e => e.1).Nodup :=
    sendList_nodup.sublist (List.Sublist.map _ List.filter_sublist)
  have hsub : (G1 N t).filter (· < 1000000) ⊆ (Lt.map fun e => e.1).toFinset := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsg, hz⟩ := Finset.mem_filter.mp hs1
    obtain ⟨h5, h6⟩ := c.good_ge hsg
    have hsnd := c.sender_eq h37 hlt h1 hsg (Nat.one_le_iff_ne_zero.mpr hz) hs2
    have hj : s = 5 + 6 * ((s - 5) / 6) := by omega
    have hmem := scan_spec bigP 166666 5 ((s - 5) / 6) t (by omega) (hj ▸ hsnd)
    rw [← hj, scan_full] at hmem
    obtain ⟨e, he, hee⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at hee
    have hcert := List.all_eq_true.mp sendList_cert e he
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcert
    have hd : e.2.2 = 0 := by
      rcases hcert with h | ⟨⟨ha, hb⟩, hc⟩
      · exact h
      · exfalso
        have hp := (c.good_facts hsg).1
        rw [← hee.1] at hp
        rcases hp.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero hc) with h | h <;> omega
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨e, List.mem_filter.mpr ⟨he, by simp [hee.2, hd]⟩, hee.1⟩
  calc ∑ s ∈ (G1 N t).filter (· < 1000000), 1 / ((s : ℚ) - 1)
      ≤ ∑ s ∈ (G1 N t).filter (· < 1000000), max 0 (1 / ((s : ℚ) - 1)) :=
        Finset.sum_le_sum fun _ _ => le_max_right _ _
    _ ≤ ∑ s ∈ (Lt.map fun e => (e.1 : ℕ)).toFinset, max 0 (1 / ((s : ℚ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => le_max_left _ _
    _ = (Lt.map fun e => max 0 (1 / ((e.1 : ℚ) - 1))).sum := by
        rw [List.sum_toFinset _ hnd, List.map_map]; rfl
    _ ≤ (Lt.map fun e => (((10 ^ 9 + e.1 - 2) / (e.1 - 1) : ℕ) : ℚ) / 10 ^ 9).sum :=
        list_sum_le _ _ _ fun e _ => max_le (by positivity) (inv_le_ceil e.1)
    _ = (cfun t : ℚ) / 10 ^ 9 := by rw [list_sum_div]; rfl

/-- The tail of the good primes above `10^6` divisible by `t`. -/
def tailU : ℚ := 1001 / 1000 / 1000 * (P4 * (4055 / 10000 / (1 - 4055 / 10000)))

theorem Inst.sum_large (c : Inst N t) (h37 : 37 ≤ t) :
    ∑ s ∈ (G1 N t).filter (¬ · < 1000000), 1 / ((s : ℚ) - 1) ≤ tailU := by
  have hsub : (G1 N t).filter (¬ · < 1000000) ⊆ good N t :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hut : (1 : ℚ) ≤ (4055 / 10000) ^ 4 * t := by
    have : (37 : ℚ) ≤ t := by exact_mod_cast h37
    nlinarith
  have key := c.sum_geom1 _ hsub (κ := 1001 / 1000 / 1000) (a := 6148 / 10000) (b := 5267 / 10000) (c' := 4790 / 10000) (d := 4238 / 10000)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (e := 4055 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (fun s hs => Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp
      (Finset.mem_of_mem_filter s hs)).2) fun s hs => ?_
  · refine key.trans (le_of_eq ?_)
    unfold tailU P4
    ring
  have hsg := hsub hs
  have hs6 : 1000000 ≤ s := not_lt.mp (Finset.mem_filter.mp hs).2
  have hF : ((1000 : ℚ)) ^ 4 ≤ ((1 + s + s ^ 2 : ℕ) : ℚ) := by
    have : (1000000 : ℚ) ≤ s := by exact_mod_cast hs6
    push_cast
    nlinarith
  exact c.inv_le4 hsg (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl hut) (by norm_num : (0 : ℚ) < 1000) hF (by norm_num) (cyc_le_fine hs6)

/-- The mid range with a bound `C` for the senders of `t`. -/
theorem Inst.false_mid (c : Inst N t) (h37 : 37 ≤ t) (hlt : t < 24500) (h1 : t % 3 = 1)
    {C : ℕ} (hC : cfun t ≤ C) {r : ℚ} (hr : rv t ≤ r)
    (hX : (C : ℚ) / 10 ^ 9 + tailU < 1)
    (hfin : rv 13 * rv 7 * rv 19 * rv 31 * r *
      (5 / 4 * (11 / 10) * (191 / 190) * (653 / 652) * (1 / (1 - X0)) *
        (1 / (1 - ((C : ℚ) / 10 ^ 9 + tailU)))) < 2) : False := by
  have hsum : ∑ s ∈ G1 N t, 1 / ((s : ℚ) - 1) ≤ (C : ℚ) / 10 ^ 9 + tailU := by
    rw [← Finset.sum_filter_add_sum_filter_not (G1 N t) (· < 1000000)]
    have hC' : (cfun t : ℚ) / 10 ^ 9 ≤ (C : ℚ) / 10 ^ 9 := by
      have : (cfun t : ℚ) ≤ C := by exact_mod_cast hC
      linarith
    exact add_le_add ((c.sum_small h37 hlt h1).trans hC') (c.sum_large h37)
  have hG1 : ∏ s ∈ G1 N t, rv s ≤ 1 / (1 - ((C : ℚ) / 10 ^ 9 + tailU)) :=
    prod_rv_le _ (fun s hs => c.good_two (Finset.mem_of_mem_filter s hs)) hsum hX
  refine c.close1 hr hG1 ?_
  have he : hits0.toFinset.erase t = hits0.toFinset :=
    Finset.erase_eq_of_notMem (by simp [hits0]; omega)
  rw [he, hits_prod]
  exact hfin

/-! ## The fourth prime `t ≥ 24500` -/

/-- The weights product of the square root tail. -/
def P2 : ℚ := 1 / (1 - 3780 / 10000) * (1 / (1 - 2774 / 10000)) * (1 / (1 - 2295 / 10000)) *
  (1 / (1 - 1797 / 10000))

theorem Inst.false_large (c : Inst N t) (hbig : 24500 ≤ t) : False := by
  have hut : (1 : ℚ) ≤ (64 / 10000) ^ 2 * t := by
    have : (24500 : ℚ) ≤ t := by exact_mod_cast hbig
    nlinarith
  have hsub : G1 N t ⊆ good N t := Finset.filter_subset _ _
  have key := c.sum_geom1 _ hsub (κ := 2) (a := 3780 / 10000) (b := 2774 / 10000) (c' := 2295 / 10000) (d := 1797 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (e := 64 / 10000) (by norm_num)
    (by norm_num) (by norm_num)
    (fun s hs => Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hs).2) fun s hs =>
      c.inv_le2 (hsub hs) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl hut) (by norm_num)
        (cyc_le_four (by have := (c.good_ge (hsub hs)).1; omega))
  have hG1 : ∏ s ∈ G1 N t, rv s ≤ 1 / (1 - 2 * (P2 * (64 / 10000 / (1 - 64 / 10000)))) :=
    prod_rv_le _ (fun s hs => c.good_two (hsub hs)) (key.trans (le_of_eq (by unfold P2; ring)))
      (by unfold P2; norm_num)
  refine c.close1 (rv_anti (by norm_num) hbig) hG1 ?_
  have he : hits0.toFinset.erase t = hits0.toFinset :=
    Finset.erase_eq_of_notMem (by simp [hits0]; omega)
  rw [he, hits_prod]
  unfold rv X0 P2
  norm_num

/-! ## Assembly -/

theorem Inst.false (c : Inst N t) : False := by
  have ht := Nat.prime_of_mem_primeFactors c.ht
  have htN := Nat.dvd_of_mem_primeFactors c.ht
  have h2 : t ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr c.opn.1) (even_iff_two_dvd.mpr htN)
  have h3 : t ≠ 3 := by rintro rfl; exact c.h3 htN
  have hmod : t % 3 = 1 ∨ t % 3 = 2 := by
    have := ht.eq_one_or_self_of_dvd 3
    have : ¬ t % 3 = 0 := fun h0 => by
      rcases this (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega
    omega
  rcases hmod with h1 | h2'
  · by_cases hbig : 24500 ≤ t
    · exact c.false_large hbig
    have h37 : 37 ≤ t := by
      by_contra hc
      have := c.ht7; have := c.ht13; have := c.ht19; have := c.ht31
      interval_cases t <;> first | omega | exact absurd ht (by norm_num)
    have hok := List.all_eq_true.mp primesL_ok t
      (primesP_eq ▸ mem_primesP ht h37 (by omega) h1)
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok.2 with hsp | hu
    · simp only [special, List.mem_cons, List.not_mem_nil, or_false] at hsp
      rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact c.false_67
      · exact c.false_79
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 9433963)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
      · exact c.false_307
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 12195122)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 19230770)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 8928572)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 25000000)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 17241380)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 14285715)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 11363637)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 10000000)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
      · exact c.false_mid (by norm_num) (by norm_num) (by norm_num) (C := 7692308)
          (by decide +kernel) le_rfl (by unfold tailU P4; norm_num)
          (by unfold rv X0 tailU P4; norm_num)
    · exact c.false_mid h37 (by omega) h1 hu (rv_anti (by norm_num) h37)
        (by unfold tailU P4; norm_num) (by unfold rv X0 tailU P4; norm_num)
  · by_cases h23 : 23 ≤ t
    · exact c.false_two_big h2' h23
    interval_cases t
    all_goals first
      | exact c.false_five
      | exact c.false_eleven
      | exact c.false_seventeen
      | omega
      | exact absurd ht (by norm_num)

/-- An odd perfect number with `3 ∤ N`, special prime 13 and `19 · 31 ∣ N` has at least five
prime factors `p ≠ 13` with `3 ∤ e_p + 1`. The result strengthens the three exception theorem
`four_le_card_mod_exceptions` of this library; whether it is new was not verified against the
literature. -/
theorem _root_.OddPerfect.five_le_card_mod_exceptions_of_thirteen {N : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 13)) (h3 : ¬ 3 ∣ N) (h19 : 19 ∣ N) (h31 : 31 ∣ N) :
    5 ≤ ((N.primeFactors.erase 13).filter fun p => ¬ 3 ∣ N.factorization p + 1).card := by
  by_contra hc
  obtain ⟨t, c⟩ := inst_of_card h hodd h3 h19 h31 (by unfold exc; omega)
  exact c.false

end FiveException

end OddPerfect

#print axioms OddPerfect.five_le_card_mod_exceptions_of_thirteen
