import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Totient

/-!
# Wheel packing of large numbers prime to a modulus

General inequalities for `RestrainedEighteen`; no data. For a natural `W ≥ 1` and a finite set
`S` of naturals, each at least `x₀` with `2 x₀ > W + 1` and each prime to `W`:

* `ratio_pow_le`: `(x/(x - 1)) ^ n ≤ (2 x + n - 1)/(2 x - n - 1)` for rational `x > 1` with
  `2 x > n + 1`.
* `class_pow_le`: if the members of `A` are congruent modulo `W` and at least `x₀`, then
  `(∏_A t/(t - 1)) ^ W ≤ 1 + 2 W #A/(2 x₀ - W - 1)` (the members of one class are spaced by
  at least `W`, and the bounds of `ratio_pow_le` telescope).
* `prod_le_mean_pow`: the inequality of the arithmetic and geometric means with natural
  exponent, `∏_s z ≤ ((∑_s z)/#s) ^ #s` for nonnegative rationals.
* `wheel_pow_le`: splitting `S` into the `φ(W)` residue classes prime to `W`,
  `(∏_S t/(t - 1)) ^ W ≤ (1 + 2 W #S/(φ(W) (2 x₀ - W - 1))) ^ φ(W)`.
* `totient_30030`: `φ(30030) = 5760`.
-/

namespace OddPerfect

namespace RestrainedEighteen

/-- `((c + 1)/(c - 1)) ^ n ≤ (c + n)/(c - n)` for rational `c > n`. -/
theorem ratio_pow_le_aux (c : ℚ) : ∀ n : ℕ, (n : ℚ) < c →
    ((c + 1) / (c - 1)) ^ n ≤ (c + n) / (c - n)
  | 0, hc => by simp [div_self hc.ne']
  | n + 1, hc => by
    push_cast at hc ⊢
    have h0 : (0 : ℚ) ≤ n := n.cast_nonneg
    have hn : (n : ℚ) < c := by linarith
    have ih := ratio_pow_le_aux c n hn
    have hc1 : 0 < c - 1 := by linarith
    have hcn : 0 < c - n := by linarith
    have hcn1 : 0 < c - (n + 1) := by linarith
    rw [pow_succ]
    calc ((c + 1) / (c - 1)) ^ n * ((c + 1) / (c - 1))
        ≤ (c + n) / (c - n) * ((c + 1) / (c - 1)) :=
          mul_le_mul_of_nonneg_right ih (div_nonneg (by linarith) hc1.le)
      _ ≤ (c + (n + 1)) / (c - (n + 1)) := by
          rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hcn hc1) hcn1]
          have : (0 : ℚ) ≤ n * (n + 1) := by positivity
          nlinarith

/-- **Ratio bound.** For rational `x > 1` and natural `n` with `n + 1 < 2 x`,
`(x/(x - 1)) ^ n ≤ (2 x + n - 1)/(2 x - n - 1)`. -/
theorem ratio_pow_le {x : ℚ} {n : ℕ} (hx : 1 < x) (h : (n : ℚ) + 1 < 2 * x) :
    (x / (x - 1)) ^ n ≤ (2 * x + n - 1) / (2 * x - n - 1) := by
  have h0 : (0 : ℚ) ≤ n := n.cast_nonneg
  have h1 := ratio_pow_le_aux (2 * x - 1) n (by linarith)
  have e1 : x / (x - 1) = (2 * x - 1 + 1) / (2 * x - 1 - 1) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  have e2 : (2 * x + n - 1) / (2 * x - n - 1) = (2 * x - 1 + n) / (2 * x - 1 - n) := by ring_nf
  rw [e1, e2]
  exact h1

/-- **One residue class.** If the members of `A` are congruent modulo `W ≥ 1` and each at least
`x₀`, with `W + 1 < 2 x₀`, then `(∏_A t/(t - 1)) ^ W ≤ 1 + 2 W #A/(2 x₀ - W - 1)`. -/
theorem class_pow_le {W r : ℕ} (hW : 0 < W) (A : Finset ℕ) : ∀ x₀ : ℕ, W + 1 < 2 * x₀ →
    (∀ t ∈ A, x₀ ≤ t ∧ t % W = r) →
    (∏ t ∈ A, (t : ℚ) / (t - 1)) ^ W ≤
      1 + 2 * (W : ℚ) * A.card / (2 * (x₀ : ℚ) - W - 1) := by
  induction A using Finset.induction_on_min with
  | empty => intro _ _ _; simp
  | insert a s ha ih =>
    intro x₀ hx₀ hA
    have haS : a ∉ s := fun h => lt_irrefl _ (ha a h)
    obtain ⟨hxa, har⟩ := hA a (Finset.mem_insert_self _ _)
    have ih' := ih (a + W) (by omega) fun t ht => by
      have h1 := ha t ht
      obtain ⟨-, htr⟩ := hA t (Finset.mem_insert_of_mem ht)
      have hmod : (t - a) % W = 0 := Nat.sub_mod_eq_zero_of_mod_eq (htr.trans har.symm)
      have hle : W ≤ t - a := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hmod)
      exact ⟨by omega, htr⟩
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS, mul_pow]
    have hW' : (1 : ℚ) ≤ W := by exact_mod_cast hW
    have hxa' : (x₀ : ℚ) ≤ a := by exact_mod_cast hxa
    have hx' : (W : ℚ) + 1 < 2 * x₀ := by exact_mod_cast hx₀
    have hratio := ratio_pow_le (x := (a : ℚ)) (n := W) (by linarith) (by linarith)
    push_cast at ih' ⊢
    have hpos : (0 : ℚ) < 2 * a - W - 1 := by linarith
    have hpos' : (0 : ℚ) < 2 * x₀ - W - 1 := by linarith
    have hpow0 : 0 ≤ ((a : ℚ) / (a - 1)) ^ W :=
      pow_nonneg (div_nonneg (by linarith) (by linarith)) _
    have hk : (0 : ℚ) ≤ s.card := by positivity
    have hden : 2 * ((a : ℚ) + W) - W - 1 = 2 * a + W - 1 := by ring
    have hpos2 : (0 : ℚ) < 2 * a + W - 1 := by linarith
    have hnn : (0 : ℚ) ≤ 1 + 2 * W * s.card / (2 * a + W - 1) := by
      have : (0 : ℚ) ≤ 2 * W * s.card / (2 * a + W - 1) := by positivity
      linarith
    rw [hden] at ih'
    calc ((a : ℚ) / (a - 1)) ^ W * (∏ t ∈ s, (t : ℚ) / (t - 1)) ^ W
        ≤ ((a : ℚ) / (a - 1)) ^ W * (1 + 2 * W * s.card / (2 * a + W - 1)) :=
          mul_le_mul_of_nonneg_left ih' hpow0
      _ ≤ (2 * a + W - 1) / (2 * a - W - 1) * (1 + 2 * W * s.card / (2 * a + W - 1)) :=
          mul_le_mul_of_nonneg_right hratio hnn
      _ = 1 + 2 * W * (s.card + 1) / (2 * a - W - 1) := by
          field_simp
          ring
      _ ≤ 1 + 2 * W * (s.card + 1) / (2 * x₀ - W - 1) := by
          gcongr

/-- **Arithmetic and geometric means**, natural exponent: for nonnegative rationals,
`∏_s z ≤ ((∑_s z)/#s) ^ #s`. -/
theorem prod_le_mean_pow {ι : Type*} (s : Finset ι) (z : ι → ℚ) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ≤ ((∑ i ∈ s, z i) / s.card) ^ s.card := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hn : s.card ≠ 0 := (Finset.card_pos.mpr hs).ne'
  have hz' : ∀ i ∈ s, (0 : ℝ) ≤ (z i : ℝ) := fun i hi => by exact_mod_cast hz i hi
  have hw : (0 : ℝ) < ∑ _i ∈ s, (1 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_pos.mpr hs
  have h := Real.geom_mean_le_arith_mean s (fun _ => (1 : ℝ)) (fun i => (z i : ℝ))
    (fun _ _ => zero_le_one) hw hz'
  simp only [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at h
  have hP : (0 : ℝ) ≤ ∏ i ∈ s, (z i : ℝ) := Finset.prod_nonneg hz'
  have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hP _) h s.card
  rw [Real.rpow_inv_natCast_pow hP hn] at h2
  have h3 : ((∏ i ∈ s, z i : ℚ) : ℝ) ≤ (((∑ i ∈ s, z i) / s.card) ^ s.card : ℚ) := by
    push_cast
    exact h2
  exact_mod_cast h3

/-- **Wheel packing.** Let `W ≥ 1` and let every member of `S` be at least `x₀` and prime to
`W`, with `W + 1 < 2 x₀`. Then
`(∏_S t/(t - 1)) ^ W ≤ (1 + 2 W #S/(φ(W) (2 x₀ - W - 1))) ^ φ(W)`. -/
theorem wheel_pow_le {W x₀ : ℕ} (hW : 0 < W) (hx₀ : W + 1 < 2 * x₀) (S : Finset ℕ)
    (hS : ∀ t ∈ S, x₀ ≤ t ∧ W.Coprime t) :
    (∏ t ∈ S, (t : ℚ) / (t - 1)) ^ W ≤
      (1 + 2 * (W : ℚ) * S.card / (W.totient * (2 * (x₀ : ℚ) - W - 1))) ^ W.totient := by
  classical
  set J := (Finset.range W).filter (fun a => W.Coprime a) with hJ
  have hJcard : J.card = W.totient := by rw [hJ, Nat.totient]
  have hmaps : ∀ t ∈ S, t % W ∈ J := fun t ht => by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hW), ?_⟩
    have h := (hS t ht).2
    unfold Nat.Coprime at h ⊢
    rw [Nat.gcd_comm, ← Nat.gcd_rec]
    exact h
  have hx' : (W : ℚ) + 1 < 2 * x₀ := by exact_mod_cast hx₀
  have hD : (0 : ℚ) < 2 * x₀ - W - 1 := by linarith
  set c : ℚ := 2 * W / (2 * x₀ - W - 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hf0 : ∀ t ∈ S, (0 : ℚ) ≤ (t : ℚ) / (t - 1) := fun t ht => by
    have : (W : ℚ) + 1 < 2 * t := by
      have := (hS t ht).1
      have : (x₀ : ℚ) ≤ t := by exact_mod_cast this
      linarith
    have hW' : (1 : ℚ) ≤ W := by exact_mod_cast hW
    exact div_nonneg (by linarith) (by linarith)
  have hsplit := Finset.prod_fiberwise_of_maps_to hmaps (fun t => (t : ℚ) / (t - 1))
  have hclass : ∀ j ∈ J, (∏ t ∈ S with t % W = j, (t : ℚ) / (t - 1)) ^ W ≤
      1 + c * (S.filter (fun t => t % W = j)).card := fun j _ => by
    have := class_pow_le (r := j) hW (S.filter (fun t => t % W = j)) x₀ hx₀ fun t ht => by
      obtain ⟨htS, htj⟩ := Finset.mem_filter.mp ht
      exact ⟨(hS t htS).1, htj⟩
    rw [hc]
    calc _ ≤ _ := this
      _ = _ := by ring
  have hcount := Finset.card_eq_sum_card_fiberwise (f := fun t => t % W) (s := S) (t := J)
    (fun t ht => hmaps t ht)
  have hJpos : (0 : ℚ) < J.card := by
    rw [hJcard]
    exact_mod_cast Nat.totient_pos.mpr hW
  calc (∏ t ∈ S, (t : ℚ) / (t - 1)) ^ W
      = ∏ j ∈ J, (∏ t ∈ S with t % W = j, (t : ℚ) / (t - 1)) ^ W := by
        rw [← hsplit, Finset.prod_pow]
    _ ≤ ∏ j ∈ J, (1 + c * (S.filter (fun t => t % W = j)).card) :=
        Finset.prod_le_prod₀ (fun j _ => pow_nonneg (Finset.prod_nonneg fun t ht =>
          hf0 t (Finset.mem_filter.mp ht).1) _) hclass
    _ ≤ ((∑ j ∈ J, (1 + c * (S.filter (fun t => t % W = j)).card)) / J.card) ^ J.card :=
        prod_le_mean_pow J _ fun j _ => by positivity
    _ = (1 + 2 * (W : ℚ) * S.card / (W.totient * (2 * (x₀ : ℚ) - W - 1))) ^ W.totient := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
        have hcast : (∑ j ∈ J, ((S.filter (fun t => t % W = j)).card : ℚ)) = S.card := by
          rw [hcount]
          push_cast
          rfl
        rw [hcast, ← hJcard, hc]
        congr 1
        field_simp

/-- `φ(30030) = 5760`. -/
theorem totient_30030 : Nat.totient 30030 = 5760 := by decide +kernel

end RestrainedEighteen

end OddPerfect

#print axioms OddPerfect.RestrainedEighteen.ratio_pow_le_aux
#print axioms OddPerfect.RestrainedEighteen.ratio_pow_le
#print axioms OddPerfect.RestrainedEighteen.class_pow_le
#print axioms OddPerfect.RestrainedEighteen.prod_le_mean_pow
#print axioms OddPerfect.RestrainedEighteen.wheel_pow_le
#print axioms OddPerfect.RestrainedEighteen.totient_30030
