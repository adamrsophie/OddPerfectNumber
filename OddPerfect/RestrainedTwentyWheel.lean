import OddPerfect.RestrainedEighteenWheel

/-!
# Wheel packing on an arbitrary residue set

General inequality for `RestrainedTwenty`; no data. It generalizes `wheel_pow_le` of
`OddPerfect.RestrainedEighteenWheel` from the residues prime to `W` to any nonempty set `J` of
residues: if every member of `S` is at least `x₀`, with `2 x₀ > W + 1`, and has its residue
modulo `W` in `J`, then `(∏_S t/(t - 1)) ^ W ≤ (1 + 2 W #S/(#J (2 x₀ - W - 1))) ^ #J`
(`wheel_pow_le_on`). The proof splits `S` into the residue classes in `J`, bounds each class by
`class_pow_le` and combines the classes by the inequality of the arithmetic and geometric means
(`prod_le_mean_pow`).
-/

namespace OddPerfect

namespace RestrainedTwenty

open RestrainedEighteen

/-- **Wheel packing on a residue set.** Let `W ≥ 1`, let `J` be a nonempty set of residues and
let every member of `S` be at least `x₀` with its residue modulo `W` in `J`, where
`W + 1 < 2 x₀`. Then `(∏_S t/(t - 1)) ^ W ≤ (1 + 2 W #S/(#J (2 x₀ - W - 1))) ^ #J`. -/
theorem wheel_pow_le_on {W x₀ : ℕ} (hW : 0 < W) (hx₀ : W + 1 < 2 * x₀) (J : Finset ℕ)
    (hJ : J.Nonempty) (S : Finset ℕ) (hS : ∀ t ∈ S, x₀ ≤ t ∧ t % W ∈ J) :
    (∏ t ∈ S, (t : ℚ) / (t - 1)) ^ W ≤
      (1 + 2 * (W : ℚ) * S.card / (J.card * (2 * (x₀ : ℚ) - W - 1))) ^ J.card := by
  classical
  have hmaps : ∀ t ∈ S, t % W ∈ J := fun t ht => (hS t ht).2
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
  have hJpos : (0 : ℚ) < J.card := by exact_mod_cast Finset.card_pos.mpr hJ
  calc (∏ t ∈ S, (t : ℚ) / (t - 1)) ^ W
      = ∏ j ∈ J, (∏ t ∈ S with t % W = j, (t : ℚ) / (t - 1)) ^ W := by
        rw [← hsplit, Finset.prod_pow]
    _ ≤ ∏ j ∈ J, (1 + c * (S.filter (fun t => t % W = j)).card) :=
        Finset.prod_le_prod (fun j _ => pow_nonneg (Finset.prod_nonneg fun t ht =>
          hf0 t (Finset.mem_filter.mp ht).1) _) hclass
    _ ≤ ((∑ j ∈ J, (1 + c * (S.filter (fun t => t % W = j)).card)) / J.card) ^ J.card :=
        prod_le_mean_pow J _ fun j _ => by positivity
    _ = (1 + 2 * (W : ℚ) * S.card / (J.card * (2 * (x₀ : ℚ) - W - 1))) ^ J.card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
        have hcast : (∑ j ∈ J, ((S.filter (fun t => t % W = j)).card : ℚ)) = S.card := by
          rw [hcount]
          push_cast
          rfl
        rw [hcast, hc]
        congr 1
        field_simp

end RestrainedTwenty

end OddPerfect

#print axioms OddPerfect.RestrainedTwenty.wheel_pow_le_on
