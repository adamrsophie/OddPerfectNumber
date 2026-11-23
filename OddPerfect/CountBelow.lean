import OddPerfect.EulerPart

/-!
# Counting odd perfect numbers up to a bound

The odd perfect numbers up to `x` form a finite set. Hornfeck's lemma lets us
bound its size by counting the possible square roots of the square parts in Euler's form.
-/

namespace OddPerfect

/-- The odd perfect numbers up to `x` form a finite set. -/
theorem finite_oddPerfect_le (x : ℕ) : {N : ℕ | OddPerfect N ∧ N ≤ x}.Finite := by
  refine (Set.finite_Iic x).subset ?_
  intro N hN
  exact (show OddPerfect N ∧ N ≤ x from hN).2

/-- A consequence of Hornfeck's lemma: at most `√(x / 5)` odd perfect numbers are at most `x`.
The set is finite (`finite_oddPerfect_le`), so `ncard` is its true size. -/
theorem ncard_oddPerfect_le_sqrt (x : ℕ) :
    {N : ℕ | OddPerfect N ∧ N ≤ x}.ncard ≤ Nat.sqrt (x / 5) := by
  classical
  let S : Set ℕ := {N : ℕ | OddPerfect N ∧ N ≤ x}
  let T : Finset ℕ := Finset.Icc 1 (Nat.sqrt (x / 5))
  have hexists : ∀ N : ℕ, ∃ m : ℕ, N ∈ S →
      m ∈ T ∧ ∃ q k : ℕ, q.Prime ∧ N = q ^ k * m ^ 2 ∧ ¬ q ∣ m := by
    intro N
    by_cases hN : N ∈ S
    · obtain ⟨hP, hx⟩ : OddPerfect N ∧ N ≤ x := hN
      obtain ⟨q, k, m, hq, hform, hqm, hq4, hk4⟩ := exists_euler_form hP
      have hm : m ≠ 0 := by
        intro hm
        exact hP.ne_zero (by simpa [hm] using hform)
      have hq2 := hq.two_le
      have hq5 : 5 ≤ q := by omega
      have hk : k ≠ 0 := by omega
      have hqk : 5 ≤ q ^ k := hq5.trans (Nat.le_self_pow hk q)
      have hbound : m ^ 2 * 5 ≤ x := calc
        m ^ 2 * 5 ≤ m ^ 2 * q ^ k := Nat.mul_le_mul_left _ hqk
        _ = N := (Nat.mul_comm _ _).trans hform.symm
        _ ≤ x := hx
      have hsq : m ^ 2 ≤ x / 5 := (Nat.le_div_iff_mul_le (by decide)).mpr hbound
      have hmem : m ∈ T := Finset.mem_Icc.mpr ⟨by omega, Nat.le_sqrt'.mpr hsq⟩
      exact ⟨m, fun _ => ⟨hmem, q, k, hq, hform, hqm⟩⟩
    · exact ⟨0, fun h => (hN h).elim⟩
  choose f hf using hexists
  have hmaps : ∀ N ∈ S, f N ∈ (T : Set ℕ) :=
    fun N hN => Finset.mem_coe.mpr (hf N hN).1
  have hinj : Set.InjOn f S := by
    intro N₁ h₁ N₂ h₂ heq
    have hP₁ : OddPerfect N₁ := (show OddPerfect N₁ ∧ N₁ ≤ x from h₁).1
    have hP₂ : OddPerfect N₂ := (show OddPerfect N₂ ∧ N₂ ≤ x from h₂).1
    obtain ⟨q₁, k₁, hq₁, hform₁, hqm₁⟩ := (hf N₁ h₁).2
    obtain ⟨q₂, k₂, hq₂, hform₂, hqm₂⟩ := (hf N₂ h₂).2
    rw [← heq] at hform₂ hqm₂
    exact eq_of_euler_form_sq_eq hP₁ hP₂ hq₁ hq₂ hform₁ hform₂ hqm₁ hqm₂
  calc
    S.ncard ≤ (T : Set ℕ).ncard := Set.ncard_le_ncard_of_injOn f hmaps hinj T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ = Nat.sqrt (x / 5) := by
      change (Finset.Icc 1 (Nat.sqrt (x / 5))).card = Nat.sqrt (x / 5)
      rw [Nat.card_Icc, Nat.add_sub_cancel]

end OddPerfect

#print axioms OddPerfect.finite_oddPerfect_le
#print axioms OddPerfect.ncard_oddPerfect_le_sqrt
