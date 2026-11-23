import OddPerfect.RankinTailGeneral
import OddPerfect.ProductBound

/-!
# The Rankin tail bound with the `(2,1)` Padé product bound

`prod_fv_le_of_rankin_tail_general` turns the sum bound `rankin_tail_general` into the product
bound `∏ σ(t^2)/t^2 ≤ 1/(1 - S)` for `S < 1`. With `prod_one_add_le_pade21`
(`OddPerfect/ProductBound.lean`) the same sum bound gives the sharper product bound
`∏ σ(t^2)/t^2 ≤ (S^2 + 4 S + 6)/(6 - 2 S)`, valid for `S < 3`. This is
`prod_fv_le_of_rankin_tail_general_pade`; the certificate checker engine uses it in its tail test
(`OddPerfect/TwoExcEngineTail.lean`).

This is a tool lemma. It makes no claim about odd perfect numbers by itself.
-/

namespace OddPerfect

open RestrainedFour (fv)

/-- Product form of `rankin_tail_general` with the `(2,1)` Padé bound: under the hypotheses of
`rankin_tail_general`, if the bound is at most `S < 3`, then
`∏ σ(t^2)/t^2 ≤ (S^2 + 4 S + 6)/(6 - 2 S)` over `T`. -/
theorem prod_fv_le_of_rankin_tail_general_pade (T K U : Finset ℕ) {x k M u : ℕ} {α : ℕ → ℚ}
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
        mM * ∏ g ∈ K, 1 / (1 - α g)) ≤ S) (hS3 : S < 3) :
    ∏ t ∈ T, fv t ≤ (S ^ 2 + 4 * S + 6) / (6 - 2 * S) := by
  have hsum := (rankin_tail_general T K U hx hk hKU hU hα0 hα1 hαw hax0 hax1 haxw hUx hmL0 hmL
    hmM0 hmM hT).trans hS
  have hnn : ∀ t ∈ T, 0 ≤ fv t - 1 := by
    intro t ht
    have ht1 : 1 ≤ t := by have := (hT t ht).1; omega
    have ht0 : (0 : ℚ) < t := by exact_mod_cast ht1
    unfold fv
    rw [div_sub_one (pow_pos ht0 2).ne']
    have e : (t : ℚ) ^ 2 + t + 1 - t ^ 2 = t + 1 := by ring
    rw [e]
    positivity
  have hP := prod_one_add_le_pade21 T (fun t => fv t - 1) hnn hsum hS3
  have e : ∏ t ∈ T, (1 + (fv t - 1)) = ∏ t ∈ T, fv t :=
    Finset.prod_congr rfl fun t _ => by ring
  rw [e] at hP
  exact hP

end OddPerfect

#print axioms OddPerfect.prod_fv_le_of_rankin_tail_general_pade
