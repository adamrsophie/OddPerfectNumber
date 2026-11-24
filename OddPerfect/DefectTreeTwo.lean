import OddPerfect.DefectTreeCheck
import OddPerfect.DefectTreeTwoData

/-!
# The support defect is at least 3

Let `N` be an odd perfect number with special prime `q`, `D = supportDefect N q` the support
defect of `OddPerfect.ExcessDefect` and `T` the total excess. This module proves `D ≥ 3`
(`three_le_supportDefect`) and, with the defect identity
`ω(N) + 2 s + D = 5 T + 5 + #escapeRows` and `#escapeRows ≤ 1`, the support bound
`ω(N) + 2 s ≤ 5 T + 3` (`card_primeFactors_add_two_mul_le_five_excess_add_three`), where
`s = v_3(σ(q ^ v_q(N)))`.

When `3 ∤ N` the definition of `D` gives `D ≥ 4` at once. When `3 ∣ N` the certificate
`certTwo` of `OddPerfect.DefectTreeTwoData` (parameters `K = 2`, `w = 0`, `u = 3`, root 3, no cap
for `T`) is accepted by the checker of `OddPerfect.DefectTreeCode`, and its soundness theorem
`check_sound` refutes `D ≤ 2`.

The results bound the support by the total excess `T`, which is not bounded; the odd perfect
number conjecture is open. Whether these bounds are new was not verified against the
literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The support defect of an odd perfect number is at least 3. -/
theorem three_le_supportDefect {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : 3 ≤ supportDefect N q := by
  by_cases h3 : 3 ∣ N
  · by_contra hlt
    refine DefectTree.check_sound DefectTree.check_Two h hq hodd
      (fun c hc => absurd hc (by simp [DefectTree.paramsTwo])) ?_ ?_ h3
    · show 0 * N.primeFactors.card + supportDefect N q ≤ 2
      omega
    · intro p hp
      show 3 ≤ p
      have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
      have hd := Nat.dvd_of_mem_primeFactors hp
      have ho := Nat.odd_iff.mp h.1
      by_contra hp3
      have : p = 2 := by omega
      subst this
      omega
  · unfold supportDefect
    rw [if_neg h3]
    omega

/-- The support bound with the defect: `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 3`, where `T` is the
total excess. The total excess is not bounded. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_three {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 3 := by
  have e := card_primeFactors_add_two_mul_add_defect_eq h hq hodd
  have hE := card_escapeRows_le_one_all h hq hodd
  have hD := three_le_supportDefect h hq hodd
  omega

end OddPerfect

#print axioms OddPerfect.three_le_supportDefect
#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_three
