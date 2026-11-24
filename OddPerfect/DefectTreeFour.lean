import OddPerfect.DefectTreeCheck
import OddPerfect.DefectTreeFourData

/-!
# The support defect is at least 4, and at least 5 when 3 divides

Let `N` be an odd perfect number with special prime `q`, `D = supportDefect N q` the support
defect of `OddPerfect.ExcessDefect`, `T` the total excess and `s = v_3(σ(q ^ v_q(N)))`. This
module proves `D ≥ 5` when `3 ∣ N` (`five_le_supportDefect_of_three_dvd`) and `D ≥ 4` always
(`four_le_supportDefect`). With the defect identity `ω(N) + 2 s + D = 5 T + 5 + #escapeRows` and
`#escapeRows ≤ 1` they give `ω(N) + 2 s ≤ 5 T + 2`
(`card_primeFactors_add_two_mul_le_five_excess_add_two`) and, when `3 ∣ N`,
`ω(N) + 2 s ≤ 5 T + 1` (`card_primeFactors_add_two_mul_le_five_excess_add_one_of_three_dvd`).

When `3 ∤ N` the definition of `D` gives `D ≥ 4` at once. When `3 ∣ N` the certificate
`certFour` of `OddPerfect.DefectTreeFourData` (parameters `K = 4`, `w = 0`, `u = 3`, root 3, no
cap for `T`) is accepted by the checker of `OddPerfect.DefectTreeCode`, and its soundness theorem
`check_sound` refutes `D ≤ 4`.

The results bound the support by the total excess `T`, which is not bounded; the odd perfect
number conjecture is open. Whether these bounds are new was not verified against the
literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- When 3 divides an odd perfect number, its support defect is at least 5. -/
theorem five_le_supportDefect_of_three_dvd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : 3 ∣ N) : 5 ≤ supportDefect N q := by
  by_contra hlt
  refine DefectTree.check_sound DefectTree.check_Four h hq hodd
    (fun c hc => absurd hc (by simp [DefectTree.paramsFour])) ?_ ?_ h3
  · show 0 * N.primeFactors.card + supportDefect N q ≤ 4
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

/-- The support defect of an odd perfect number is at least 4. -/
theorem four_le_supportDefect {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : 4 ≤ supportDefect N q := by
  by_cases h3 : 3 ∣ N
  · have := five_le_supportDefect_of_three_dvd h hq hodd h3
    omega
  · unfold supportDefect
    rw [if_neg h3]
    omega

/-- The support bound `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 2`, where `T` is the total excess.
The total excess is not bounded. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_two {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 2 := by
  have e := card_primeFactors_add_two_mul_add_defect_eq h hq hodd
  have hE := card_escapeRows_le_one_all h hq hodd
  have hD := four_le_supportDefect h hq hodd
  omega

/-- When 3 divides `N`, the support bound `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 1`, where `T` is
the total excess. The total excess is not bounded. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_one_of_three_dvd {N q : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (h3 : 3 ∣ N) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 1 := by
  have e := card_primeFactors_add_two_mul_add_defect_eq h hq hodd
  have hE := card_escapeRows_le_one_all h hq hodd
  have hD := five_le_supportDefect_of_three_dvd h hq hodd h3
  omega

end OddPerfect

#print axioms OddPerfect.five_le_supportDefect_of_three_dvd
#print axioms OddPerfect.four_le_supportDefect
#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_two
#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_one_of_three_dvd
