import OddPerfect.ExcessFive
import OddPerfect.ExcessSixData3
import OddPerfect.ExcessSixData5
import OddPerfect.ExcessSixData7
import OddPerfect.ExcessSixData11
import OddPerfect.ExcessSixData13
import OddPerfect.ExcessSixData17
import OddPerfect.ExcessSixData19

/-!
# Total excess at least 6

Let `N` be an odd perfect number with special prime `q`. Every other prime factor `p` has an
even exponent `e_p ≥ 2`; call `e_p / 2 - 1` its excess and `T` the total excess. This module
proves `T ≥ 6` (`six_le_excess`), equivalently `ω(m) + 6 ≤ Ω(m)` in Euler's form
`N = q ^ a * m ^ 2` with `q ∤ m` (`six_le_cardFactors_sub`), and in the variables of `N`,
`Ω(N) ≥ 2 * ω(N) + a + 10` (`two_mul_omega_add_special_add_ten_le_Omega`).

Relation to published results. Since `Ω(N) - 2 * ω(N) = a - 2 + 2 * (Ω(m) - ω(m))`, the
published inequality `Ω(N) ≥ 2 * ω(N) + 51` of Ochem and Rao (Math. Comp. 83, 2014) gives
`2 * T ≥ 53 - a`, hence `T ≥ 6` for every special exponent `a ≤ 41`. The statements here do not
depend on `a`. Whether the case `a ≥ 45` is new has not been verified against the literature.
P. Ochem reported on the Mersenne Forum in July 2026 that a run for `Ω(N) ≥ 2 * ω(N) + 55`
had finished (not published, not checked here); with that constant the case `a = 45` would
follow as well.

## The proof

The proof is that of `OddPerfect.ExcessFive` with the cap 5. Suppose `T ≤ 5`. The defect
identity and `#escapeRows ≤ 1` give `ω(N) + D ≤ 31` for the support defect `D`. If `3 ∣ N`, the
certificate with root 3 and lower bound 3 applies. If `3 ∤ N`, the smallest prime factor `p`
is at least 5 and `3 * p < 2 * ω(N) + 6 ≤ 2 * (5 * T + 2) + 6 ≤ 60`, so `p` is 5, 7, 11, 13, 17
or 19, and the certificate with root `p` and lower bound `p` applies. The seven certificates
(parameters `K = 31`, `w = 1`, cap 5 for `T`) come from an exact search and are checked in the
kernel by the checker `DefectTree.check` of `OddPerfect.DefectTreeCode`; its soundness theorem
`DefectTree.check_sound` turns each into a contradiction. The search trees have 4522, 761, 362,
31, 99, 130 and 71 nodes for the roots 3, 5, 7, 11, 13, 17 and 19. The kernel checks of the
larger certificates are split over several data modules (`OddPerfect.DefectTreeSplit`).

The total excess is not bounded by this method; the odd perfect number conjecture is open.
-/

open ArithmeticFunction

namespace OddPerfect

/-- For an odd perfect number `N` with special prime `q`, the total excess
`∑ (v_p(N) / 2 - 1)` over the prime factors `p ≠ q` is at least 6. For a special exponent at
most 41 this follows from a published inequality of Ochem and Rao (see the module docstring);
whether the remaining case is new has not been verified against the literature. -/
theorem six_le_excess {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    6 ≤ ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) := by
  by_contra hlt
  have hT : ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) ≤ 5 := by omega
  by_cases h3 : 3 ∣ N
  · refine false_of_check_excess_cap DefectTree.check_Excess6R3 ⟨rfl, rfl, rfl⟩ h hq hodd hT
      (fun p hp => ?_) h3
    show 3 ≤ p
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hd := Nat.dvd_of_mem_primeFactors hp
    have ho := Nat.odd_iff.mp h.1
    by_contra hp3
    have : p = 2 := by omega
    subst this
    omega
  · obtain ⟨hp, h5, hlt3, hd, hle⟩ := minFac_facts_of_not_three_dvd h hq hodd h3 hT
    generalize N.minFac = p at hp h5 hlt3 hd hle
    have hp19 : p ≤ 19 := by omega
    interval_cases p
    all_goals try (norm_num at hp; done)
    · exact false_of_check_excess_cap DefectTree.check_Excess6R5 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd
    · exact false_of_check_excess_cap DefectTree.check_Excess6R7 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd
    · exact false_of_check_excess_cap DefectTree.check_Excess6R11 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd
    · exact false_of_check_excess_cap DefectTree.check_Excess6R13 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd
    · exact false_of_check_excess_cap DefectTree.check_Excess6R17 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd
    · exact false_of_check_excess_cap DefectTree.check_Excess6R19 ⟨rfl, rfl, rfl⟩ h hq hodd hT
        hle hd

/-- In Euler's form `N = q ^ a * m ^ 2` with `q ∤ m` of an odd perfect number,
`ω(m) + 6 ≤ Ω(m)`. For `a ≤ 41` this follows from a published inequality of Ochem and Rao (see
the module docstring); whether the case `a ≥ 45` is new has not been verified against the
literature. -/
theorem six_le_cardFactors_sub {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hN : N = q ^ a * m ^ 2) :
    ArithmeticFunction.cardDistinctFactors m + 6 ≤ ArithmeticFunction.cardFactors m :=
  cardFactors_sub_of_le_excess h hq hqm hN (six_le_excess h hq)

/-- For an odd perfect number `N` with special prime `q` of exponent `a`,
`2 * ω(N) + a + 10 ≤ Ω(N)`. The published inequality `Ω(N) ≥ 2 * ω(N) + 51` of Ochem and Rao
(Math. Comp. 83, 2014) is stronger for `a ≤ 37`, equal for `a = 41` and weaker for `a ≥ 45`
(the special exponent is 1 modulo 4). This is the bound `six_le_excess` in other variables, not
a second obstruction. -/
theorem two_mul_omega_add_special_add_ten_le_Omega {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    2 * ArithmeticFunction.cardDistinctFactors N + N.factorization q + 10 ≤
      ArithmeticFunction.cardFactors N := by
  have := two_mul_omega_add_special_le_Omega_of_le_excess h hq hodd
    (six_le_excess h hq hodd)
  omega

end OddPerfect

#print axioms OddPerfect.six_le_excess
#print axioms OddPerfect.six_le_cardFactors_sub
#print axioms OddPerfect.two_mul_omega_add_special_add_ten_le_Omega
