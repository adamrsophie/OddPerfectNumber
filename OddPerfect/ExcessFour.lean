import OddPerfect.ExcessFourS1
import OddPerfect.ExcessFourS2a
import OddPerfect.ExcessFourS2b

/-!
# Total excess at least 4

Let `N` be an odd perfect number with special prime `q`. Every other prime factor `p` has an
even exponent `e_p ≥ 2`; call `e_p / 2 - 1` its excess. This module proves that the total
excess is at least 4 (`four_le_excess`), equivalently `ω(m) + 4 ≤ Ω(m)` in Euler's form
`N = q ^ a * m ^ 2` with `q ∤ m` (`four_le_cardFactors_sub`).

Relation to published results. Since `Ω(N) - 2 * ω(N) = a - 2 + 2 * (Ω(m) - ω(m))`, the
published inequality `Ω(N) ≥ 2 * ω(N) + 51` of Ochem and Rao (Math. Comp. 83, 2014) gives
`2 * (Ω(m) - ω(m)) ≥ 53 - a`, which is much stronger than the bound here when the special
exponent `a` is small and gives the bound 4 for every `a ≤ 45`. The statement here does not depend
on `a`. Whether the case `a ≥ 49` is new has not been verified against the literature.

## The proof

`ExcessFourReduction` reduces both statements to three exclusions of restricted families,
`ExcessS1`, `ExcessS2a` and `ExcessS2b` (`four_le_excess_of_exclusions` and
`four_le_cardFactors_sub_of_exclusions`). The exclusions are proved in `ExcessFourS1`,
`ExcessFourS2a` and `ExcessFourS2b`, each by one certificate of an exact search (397, 361 and
234 search nodes; 346, 213 and 234 records as checker terms) checked in the kernel by the
checker `checkV` of `OddPerfect.TwoExcEngine`, a tool whose soundness theorem `checkV_sound` is
proved in `TwoExcEngineCheck` and `TwoExcEngineTail`.
-/

open ArithmeticFunction

namespace OddPerfect

/-- For an odd perfect number `N` with special prime `q`, the total excess
`∑ (v_p(N) / 2 - 1)` over the prime factors `p ≠ q` is at least 4. For a special exponent at
most 45 this follows from a published inequality of Ochem and Rao (see the module docstring);
whether the remaining case is new has not been verified against the literature. -/
theorem four_le_excess {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    4 ≤ ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) :=
  four_le_excess_of_exclusions excessS1 excessS2a excessS2b h hq hodd

/-- In Euler's form `N = q ^ a * m ^ 2` with `q ∤ m` of an odd perfect number,
`ω(m) + 4 ≤ Ω(m)`. For `a ≤ 45` this follows from a published inequality of Ochem and Rao (see
the module docstring); whether the case `a ≥ 49` is new has not been verified against the
literature. -/
theorem four_le_cardFactors_sub {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hN : N = q ^ a * m ^ 2) :
    ArithmeticFunction.cardDistinctFactors m + 4 ≤ ArithmeticFunction.cardFactors m :=
  four_le_cardFactors_sub_of_exclusions excessS1 excessS2a excessS2b h hq hqm hN

end OddPerfect

#print axioms OddPerfect.four_le_excess
#print axioms OddPerfect.four_le_cardFactors_sub
