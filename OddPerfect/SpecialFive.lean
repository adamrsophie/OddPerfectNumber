import OddPerfect.SpecialFiveCheck
import OddPerfect.SpecialFiveData

/-!
# Odd perfect numbers with special component `5 ^ 1` have a component above `10 ^ 24`

If `N` is an odd perfect number with `v_5(N) = 1`, then some prime power component
`p ^ v_p(N)` of `N` exceeds `10 ^ 24`. The proof is the kernel checked certificate of
`OddPerfect.SpecialFiveData` and the soundness theorem `OddPerfect.SpecialFive.check_sound`.

Ochem and Rao (Math. Comp. 81, 2012) proved that every odd perfect number has a component
above `10 ^ 62`, so this statement is a special case of a published theorem; its interest is
the machine checked proof. The odd perfect number conjecture remains open.
-/

namespace OddPerfect

/-- An odd perfect number `N` with `v_5(N) = 1` has a prime factor `p` with
`10 ^ 24 < p ^ v_p(N)`. -/
theorem exists_component_gt_of_factorization_five_eq_one {N : ℕ} (h : OddPerfect N)
    (h5 : N.factorization 5 = 1) : ∃ p ∈ N.primeFactors, 10 ^ 24 < p ^ N.factorization p :=
  SpecialFive.check_sound SpecialFive.check_cert h h5

end OddPerfect

#print axioms OddPerfect.exists_component_gt_of_factorization_five_eq_one
