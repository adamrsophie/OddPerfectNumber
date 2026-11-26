import OddPerfect.TwoExceptionsNinetySevenCore
import OddPerfect.CycloRootCount
import OddPerfect.AbundancyTail

/-!
# Two exceptions at the prime 97

Let `N` be an odd perfect number and let `a` and `b` be arbitrary natural numbers (two allowed
exceptions). If every prime factor `p` of `N` other than `a` and `b` has `97 ∣ e_p + 1`, then
`97 ∣ N`. The special prime may be one of the two exceptions: with `a` the special prime, this
says that an odd perfect number not divisible by `97` has at least two ordinary prime factors
whose index is not divisible by `97`. The argument is in
`OddPerfect.TwoExceptionsNinetySevenCore`; this module supplies its five inputs from
`OddPerfect.CycloRootCount` and `OddPerfect.AbundancyTail`.

Restricted result; no published source was checked; novelty not verified. It says nothing when
three prime factors have an index not divisible by `97`.
-/

namespace OddPerfect

/-- Let `a` and `b` be arbitrary natural numbers. An odd perfect number all of whose prime
factors other than `a` and `b` have an index divisible by `97` is divisible by `97`. Restricted
result; no published source was checked; novelty not verified. -/
theorem ninetyseven_dvd_of_two_exceptions {N a b : ℕ} (h : OddPerfect N)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ a → p ≠ b → 97 ∣ N.factorization p + 1) : 97 ∣ N :=
  TwoExc97.ninetyseven_dvd_of_two_exceptions_of
    (fun hr hr97 hk => card_filter_pow_dvd_geom_sum_le (by norm_num) hr hr97 hk)
    (fun hr hr97 hp₁ hp₂ h12 h₁ h₂ =>
      pow_lt_of_geom_sum_eq_prime_pow (by norm_num) hr hr97 hp₁ hp₂ h12 h₁ h₂)
    (fun s x hx hs => prod_one_add_le_inv_one_sub s x hx hs)
    (two_lt_prod_primeFactors_div h)
    (fun _ _ hs hc => sum_inv_pred_le_of_interval_card (by norm_num) hs hc)
    h hcomp

end OddPerfect

#print axioms OddPerfect.ninetyseven_dvd_of_two_exceptions
