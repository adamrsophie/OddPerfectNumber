import OddPerfect.TwoExceptionsEightyNineData

/-!
# Two exceptions at the prime 89

Let `N` be an odd perfect number and let `a` and `b` be arbitrary natural numbers (two allowed
exceptions). If every prime factor `p` of `N` other than `a` and `b` has `89 ∣ e_p + 1`, then
`89 ∣ N`. The argument is `OddPerfect.TwoExcGen.dvd_of_two_exceptions_gen` with `l = 89`,
block base `1600`, half exponent `44`, least small compatible prime `11` and least receiver `179`;
the finite facts are in `OddPerfect.TwoExceptionsEightyNineData`.

Restricted result; no published source was checked; novelty not verified. It says nothing when
three prime factors have an index not divisible by `89`. The primes `61, 71, 73, 79, 83` are not
covered: the same argument does not close there. The odd perfect number conjecture remains open.
-/

namespace OddPerfect

/-- Let `a` and `b` be arbitrary natural numbers. An odd perfect number all of whose prime
factors other than `a` and `b` have an index divisible by `89` is divisible by `89`. Restricted
result; no published source was checked; novelty not verified. -/
theorem eightynine_dvd_of_two_exceptions {N a b : ℕ} (h : OddPerfect N)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ a → p ≠ b → 89 ∣ N.factorization p + 1) : 89 ∣ N :=
  TwoExcGen.dvd_of_two_exceptions_gen (l := 89) (B := 1600) (k := 44) (m := 11) (r0 := 179)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    TwoExc89.small_facts TwoExc89.e_ge TwoExc89.e_coprime TwoExc89.ge_r0 (by norm_num)
    (by norm_num) TwoExc89.big_mem TwoExc89.big_ge TwoExc89.c_lt_one TwoExc89.numeric_a
    TwoExc89.c_lt_one' TwoExc89.numeric_b h hcomp

end OddPerfect

#print axioms OddPerfect.eightynine_dvd_of_two_exceptions
