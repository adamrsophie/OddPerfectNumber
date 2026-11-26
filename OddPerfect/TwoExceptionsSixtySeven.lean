import OddPerfect.TwoExceptionsSixtySevenData

/-!
# Two exceptions at the prime 67

Let `N` be an odd perfect number and let `a` and `b` be arbitrary natural numbers (two allowed
exceptions). If every prime factor `p` of `N` other than `a` and `b` has `67 ∣ e_p + 1`, then
`67 ∣ N`. The argument is `OddPerfect.TwoExcGen.dvd_of_two_exceptions_gen` with `l = 67`,
block base `1200`, half exponent `33`, least small compatible prime `13` and least receiver `269`;
the finite facts are in `OddPerfect.TwoExceptionsSixtySevenData`.

Restricted result; no published source was checked; novelty not verified. It says nothing when
three prime factors have an index not divisible by `67`. The primes `61, 71, 73, 79, 83` are not
covered: the same argument does not close there. The odd perfect number conjecture remains open.
-/

namespace OddPerfect

/-- Let `a` and `b` be arbitrary natural numbers. An odd perfect number all of whose prime
factors other than `a` and `b` have an index divisible by `67` is divisible by `67`. Restricted
result; no published source was checked; novelty not verified. -/
theorem sixtyseven_dvd_of_two_exceptions {N a b : ℕ} (h : OddPerfect N)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ a → p ≠ b → 67 ∣ N.factorization p + 1) : 67 ∣ N :=
  TwoExcGen.dvd_of_two_exceptions_gen (l := 67) (B := 1200) (k := 33) (m := 13) (r0 := 269)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    TwoExc67.small_facts TwoExc67.e_ge TwoExc67.e_coprime TwoExc67.ge_r0 (by norm_num)
    (by norm_num) TwoExc67.big_mem TwoExc67.big_ge TwoExc67.c_lt_one TwoExc67.numeric_a
    TwoExc67.c_lt_one' TwoExc67.numeric_b h hcomp

end OddPerfect

#print axioms OddPerfect.sixtyseven_dvd_of_two_exceptions
