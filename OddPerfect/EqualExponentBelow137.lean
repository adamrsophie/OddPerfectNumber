import OddPerfect.EqualExponentBelow131
import OddPerfect.EqualExponentCount131

/-!
# Equal exponents `l - 1` for the odd primes below `137`

No odd perfect number has every ordinary exponent equal to `l - 1` for an odd prime `l < 137`:
the cases below `131` are `not_all_exponents_eq_pred_of_lt_131`, and `l = 131` is the counting
certificate of `OddPerfect.EqualExponentCount131`.

Restricted result: it covers only the odd primes below `137`; the family with larger `l` is not
excluded, and the odd perfect number conjecture remains open. Restricted result; no published
source was checked; novelty not verified.
-/

namespace OddPerfect

/-- No odd perfect number has every ordinary exponent equal to `l - 1` for an odd prime
`l < 137`. Restricted result; no published source was checked; novelty not verified. -/
theorem not_all_exponents_eq_pred_of_lt_137 {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) (hl137 : l < 137)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) : False := by
  rcases Nat.lt_or_ge l 131 with h131 | h131
  · exact not_all_exponents_eq_pred_of_lt_131 h hq hodd hl hl2 h131 hexp
  · interval_cases l <;> first
      | exact not_all_exponents_eq_one_hundred_thirty h hq hodd hexp
      | exact absurd hl (by norm_num)

end OddPerfect

#print axioms OddPerfect.not_all_exponents_eq_pred_of_lt_137
