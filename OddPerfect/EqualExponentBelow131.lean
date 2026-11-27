import OddPerfect.Steuerwald
import OddPerfect.EqualExponentChain
import OddPerfect.EqualExponentChainMore
import OddPerfect.EqualExponentChainFar
import OddPerfect.EqualExponentChainFar53
import OddPerfect.EqualExponentChainFar59
import OddPerfect.EqualExponentChainFar67
import OddPerfect.EqualExponentCount61
import OddPerfect.EqualExponentCount71
import OddPerfect.EqualExponentCount73
import OddPerfect.EqualExponentCount79
import OddPerfect.EqualExponentCount83
import OddPerfect.EqualExponentCount89
import OddPerfect.EqualExponentCount97
import OddPerfect.EqualExponentCount101
import OddPerfect.EqualExponentCount103
import OddPerfect.EqualExponentCount107
import OddPerfect.EqualExponentCount109
import OddPerfect.EqualExponentCount113
import OddPerfect.EqualExponentCount127

/-!
# Equal exponents `l - 1` for every odd prime `l < 131`

If every ordinary exponent of an odd perfect number equals `l - 1` for an odd prime `l < 131`,
we reach a contradiction. This collects the thirty landed cases (exponents `2`, `4`, ..., `126`)
into one statement.

Restricted result: it covers only the odd primes below `131`; the family with larger `l` is not
excluded, and the odd perfect number conjecture remains open. Restricted result; no published
source was checked; novelty not verified.
-/

namespace OddPerfect

/-- No odd perfect number has every ordinary exponent equal to `l - 1` for an odd prime
`l < 131`. Restricted result; no published source was checked; novelty not verified. -/
theorem not_all_exponents_eq_pred_of_lt_131 {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) (hl131 : l < 131)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) : False := by
  interval_cases l <;> first
    | exact absurd rfl hl2
    | exact steuerwald h hq hodd hexp
    | exact not_all_exponents_eq_four h hq hodd hexp
    | exact not_all_exponents_eq_six h hq hodd hexp
    | exact not_all_exponents_eq_ten h hq hodd hexp
    | exact not_all_exponents_eq_twelve h hq hodd hexp
    | exact not_all_exponents_eq_sixteen h hq hodd hexp
    | exact not_all_exponents_eq_eighteen h hq hodd hexp
    | exact not_all_exponents_eq_twenty_two h hq hodd hexp
    | exact not_all_exponents_eq_twenty_eight h hq hodd hexp
    | exact not_all_exponents_eq_thirty h hq hodd hexp
    | exact not_all_exponents_eq_thirty_six h hq hodd hexp
    | exact not_all_exponents_eq_forty h hq hodd hexp
    | exact not_all_exponents_eq_forty_two h hq hodd hexp
    | exact not_all_exponents_eq_forty_six h hq hodd hexp
    | exact not_all_exponents_eq_fifty_two h hq hodd hexp
    | exact not_all_exponents_eq_fifty_eight h hq hodd hexp
    | exact not_all_exponents_eq_sixty h hq hodd hexp
    | exact not_all_exponents_eq_sixty_six h hq hodd hexp
    | exact not_all_exponents_eq_seventy h hq hodd hexp
    | exact not_all_exponents_eq_seventy_two h hq hodd hexp
    | exact not_all_exponents_eq_seventy_eight h hq hodd hexp
    | exact not_all_exponents_eq_eighty_two h hq hodd hexp
    | exact not_all_exponents_eq_eighty_eight h hq hodd hexp
    | exact not_all_exponents_eq_ninety_six h hq hodd hexp
    | exact not_all_exponents_eq_one_hundred h hq hodd hexp
    | exact not_all_exponents_eq_one_hundred_two h hq hodd hexp
    | exact not_all_exponents_eq_one_hundred_six h hq hodd hexp
    | exact not_all_exponents_eq_one_hundred_eight h hq hodd hexp
    | exact not_all_exponents_eq_one_hundred_twelve h hq hodd hexp
    | exact not_all_exponents_eq_one_hundred_twenty_six h hq hodd hexp
    | (norm_num at hl)

end OddPerfect

#print axioms OddPerfect.not_all_exponents_eq_pred_of_lt_131
