import OddPerfect.EqualExponentCountDivisible
import OddPerfect.EqualExponentCount83
import OddPerfect.EqualExponentCount89
import OddPerfect.EqualExponentCount97

/-!
# Exponent floors under divisible indices

Restricted result; no published source was checked; novelty not verified.

Setting: `N` is an odd perfect number with special prime `q` and `l` is a prime for which a
counting certificate is accepted
(`l = 83`, `l = 89`, `l = 97`).
The hypothesis is that every ordinary index `v_p(N) + 1` (for a prime factor `p ≠ q`) is
divisible by `l`; it contains the equal exponent
family `v_p(N) = l - 1`. With `l ∣ N` and `l ≠ q` (automatic for `l ≡ 3 (mod 4)`), the
exponent `v_l(N)` is at least `3 l - 1`, by `EqCount.floor_of_checkCert`. The case `l ∤ N` is
not treated here.
-/

namespace OddPerfect

/-- Under divisible indices with `83 ∣ N`, the exponent of `83` is at least
`3 * 83 - 1 = 248`. Here `83 ≡ 3 (mod 4)`, so `83` is not the special prime. -/
theorem exponent_floor_eighty_three {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → 83 ∣ N.factorization p + 1)
    (hlN : 83 ∣ N) : 3 * 83 - 1 ≤ N.factorization 83 :=
  EqCount.floor_of_checkCert_mod_four EqCount.check83 (by decide) h hq hodd hdiv hlN

/-- Under divisible indices with `89 ∣ N`, the exponent of `89` is at least
`3 * 89 - 1 = 266`. Here `89 ≠ q` is assumed. -/
theorem exponent_floor_eighty_nine {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → 89 ∣ N.factorization p + 1)
    (hlN : 89 ∣ N) (hlq : 89 ≠ q) : 3 * 89 - 1 ≤ N.factorization 89 :=
  EqCount.floor_of_checkCert EqCount.check89 h hq hodd hdiv hlN hlq

/-- Under divisible indices with `97 ∣ N`, the exponent of `97` is at least
`3 * 97 - 1 = 290`. Here `97 ≠ q` is assumed. -/
theorem exponent_floor_ninety_seven {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → 97 ∣ N.factorization p + 1)
    (hlN : 97 ∣ N) (hlq : 97 ≠ q) : 3 * 97 - 1 ≤ N.factorization 97 :=
  EqCount.floor_of_checkCert EqCount.check97 h hq hodd hdiv hlN hlq

end OddPerfect

#print axioms OddPerfect.exponent_floor_eighty_three
#print axioms OddPerfect.exponent_floor_eighty_nine
#print axioms OddPerfect.exponent_floor_ninety_seven
