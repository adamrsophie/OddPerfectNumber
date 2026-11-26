import OddPerfect.EqualExponentCountDivisible
import OddPerfect.EqualExponentCount61
import OddPerfect.EqualExponentCount71
import OddPerfect.EqualExponentCount73
import OddPerfect.EqualExponentCount79

/-!
# Exponent floors under divisible indices

Restricted result; no published source was checked; novelty not verified.

Setting: `N` is an odd perfect number with special prime `q` and `l` is a prime for which a
counting certificate is accepted
(`l = 61`, `l = 71`, `l = 73`, `l = 79`).
The hypothesis is that every ordinary index `v_p(N) + 1` (for a prime factor `p ≠ q`) is
divisible by `l`; it contains the equal exponent
family `v_p(N) = l - 1`. With `l ∣ N` and `l ≠ q` (automatic for `l ≡ 3 (mod 4)`), the
exponent `v_l(N)` is at least `3 l - 1`, by `EqCount.floor_of_checkCert`. The case `l ∤ N` is
not treated here.
-/

namespace OddPerfect

/-- Under divisible indices with `61 ∣ N`, the exponent of `61` is at least
`3 * 61 - 1 = 182`. Here `61 ≠ q` is assumed. -/
theorem exponent_floor_sixty_one {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → 61 ∣ N.factorization p + 1)
    (hlN : 61 ∣ N) (hlq : 61 ≠ q) : 3 * 61 - 1 ≤ N.factorization 61 :=
  EqCount.floor_of_checkCert EqCount.check61 h hq hodd hdiv hlN hlq

/-- Under divisible indices with `71 ∣ N`, the exponent of `71` is at least
`3 * 71 - 1 = 212`. Here `71 ≡ 3 (mod 4)`, so `71` is not the special prime. -/
theorem exponent_floor_seventy_one {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → 71 ∣ N.factorization p + 1)
    (hlN : 71 ∣ N) : 3 * 71 - 1 ≤ N.factorization 71 :=
  EqCount.floor_of_checkCert_mod_four EqCount.check71 (by decide) h hq hodd hdiv hlN

/-- Under divisible indices with `73 ∣ N`, the exponent of `73` is at least
`3 * 73 - 1 = 218`. Here `73 ≠ q` is assumed. -/
theorem exponent_floor_seventy_three {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → 73 ∣ N.factorization p + 1)
    (hlN : 73 ∣ N) (hlq : 73 ≠ q) : 3 * 73 - 1 ≤ N.factorization 73 :=
  EqCount.floor_of_checkCert EqCount.check73 h hq hodd hdiv hlN hlq

/-- Under divisible indices with `79 ∣ N`, the exponent of `79` is at least
`3 * 79 - 1 = 236`. Here `79 ≡ 3 (mod 4)`, so `79` is not the special prime. -/
theorem exponent_floor_seventy_nine {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hdiv : ∀ p ∈ N.primeFactors, p ≠ q → 79 ∣ N.factorization p + 1)
    (hlN : 79 ∣ N) : 3 * 79 - 1 ≤ N.factorization 79 :=
  EqCount.floor_of_checkCert_mod_four EqCount.check79 (by decide) h hq hodd hdiv hlN

end OddPerfect

#print axioms OddPerfect.exponent_floor_sixty_one
#print axioms OddPerfect.exponent_floor_seventy_one
#print axioms OddPerfect.exponent_floor_seventy_three
#print axioms OddPerfect.exponent_floor_seventy_nine
