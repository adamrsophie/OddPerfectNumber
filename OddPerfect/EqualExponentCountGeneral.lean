import OddPerfect.EqualExponentCount
import OddPerfect.EqualExponentNotSpecial

/-!
# Equal exponents: soundness of the counting checker for every odd prime `l`

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

The hypothesis `l ≠ q` of `EqCount.checkCert_sound_of_ne` is discharged by
`ordinary_of_all_exponents_eq_pred`.
-/

namespace OddPerfect.EqCount

/-- Soundness of an accepted certificate: the ordinary exponents of an odd perfect number
cannot all equal `l - 1`. -/
theorem checkCert_sound {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)}
    {main : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ × ℕ))}
    (hc : checkCert l pc main cases = true) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) : False :=
  checkCert_sound_of_ne hc h hq hodd hexp
    (ordinary_of_all_exponents_eq_pred h hq hodd (checkCert_prime hc).1 (checkCert_prime hc).2
      hexp).2

end OddPerfect.EqCount

#print axioms OddPerfect.EqCount.checkCert_sound
