import OddPerfect.CommonFiveSeven

/-!
# Common exponent families: the common `55` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves that the common `55` family
is impossible, with the reach and abundance checkers of
`OddPerfect.CommonFiveSeven`. We did not locate a published proof of this case.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

