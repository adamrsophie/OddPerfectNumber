import OddPerfect.CommonFiveSeven

/-!
# Common exponent families: the common `65` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves that the common `65` family
is impossible (known; Evans and Pearlman 2007), with the reach and abundance checkers of
`OddPerfect.CommonFiveSeven`. The special prime `13` gets its own branch with the extra seed `7`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

