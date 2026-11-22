import OddPerfect.CommonFiveSeven

/-!
# Common exponent families: the common `85` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves that the common `85` family
is impossible, with the reach and abundance checkers of
`OddPerfect.CommonFiveSeven`. Known: the statement follows from the Main Theorem of Fletcher,
Nielsen and Ochem (Math. Comp. 81, 2012) together with Kanold's theorem
(`OddPerfect.dvd_of_dvd_succ`); the proof here is an independent certificate checked by the kernel.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

