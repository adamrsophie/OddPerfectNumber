import OddPerfect.CommonFiveSeven

/-!
# Common exponent families: the table of the common `115` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file holds the forcing table of the
common `115` family (seeds `5, 23`) with its row divisibility checks, its target primes and
their full products. The primality of the nodes is in `OddPerfect.CommonOneFifteenPrime`; the
reach checks, the abundance check and the final theorem are in `OddPerfect.CommonOneFifteen`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

