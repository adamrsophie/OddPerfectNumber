import OddPerfect.CommonOneFifteenData

/-!
# Common exponent families: primality of the `115` table

The nodes of the forcing table of the common `115` family in
`OddPerfect.CommonOneFifteenData` are prime, by trial division over odd numbers up to the
square root, checked in parts.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

