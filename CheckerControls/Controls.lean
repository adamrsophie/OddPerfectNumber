import OddPerfect.Pratt
import OddPerfect.Certificate
import OddPerfect.LowerBound
import OddPerfect.LargestPrimeFactor
import OddPerfect.EqualExponentChain
import OddPerfect.CommonPrimeChain
import OddPerfect.CommonFamily
import OddPerfect.CommonFiveSeven
import OddPerfect.OmegaSix
import OddPerfect.OmegaSevenEngine
import OddPerfect.ThreeFreeThreeChecker
import OddPerfect.ForcingClosedBound
import OddPerfect.ReciprocalSumTwo
import OddPerfect.CommonFastChecks
import OddPerfect.RestrainedSevenCheck
import OddPerfect.LargestPrimeFactorTwo
import OddPerfect.SecondLargestPrimeFast
import OddPerfect.MixedIndexData
import OddPerfect.MixedIndexThreePrimes
import OddPerfect.TwoExcEngineCode

/-!
# Checker controls

Regression controls for the Boolean certificate checkers of the library, not part of the
library: nothing imports this file and the library build never compiles it. Run it with
`sh CheckerControls/run.sh`.

Every control is an `example` fixing the value of a checker on a tiny hand made input: `true`
on a well formed input, `false` on an input with exactly one malformation. Some controls pin a
documented raw behavior, where the checker accepts an input whose side conditions are false;
the soundness theorem named in the comment carries the hypothesis that excludes it.
-/

namespace CheckerControls

open OddPerfect

/-! ## Pratt certificates (`OddPerfect.Pratt`) -/

-- Well formed: `2` has order `12` modulo `13` and `12 = 2 * 2 * 3`.
example : Pratt.check [(13, 2, [2, 2, 3])] = true := by decide +kernel
-- Well formed: the entry checker certifies the listed prime `13`.
example : Pratt.checkPrime 13 [(13, 2, [2, 2, 3])] = true := by decide +kernel
-- Wrong target: `17` is not the prime of any entry.
example : Pratt.checkPrime 17 [(13, 2, [2, 2, 3])] = false := by decide +kernel
-- Wrong witness: `3 ^ 6 ≡ 1 (mod 13)`, so `3` does not have order `12`.
example : Pratt.check [(13, 3, [2, 2, 3])] = false := by decide +kernel
-- Composite factor: `6` is listed as a prime factor of `12` without its own entry.
example : Pratt.check [(13, 2, [2, 6])] = false := by decide +kernel
-- Composite factor with its own entry: the entry for `6` is itself rejected.
example : Pratt.check [(6, 5, [5]), (13, 2, [2, 6])] = false := by decide +kernel
-- Incomplete factorization: `2 * 3 ≠ 12`.
example : Pratt.check [(13, 2, [2, 3])] = false := by decide +kernel
-- Composite entry: `15` has no element of order `14`.
example : Pratt.check [(15, 2, [2, 7])] = false := by decide +kernel
-- A later entry that is wrong rejects the whole certificate.
example : Pratt.check [(13, 2, [2, 2, 3]), (13, 3, [2, 2, 3])] = false := by decide +kernel

/-! ## Trial division primality tests -/

-- `Pratt.trialPrime`: primes accepted.
example : [2, 3, 5, 97].all Pratt.trialPrime = true := by decide +kernel
-- `Pratt.trialPrime`: `0`, `1`, a composite and a prime square rejected.
example : [0, 1, 91, 49].any Pratt.trialPrime = false := by decide +kernel
-- `LowerBound.tdPrime`: primes accepted.
example : [2, 3, 5, 97, 9973].all LowerBound.tdPrime = true := by decide +kernel
-- `LowerBound.tdPrime`: `0`, `1`, composites and prime squares rejected.
example : [0, 1, 4, 9, 91, 49, 9409].any LowerBound.tdPrime = false := by decide +kernel
-- `FamInst.sqPrime`: primes accepted, including the special case `2`.
example : [2, 3, 5, 97, 9973].all FamInst.sqPrime = true := by decide +kernel
-- `FamInst.sqPrime`: `0`, `1`, even and odd composites and prime squares rejected.
example : [0, 1, 4, 9, 25, 91, 49, 9409].any FamInst.sqPrime = false := by decide +kernel
-- `Cert.isPrimeB`: primes accepted.
example : [2, 3, 5, 97].all Cert.isPrimeB = true := by decide +kernel
-- `Cert.isPrimeB`: `0`, `1`, a composite and a prime square rejected.
example : [0, 1, 91, 49].any Cert.isPrimeB = false := by decide +kernel
-- `LPF.isPrimeF`: primes accepted.
example : [2, 3, 5, 97, 9973].all LPF.isPrimeF = true := by decide +kernel
-- `LPF.isPrimeF`: `0`, `1`, a composite and prime squares rejected.
example : [0, 1, 91, 49, 9409].any LPF.isPrimeF = false := by decide +kernel
-- `OmegaSixSearch.isPrimeQ` (a filter that must keep every prime): primes kept.
example : [2, 3, 5, 97, 9973].all OmegaSixSearch.isPrimeQ = true := by decide +kernel
-- `OmegaSixSearch.isPrimeQ`: `0`, `1`, a composite and prime squares dropped.
example : [0, 1, 91, 49, 9409].any OmegaSixSearch.isPrimeQ = false := by decide +kernel

/-! ## Small sieve (`ForcingClosedBound.smallSieveB`) -/

-- The least prime passes.
example : ForcingClosedBound.smallSieveB 2 = true := by decide +kernel
-- The least composite is rejected.
example : ForcingClosedBound.smallSieveB 4 = false := by decide +kernel
-- Documented raw behavior: `0` passes although it is not prime (`q ≤ d` holds for every `d`).
-- The filter is used only on lists that start at `3`, and soundness uses only
-- `smallSieveB_of_prime`.
example : ForcingClosedBound.smallSieveB 0 = true := by decide +kernel
-- Documented raw behavior: `1` passes although it is not prime, for the same reason.
example : ForcingClosedBound.smallSieveB 1 = true := by decide +kernel

/-! ## Consecutive primes (`LowerBound.consec`) -/

-- Well formed: the consecutive primes from `3`.
example : LowerBound.consec 3 [3, 5, 7, 11] = true := by decide +kernel
-- Skipped prime: `5` lies between `3` and `7`.
example : LowerBound.consec 3 [3, 7] = false := by decide +kernel
-- Entry below the bound: `3 < 5`.
example : LowerBound.consec 5 [3] = false := by decide +kernel
-- Documented raw behavior: entries need not be prime. `prod_consec_le_prod` only uses the
-- entries as lower bounds for the consecutive primes, so this is sound.
example : LowerBound.consec 8 [8] = true := by decide +kernel

/-! ## The lower bound proof tree runner (`LowerBound.run`) -/

-- No instructions and no open states: accepted (`run_sound` then says nothing).
example : LowerBound.run 0 .leaf [] [] = true := by decide +kernel
-- An open state left on the stack is never accepted.
example : LowerBound.run 0 .leaf [] [[.nd 3]] = false := by decide +kernel
-- Well formed leaf: `3 ∣ N` against `¬ 3 ∣ N`.
example : LowerBound.run 0 .leaf [.ndc 3] [[.pw 3 1, .nd 3]] = true := by decide +kernel
-- Leaf without its contradiction: the state does not record `¬ 3 ∣ N`.
example : LowerBound.run 0 .leaf [.ndc 3] [[.pw 3 1]] = false := by decide +kernel
-- Instructions left over after the stack is empty.
example : LowerBound.run 0 .leaf [.ndc 3, .ndc 3] [[.pw 3 1, .nd 3]] = false := by decide +kernel

/-! ## Prime factor outside a modulus (`LPF.bigF`) -/

-- `15` has the prime factors `3, 5`, which do not divide `2`.
example : LPF.bigF 2 15 = true := by decide +kernel
-- After stripping the factor `2` (99 rounds) the cofactor `3` is coprime to `2`.
example : LPF.bigF 2 (3 * 2 ^ 99) = true := by decide +kernel
-- Every prime factor of `45` divides `15`.
example : LPF.bigF 15 45 = false := by decide +kernel
-- `1` has no prime factor.
example : LPF.bigF 2 1 = false := by decide +kernel
-- Documented one sided behavior: the stripping stops after 100 rounds, so `false` is
-- inconclusive here although `3` divides the argument and not `2`.
example : LPF.bigF 2 (3 * 2 ^ 101) = false := by decide +kernel

/-! ## Equal exponent chains (`OddPerfect.EqChain`) -/

-- Well formed overflow for `l = 5`: `5 ∣ σ(p ^ 4)` for five known primes, `5 > 4`.
example : EqChain.run 5 [] ⟨[11831, 1361, 211, 71, 11, 5], [], none, 2⟩
    (.overflow 5 [(11831, 1), (1361, 1), (211, 1), (71, 1), (11, 1)] 0 0) = true := by
  decide +kernel
-- Duplicated node: `11` is listed twice in the ledger.
example : EqChain.run 5 [] ⟨[11831, 1361, 211, 71, 11, 5], [], none, 2⟩
    (.overflow 5 [(11831, 1), (1361, 1), (211, 1), (11, 1), (11, 1)] 0 0) = false := by
  decide +kernel
-- Ledger entry that is not a divisor: `5 ∤ σ(13 ^ 4)`.
example : EqChain.run 5 [] ⟨[11831, 1361, 211, 71, 13, 5], [], none, 2⟩
    (.overflow 5 [(11831, 1), (1361, 1), (211, 1), (71, 1), (13, 1)] 0 0) = false := by
  decide +kernel
-- Valuation claimed too large: `25 ∤ σ(11 ^ 4)`.
example : EqChain.run 5 [] ⟨[1361, 211, 71, 11, 5], [], none, 2⟩
    (.overflow 5 [(1361, 1), (211, 1), (71, 1), (11, 2)] 0 0) = false := by
  decide +kernel
-- Count too small: four contributions do not exceed `l - 1 = 4`.
example : EqChain.run 5 [] ⟨[1361, 211, 71, 11, 5], [], none, 2⟩
    (.overflow 5 [(1361, 1), (211, 1), (71, 1), (11, 1)] 0 0) = false := by
  decide +kernel
-- Unknown prime: `11831` is used without being forced first.
example : EqChain.run 5 [] ⟨[1361, 211, 71, 11, 5], [], none, 2⟩
    (.overflow 5 [(11831, 1), (1361, 1), (211, 1), (71, 1), (11, 1)] 0 0) = false := by
  decide +kernel
-- Well formed forcing step: `11 ∣ σ(5 ^ 4) = 781`, then the special prime `3` closes.
example : EqChain.run 5 [] ⟨[5], [5], some 3, 2⟩ (.ord 5 11 .mod4) = true := by decide +kernel
-- Forcing step with a non divisor: `13 ∤ σ(5 ^ 4)`.
example : EqChain.run 5 [] ⟨[5], [5], some 3, 2⟩ (.ord 5 13 .mod4) = false := by decide +kernel
-- Forcing step from a prime that is not known: `7` is not in `known`.
example : EqChain.run 5 [] ⟨[5], [5], some 3, 2⟩ (.ord 7 11 .mod4) = false := by decide +kernel
-- Well formed closing: the known special prime `3` is not `1 (mod 4)`.
example : EqChain.run 5 [] ⟨[], [], some 3, 2⟩ .mod4 = true := by decide +kernel
-- Closing with `13 ≡ 1 (mod 4)` is rejected.
example : EqChain.run 5 [] ⟨[], [], some 13, 2⟩ .mod4 = false := by decide +kernel
-- Closing without a known special prime is rejected.
example : EqChain.run 5 [] ⟨[], [], none, 2⟩ .mod4 = false := by decide +kernel

/-! ## Common prime chains (`OddPerfect.CommonChain.check`) -/

-- Well formed: `σ(5 ^ 4) = 781 = 11 · 71`, both `≡ 1 (mod 5)`, count `2`.
example : CommonChain.check 5 [11, 71] [[1, 2]] 2 2 = true := by decide +kernel
-- Duplicated node.
example : CommonChain.check 5 [11, 71, 71] [[1, 2]] 2 2 = false := by decide +kernel
-- Row entry that is not a divisor: `71 ∤ Φ_5(11) = 16105`.
example : CommonChain.check 5 [11, 71] [[1, 2], [2]] 2 2 = false := by decide +kernel
-- Robust count too large.
example : CommonChain.check 5 [11, 71] [[1, 2]] 2 3 = false := by decide +kernel
-- Node not `≡ 1 (mod 5)`: `13`.
example : CommonChain.check 5 [11, 71, 13] [[1, 2]] 2 2 = false := by decide +kernel
-- No passes: nothing is reached.
example : CommonChain.check 5 [11, 71] [[1, 2]] 0 2 = false := by decide +kernel

/-! ## Common families (`OddPerfect.CommonFam`, `OddPerfect.FamInst`) -/

-- `tcheck`, well formed: from the seed `5` the row reaches `11, 71`; no node is `≡ 1 (mod 12)`.
example : CommonFam.tcheck 5 12 1 [5, 11, 71] 1 [[1, 2]] [1, 2] 1 = true := by decide +kernel
-- `tcheck`: the seed `5 ≡ 1 (mod 4)` may be the special prime, and then nothing is reached.
example : CommonFam.tcheck 5 4 1 [5, 11, 71] 1 [[1, 2]] [1, 2] 1 = false := by decide +kernel
-- `tcheck`: target not reached.
example : CommonFam.tcheck 5 12 1 [5, 11, 71] 1 [[1]] [1, 2] 1 = false := by decide +kernel
-- `tcheck`: row entry that is not a divisor: `71 ∤ Φ_5(11)`.
example : CommonFam.tcheck 5 12 1 [5, 11, 71] 1 [[1, 2], [2]] [1, 2] 1 = false := by
  decide +kernel
-- `tcheck`: a node equal to `2`.
example : CommonFam.tcheck 5 12 1 [5, 11, 71, 2] 1 [[1, 2]] [1, 2] 1 = false := by
  decide +kernel
-- `FamInst.reach`, well formed: the target mask `6` (nodes `11, 71`) is reached.
example : FamInst.reach [5, 11, 71] [[1, 2]] 1 6 1 0 = true := by decide +kernel
-- `FamInst.reach`: the blocked source `5` reaches nothing.
example : FamInst.reach [5, 11, 71] [[1, 2]] 1 6 1 5 = false := by decide +kernel
-- `FamInst.reach`: zero passes reach nothing.
example : FamInst.reach [5, 11, 71] [[1, 2]] 1 6 0 0 = false := by decide +kernel
-- `FamInst.rowChk`: a receiver that does not divide `Φ_5(11)`.
example : FamInst.rowChk 5 [5, 11, 71] (11, [2]) = false := by decide +kernel
-- `FamInst.ndM`: duplicates rejected.
example : FamInst.ndM [3, 5, 3] 0 = false := by decide +kernel
-- `abOK`, well formed: `3 ^ 4 5 ^ 4 11 ^ 4` is abundant, no element `≡ 1 (mod 12)`.
example : CommonFam.abOK [3, 5, 11] 12 1 = true := by decide +kernel
-- `abOK`: abundance product not above `2`: `σ(3 ^ 4) / 3 ^ 4 = 121 / 81`.
example : CommonFam.abOK [3] 12 1 = false := by decide +kernel
-- `abOK`: with `5` as a candidate special prime, `3 ^ 4 5 11 ^ 4` is not abundant.
example : CommonFam.abOK [3, 5, 11] 4 1 = false := by decide +kernel
-- `abOK`, documented raw behavior: duplicate components are not rejected by the predicate;
-- `abOK_sound` assumes `S.Nodup`.
example : CommonFam.abOK [3, 3] 12 1 = true := by decide +kernel
-- `abOK2`, well formed: `P` and `G` are the products for `[3, 5, 11]`.
example : FamInst.abOK2 [3, 5, 11] (fun b => b % 12 == 1) (81 * 625 * 14641)
    (121 * 781 * 16105) = true := by decide +kernel
-- `abOK2`: abundance product not above `2`.
example : FamInst.abOK2 [3] (fun b => b % 12 == 1) 81 121 = false := by decide +kernel
-- `abOK2`: with `5` as a candidate special prime the product is not above `2`.
example : FamInst.abOK2 [3, 5, 11] (fun b => b % 4 == 1) (81 * 625 * 14641)
    (121 * 781 * 16105) = false := by decide +kernel
-- `abOK2`, documented raw behavior: duplicates are not rejected; `FamInst.abOK2_sound`
-- assumes `S.Nodup`.
example : FamInst.abOK2 [3, 3] (fun b => b % 12 == 1) (81 * 81) (121 * 121) = true := by
  decide +kernel
-- `abOK2`, documented raw behavior: `P` and `G` are not tied to `S`; `FamInst.abOK2_sound`
-- assumes `pPow (expL S 0) = P` and `pSig (expL S 0) = G`.
example : FamInst.abOK2 [3] (fun b => b % 12 == 1) 1 3 = true := by decide +kernel

/-! ## The six prime search (`OmegaSixSearch.solve`) -/

-- Zero fuel: unresolved, never accepted.
example : OmegaSixSearch.solve 0 [⟨3, 4, true⟩, ⟨5, 2, true⟩, ⟨11, 2, true⟩] 0 11 = false := by
  decide +kernel
-- Exact exponents with abundancy above `2`: closed.
example : OmegaSixSearch.solve 5 [⟨3, 4, true⟩, ⟨5, 2, true⟩, ⟨11, 2, true⟩] 0 11 = true := by
  decide +kernel
-- The same state with minimal exponents: also closed (the abundancy test uses the lower bound).
example : OmegaSixSearch.solve 5 [⟨3, 4, false⟩, ⟨5, 2, false⟩, ⟨11, 2, false⟩] 0 11 = true := by
  decide +kernel
-- Exact `2 ^ 2 7`, abundancy exactly `2` (the perfect number `28`): not closed.
example : OmegaSixSearch.solve 5 [⟨2, 2, true⟩, ⟨7, 1, true⟩] 0 7 = false := by decide +kernel
-- The same with minimal exponents: not closed, since its exact branch is the state above.
example : OmegaSixSearch.solve 5 [⟨2, 2, false⟩, ⟨7, 1, false⟩] 0 7 = false := by decide +kernel
-- Exact `3 ^ 2` alone is deficient: closed.
example : OmegaSixSearch.solve 5 [⟨3, 2, true⟩] 0 3 = true := by decide +kernel

/-! ## The seven prime engine (`OmegaSevenEngine.run`) -/

-- Zero fuel: unresolved, never accepted.
example : OmegaSevenEngine.run 0 [⟨3, 4, true⟩, ⟨5, 2, true⟩, ⟨11, 2, true⟩] 0 11 = false := by
  decide +kernel
-- Exact exponents with abundancy above `2`: closed.
example : OmegaSevenEngine.run 5 [⟨3, 4, true⟩, ⟨5, 2, true⟩, ⟨11, 2, true⟩] 0 11 = true := by
  decide +kernel
-- The same state with minimal exponents: also closed.
example : OmegaSevenEngine.run 5 [⟨3, 4, false⟩, ⟨5, 2, false⟩, ⟨11, 2, false⟩] 0 11 = true := by
  decide +kernel
-- Exact `2 ^ 2 7` (the perfect number `28`): not closed.
example : OmegaSevenEngine.run 5 [⟨2, 2, true⟩, ⟨7, 1, true⟩] 0 7 = false := by decide +kernel
-- The same with minimal exponents: not closed.
example : OmegaSevenEngine.run 5 [⟨2, 2, false⟩, ⟨7, 1, false⟩] 0 7 = false := by decide +kernel
-- Exact `3 ^ 2` alone is deficient: closed.
example : OmegaSevenEngine.run 5 [⟨3, 2, true⟩] 0 3 = true := by decide +kernel

/-! ## Three exceptional primes (`OddPerfect.ThreeFreeThree.leafOK`, `treeOK`) -/

-- Well formed: leaf 388 of the certificate, the leaf with the largest bound (about 1.99653).
example : ThreeFreeThree.leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 109⟩
    ⟨(109, 393), (223, 590), (209, 911), (25, 261)⟩ = true := by decide +kernel
-- Weight `w₃ = 25/262` is not admissible: `262 ^ 2 > 25 ^ 2 * 109`.
example : ThreeFreeThree.leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 109⟩
    ⟨(109, 393), (223, 590), (209, 911), (25, 262)⟩ = false := by decide +kernel
-- Weight `w₀ = 111/393` is admissible but too large: the bound is about `2.0038`.
example : ThreeFreeThree.leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 109⟩
    ⟨(111, 393), (223, 590), (209, 911), (25, 261)⟩ = false := by decide +kernel
-- `r₃` pinned to `127` instead of `109`: with the same weights the bound is about `2.0127`.
example : ThreeFreeThree.leafOK (.c7, .c19, .big) ⟨.free .q 13 [], .pin 7, .pin 19, .pin 127⟩
    ⟨(109, 393), (223, 590), (209, 911), (25, 261)⟩ = false := by decide +kernel
-- Well formed tree (hand made): split `q` at `13`. The pinned child is closed with
-- `w₀ = 109/393`; in the other child `13` is excluded, the least value of `q` is `25` and the
-- weight `w₀ = 1/5` is admissible.
example : ThreeFreeThree.treeOK (.c5, .n2, .n2) (ThreeFreeThree.rootNode (.c5, .n2, .n2))
    (.split 0 13 (.leaf ⟨(109, 393), (0, 1), (0, 1), (0, 1)⟩)
      (.leaf ⟨(1, 5), (0, 1), (0, 1), (0, 1)⟩)) = true := by decide +kernel
-- The same tree with the pinned child removed: `13` is no longer excluded, and `1/5` is not
-- admissible for the least value `13`.
example : ThreeFreeThree.treeOK (.c5, .n2, .n2) (ThreeFreeThree.rootNode (.c5, .n2, .n2))
    (.leaf ⟨(1, 5), (0, 1), (0, 1), (0, 1)⟩) = false := by decide +kernel
-- The other child alone, from its explicit constraints: accepted with `13` excluded.
example : ThreeFreeThree.treeOK (.c5, .n2, .n2) ⟨.free .q 13 [13], .pin 5, .free .n2 11 [],
    .free .n2 11 []⟩ (.leaf ⟨(1, 5), (0, 1), (0, 1), (0, 1)⟩) = true := by decide +kernel
-- The same with the excluded value `13` dropped: rejected.
example : ThreeFreeThree.treeOK (.c5, .n2, .n2) ⟨.free .q 13 [], .pin 5, .free .n2 11 [],
    .free .n2 11 []⟩ (.leaf ⟨(1, 5), (0, 1), (0, 1), (0, 1)⟩) = false := by decide +kernel
-- A split of a pinned slot (`r₁ = 5`) is rejected whatever its children are.
example : ThreeFreeThree.treeOK (.c5, .n2, .n2) (ThreeFreeThree.rootNode (.c5, .n2, .n2))
    (.split 1 5 (.leaf ⟨(109, 393), (0, 1), (0, 1), (0, 1)⟩)
      (.leaf ⟨(109, 393), (0, 1), (0, 1), (0, 1)⟩)) = false := by decide +kernel
-- The closing test `finalOK m C X` accepts when `ρ(m) ∏ s/(s - 1) (178802/178801) / (1 - X)`
-- is at most `2`, where `ρ(m) = ∏ mᵢ/(mᵢ - 1)` and `X = X.1/X.2`. Its earlier form used
-- `(s ^ 2 + s + 1)/s ^ 2` for each small prime `s` of `C` and no tail factor `178802/178801`.
-- The three controls below separate the two forms; all values are exact.
-- Small prime factor: `m = (7, 11, 13, 17)`, `C = [5]`, `X = 1/12`. The current value is
-- `19757621/9808512 ≈ 2.01433 > 2` (already `1547/768 ≈ 2.01432` without the tail factor), the
-- earlier one `47957/24000 ≈ 1.99821 ≤ 2` (and `612486251/306516000 ≈ 1.99822` with the tail).
example : ThreeFreeThree.finalOK (7, 11, 13, 17) [5] (1, 12) = false := by decide +kernel
-- Tail factor alone: `m = (5, 7, 11, 13)`, `C = []`, `X = 151/1152`. Without the tail factor
-- the value is exactly `2`, which the earlier form accepts; with it, `357604/178801 > 2`.
example : ThreeFreeThree.finalOK (5, 7, 11, 13) [] (151, 1152) = false := by decide +kernel
-- Accepted at the boundary: `m = (7, 11, 13, 17)`, `C = [5]`, `X = 18070457/235404288`. The
-- current value is exactly `2`; the earlier one is `22171324/11175125 ≈ 1.98399`.
example : ThreeFreeThree.finalOK (7, 11, 13, 17) [5] (18070457, 235404288) = true := by
  decide +kernel

/-! ## Correction weights (`OddPerfect.corrBound`) -/

-- `OddPerfect/ReciprocalSumThree.lean` checks each table weight `w` by `corrBound p ≤ w / 10 ^ 15`.
-- The table weight of the prime 3 passes; the same weight less one fails, so the table holds
-- the least admissible value and the comparison is not vacuous.
example : corrBound 3 ≤ (72132645667761 : ℚ) / 1000000000000000 := by decide +kernel
example : ¬ (corrBound 3 ≤ (72132645667760 : ℚ) / 1000000000000000) := by decide +kernel

/-! ## Common fast checks (`OddPerfect.FamInst.fastPrime`, `rowChkP`, `reachS`) -/

-- `incr`, ordering premise of `fastPrime_sound`: a strictly increasing list is accepted.
example : FamInst.incr [3, 5, 7] = true := by decide +kernel
-- `incr`: the descending step `7, 5` is rejected (`Nat.blt 7 5`).
example : FamInst.incr [7, 5] = false := by decide +kernel
-- `incr`: equal neighbors are rejected (the order is strict).
example : FamInst.incr [3, 3, 5] = false := by decide +kernel
-- Raw behavior on a list that is not increasing: `tdl` stops at the first element `7` since
-- `25 < 7 * 7`, before it reaches the divisor `5`; `fastPrime_sound` assumes `incr L`.
example : FamInst.tdl 25 [7, 5] = true := by decide +kernel
-- `cover`, coverage premise: `[3, 5, 7]` holds every odd prime up to `7`; fuel `6` is exactly
-- enough (the values `3, ..., 7` and the final empty list).
example : FamInst.cover 6 3 [3, 5, 7] = true := by decide +kernel
-- `cover`: fuel `5` is exhausted before the empty list is reached (the clause `0 => false`).
example : FamInst.cover 5 3 [3, 5, 7] = false := by decide +kernel
-- `cover`: the prime `5` is omitted; `5 ≠ 7` and `hasDiv 5` fails.
example : FamInst.cover 10 3 [3, 7] = false := by decide +kernel
-- Contract boundary, part 1: the raw trial division Boolean with a trial list that omits `3`
-- classifies `9` as a candidate prime, since `9 < 5 * 5` at the first element.
example : FamInst.fastPrime [5, 7] 9 = true := by decide +kernel
-- Contract boundary, part 2: the coverage premise `cover f 3 L` of `fastPrime_sound` rejects
-- that list: `3 ≠ 5` and `hasDiv 3` fails.
example : FamInst.cover 10 3 [5, 7] = false := by decide +kernel
-- `cover`, raw behavior: a listed composite (`4`) is accepted; it is harmless, since the
-- soundness only needs every prime to be listed.
example : FamInst.cover 10 3 [3, 4, 5, 7] = true := by decide +kernel
-- `tdl`: no element of `[3, 5, 7]` divides `47`, and the walk stops at `7` (`47 < 49`).
example : FamInst.tdl 47 [3, 5, 7] = true := by decide +kernel
-- `tdl`: `7` divides `49` (and `49 < 7 * 7` fails).
example : FamInst.tdl 49 [3, 5, 7] = false := by decide +kernel
-- `tdl`, exhausted list: no element divides `53`, but `53 ≥ 7 * 7`, so the walk reaches the
-- clause `[] => false`.
example : FamInst.tdl 53 [3, 5, 7] = false := by decide +kernel
-- `fastPrime oddP`: odd primes accepted, including the last listed prime `4201`.
example : [3, 97, 9973, 4201].all (FamInst.fastPrime FamInst.oddP) = true := by decide +kernel
-- `fastPrime oddP`: `1` (not above `2`), `2` (even: the test is for odd numbers only) and the
-- prime square `97 * 97` (divisor `97`) are rejected.
example : [1, 2, 9409].any (FamInst.fastPrime FamInst.oddP) = false := by decide +kernel
-- `fastPrime oddP`, one sided above `4201 ^ 2 = 17648401`: the prime `17648461` is rejected,
-- because the walk exhausts `oddP` without meeting `q < p * p`.
example : FamInst.fastPrime FamInst.oddP 17648461 = false := by decide +kernel
-- `lensOK`, chunk shape: parts of length `2`, the last one shorter.
example : FamInst.lensOK 2 [[5, 11], [71]] = true := by decide +kernel
-- `lensOK`: a part other than the last is short.
example : FamInst.lensOK 2 [[5], [11, 71]] = false := by decide +kernel
-- `lensOK`: the last part is longer than `2`.
example : FamInst.lensOK 2 [[5, 11], [71, 3, 7]] = false := by decide +kernel
-- `ptD`, chunk boundaries: index `2` reads entry `0` of part `1`; index `3` is past the end.
example : [0, 1, 2, 3].map (FamInst.ptD 2 [[5, 11], [71]]) = [5, 11, 71, 0] := by
  decide +kernel
-- `rowChkP`, well formed: `11 * 71 = 781 = 1 + 5 + 5 ^ 2 + 5 ^ 3 + 5 ^ 4`.
example : FamInst.rowChkP 2 [[5, 11], [71]] 5 (5, [1, 2]) = true := by decide +kernel
-- `rowChkP`, altered row: `71` does not divide `1 + 11 + ... + 11 ^ 4 = 16105`.
example : FamInst.rowChkP 2 [[5, 11], [71]] 5 (11, [2]) = false := by decide +kernel
-- `rowChkP`: index `3` is past the end and reads `0`, which divides nothing here.
example : FamInst.rowChkP 2 [[5, 11], [71]] 5 (5, [1, 3]) = false := by decide +kernel
-- Raw behavior on misshaped parts: index `4` is read as entry `0` of part `2`, the node `11`,
-- so the row passes; `rowChk_of_rowChkP` assumes `lensOK`, which rejects these parts, and on
-- the flattened list `[5, 7, 3, 11]` index `4` is past the end and `rowChk` rejects the row.
example : FamInst.rowChkP 2 [[5, 7], [3], [11]] 5 (5, [4]) = true := by decide +kernel
example : FamInst.lensOK 2 [[5, 7], [3], [11]] = false := by decide +kernel
example : FamInst.rowChk 5 [5, 7, 3, 11] (5, [4]) = false := by decide +kernel
-- `reachS`, well formed: with nothing blocked the seed `5` reaches the target mask `6`.
example : FamInst.reachS [5, 11, 71] [[1, 2]] 1 6 1 (fun _ => false) = true := by
  decide +kernel
-- `reachS`, blocked seed: the blocked set `x ≡ 1 (mod 4)` contains `5`, so its row is skipped.
example : FamInst.reachS [5, 11, 71] [[1, 2]] 1 6 1 (fun x => x % 4 == 1) = false := by
  decide +kernel
-- `reachS`, fuel: zero passes leave the seed mask `1`.
example : FamInst.reachS [5, 11, 71] [[1, 2]] 1 6 0 (fun _ => false) = false := by
  decide +kernel
-- `reachS`, row order: bit `3` is set by row `1`, whose own bit is set only by the later row
-- `2`; one pass is not enough, two passes are.
example : FamInst.reachS [5, 7, 11, 13] [[2], [3], [1]] 1 8 1 (fun _ => false) = false := by
  decide +kernel
example : FamInst.reachS [5, 7, 11, 13] [[2], [3], [1]] 1 8 2 (fun _ => false) = true := by
  decide +kernel
-- `reachS`, target semantics: bits of the seed mask count as reached, so `ns = 3` meets the
-- target `6` with zero passes and every source blocked; sound because `dvd_of_reach` assumes
-- that the first `ns` nodes divide `N`.
example : FamInst.reachS [5, 11, 71] [[1, 2]] 3 6 0 (fun _ => true) = true := by decide +kernel
-- Coverage premise of `hcand_of_groups`: the candidate seed `5` lies in no blocked set.
example : ([5, 11, 71].take 1).all
    (fun b => !(b % 4 == 1) || [fun x : ℕ => x == 13].any fun f => f b) = false := by
  decide +kernel

/-! ## The restrained exclusion tree checker (`OddPerfect.RestrainedSeven.chk`, `rowsOK`) -/

-- `oddPrime`: odd primes accepted, up to the largest prime below `1000000`.
example : [3, 5, 97, 999983].all RestrainedSeven.oddPrime = true := by decide +kernel
-- `oddPrime`: `0`, `1`, `2` (below `3`) and odd composites rejected.
example : [0, 1, 2, 9, 25, 91].any RestrainedSeven.oddPrime = false := by decide +kernel
-- `tdiv`, fuel: three steps reach `7` with `47 < 7 * 7`; two steps run out (`0 => false`).
example : RestrainedSeven.tdiv 47 3 3 = true ∧ RestrainedSeven.tdiv 47 2 3 = false := by
  decide +kernel
-- `isPr`, a Pratt certificate above `1000000`: `2` has order `1000428 = 2 ^ 2 3 11 ^ 2 13 53`.
example : RestrainedSeven.isPr [(1000429, 2, [2, 2, 3, 11, 11, 13, 53])] 1000429 = true := by
  decide +kernel
-- `isPr`, bad Pratt certificate: `3` does not have order `1000428` modulo `1000429`.
example : RestrainedSeven.isPr [(1000429, 3, [2, 2, 3, 11, 11, 13, 53])] 1000429 = false := by
  decide +kernel
-- `isPr`, one sided: above `1000000` a prime without a certificate is rejected.
example : RestrainedSeven.isPr [] 1000429 = false := by decide +kernel
-- `isPr`: a valid certificate of another prime does not certify `1000777`.
example : RestrainedSeven.isPr [(1000429, 2, [2, 2, 3, 11, 11, 13, 53])] 1000777 = false := by
  decide +kernel
-- `chkRoot`, accepted: `σ(5 ^ 2) = 31` is closed by the prime `31` of the mask.
example : RestrainedSeven.chkRoot (2 ^ 31) 5 .skip (.kill 31) = true := by decide +kernel
-- Wrong kill prime: `7` does not divide `31` (`src % t == 0`).
example : RestrainedSeven.chkRoot (2 ^ 7) 5 .skip (.kill 7) = false := by decide +kernel
-- Kill prime not yet excluded: bit `31` is not set in the mask (`M.testBit t`).
example : RestrainedSeven.chkRoot 0 5 .skip (.kill 31) = false := by decide +kernel
-- Composite kill value: `57 = 3 * 19` divides `σ(7 ^ 2) = 57` and its bit is set, but
-- `oddPrime 57` fails.
example : RestrainedSeven.chkRoot (2 ^ 57) 7 .skip (.kill 57) = false := by decide +kernel
-- Accepted node: `σ(31 ^ 2) = 993 = 3 * 331`; at the prime `331 ≢ 1 (mod 12)` the source
-- `σ(331 ^ 2) = 109893` is divisible by `3`.
example : RestrainedSeven.chkRoot (2 ^ 3) 31 .skip (.node 331 [] .skip (.kill 3)) = true := by
  decide +kernel
-- A node at `3` is rejected (`t != 3`), although `3 ∣ 993` and its subtree closes `13`.
example : RestrainedSeven.chkRoot (2 ^ 3 ||| 2 ^ 13) 31 .skip (.node 3 [] .skip (.kill 13)) =
    false := by decide +kernel
-- Even and excluded row primes: `p % 2 == 1` rejects `4`, `p != 3` rejects `3`.
example : RestrainedSeven.chkRoot (2 ^ 7) 4 .skip (.kill 7) = false := by decide +kernel
example : RestrainedSeven.chkRoot (2 ^ 13) 3 .skip (.kill 13) = false := by decide +kernel
-- Raw behavior: no primality test of the row value; `9 ^ 2 + 9 + 1 = 91 = 7 * 13` is closed by
-- `7`. A row is only used when its value is prime, and the soundness reads only the prime bits
-- of the mask, so the bit `9` set by such a row carries no claim.
example : RestrainedSeven.chkRoot (2 ^ 7) 9 .skip (.kill 7) = true := by decide +kernel
-- Root `13 ≡ 1 (mod 12)`: the branch `13 = q` closes `14` by `7`, the branch of exponent `2`
-- closes `183 = 3 * 61` by `61`.
example : RestrainedSeven.chkRoot (2 ^ 7 ||| 2 ^ 61) 13 (.kill 7) (.kill 61) = true := by
  decide +kernel
-- The same root without the branch `13 = q` (`skip` is never accepted).
example : RestrainedSeven.chkRoot (2 ^ 7 ||| 2 ^ 61) 13 .skip (.kill 61) = false := by
  decide +kernel
-- Forced prime that may be the special prime: `σ(29 ^ 2) = 871 = 13 * 67`, and the node `13`
-- needs both branches while `q` is not fixed.
example : RestrainedSeven.chkRoot (2 ^ 7 ||| 2 ^ 61) 29 .skip
    (.node 13 [] (.kill 7) (.kill 61)) = true := by decide +kernel
example : RestrainedSeven.chkRoot (2 ^ 7 ||| 2 ^ 61) 29 .skip
    (.node 13 [] .skip (.kill 61)) = false := by decide +kernel
-- Once `q = 13` is fixed, a node at `13` is rejected (`t != qv`); with `qv = 0` it is accepted.
example : RestrainedSeven.chk (2 ^ 7 ||| 2 ^ 61) 13 91 (.node 13 [] (.kill 7) (.kill 61)) =
    false := by decide +kernel
example : RestrainedSeven.chk (2 ^ 7 ||| 2 ^ 61) 0 91 (.node 13 [] (.kill 7) (.kill 61)) =
    true := by decide +kernel
-- `rowsOK`, order of exclusions: the row of `31` kills by `3` and sets bit `31`; the row of `5`
-- then kills `31`.
example : RestrainedSeven.rowsOK 8 [(31, .skip, .kill 3), (5, .skip, .kill 31)]
    (8 ||| 2 ^ 31 ||| 2 ^ 5) = true := by decide +kernel
-- `rowsOK`: in the reverse order the row of `5` uses bit `31` before it is set.
example : RestrainedSeven.rowsOK 8 [(5, .skip, .kill 31), (31, .skip, .kill 3)]
    (8 ||| 2 ^ 31 ||| 2 ^ 5) = false := by decide +kernel
-- `rowsOK`: the final mask must be the mask after the rows (`M == M'`).
example : RestrainedSeven.rowsOK 8 [(31, .skip, .kill 3)] 8 = false := by decide +kernel
-- `cover`: `5` and `7` by bits, `6`, `8`, `9` by the divisors `2`, `3`.
example : RestrainedSeven.cover (2 ^ 5 ||| 2 ^ 7) [2, 3] 5 5 = true := by decide +kernel
-- `cover`, gap between segments: `[5, 7)` and `[8, 10)` pass, but they are not adjacent, and
-- the range `[5, 10)` fails at the prime `7`, whose bit is not set.
example : RestrainedSeven.cover (2 ^ 5) [2, 3] 5 2 = true ∧
    RestrainedSeven.cover (2 ^ 5) [2, 3] 8 2 = true := by decide +kernel
example : RestrainedSeven.cover (2 ^ 5) [2, 3] 5 5 = false := by decide +kernel
-- `cover`: a divisor must be proper (`d < m`) and at least `2`.
example : RestrainedSeven.cover 0 [5] 5 1 = false ∧ RestrainedSeven.cover 0 [1] 7 1 = false := by
  decide +kernel

/-! ## Certified rows of the largest prime factor search (`OddPerfect.LPF2.rowOK`) -/

-- Bound `B = 11`: `P = [3, 5, 7, 11]`, `M = 2 * 3 * 5 * 7 * 11 = 2310`, `D = 2 * 4 * 6 * 10`.
-- `killP`, accepted: `σ(3 ^ 2) = 13`; neither `3` nor `2 * 3 + 1 = 7` divides it.
example : LPF2.killP 11 3 3 1 = true := by decide +kernel
-- `killP`, bad residue: `σ(3 ^ 4) = 121` is divisible by `2 * 5 + 1 = 11 ≤ B` (`candOK`).
example : LPF2.killP 11 3 5 1 = false := by decide +kernel
-- `killP`, target semantics: for `B = 9` the candidate `11` is above the bound and is not
-- tested, which is right: `11 > 9` is a prime factor above the bound.
example : LPF2.killP 9 3 5 1 = true := by decide +kernel
-- `killP`: `r = 3` divides the quotient `σ(7 ^ 2) = 57` (`gs / S % r`); dividing by `S = 3`
-- first leaves `19`, which passes.
example : LPF2.killP 11 7 3 1 = false ∧ LPF2.killP 11 7 3 3 = true := by decide +kernel
-- `killP`: the divisor `S = 13` leaves the quotient `1` (`Nat.blt 1`).
example : LPF2.killP 11 3 3 13 = false := by decide +kernel
-- `primeOK`, prime coverage: with `X = [5]` every prime `r ≤ 5` is listed or killed; without
-- it the prime `5` is neither listed nor killed (`killP 11 3 5 1` fails).
example : LPF2.primeOK 11 3 5 [5] [3, 5, 7, 11] [] = true ∧
    LPF2.primeOK 11 3 5 [] [3, 5, 7, 11] [] = false := by decide +kernel
-- `listOK`: the exponents `e ≤ 4` with `e + 1 ∣ 10 ^ 20` are `4, 3, 1`; omitting `3` fails.
example : LPF2.listOK (10 ^ 20) 4 [4, 3, 1] = true ∧ LPF2.listOK (10 ^ 20) 4 [4, 1] = false := by
  decide +kernel
-- `rowOK`, accepted: the row `[4]` of `3` (`σ(3 ^ 4) = 11 ^ 2`, so `4` is admissible).
example : LPF2.rowOK 11 2310 (10 ^ 20) [3, 5, 7, 11] [4, 3, 1] (3, [4], [5], [], []) = true := by
  decide +kernel
-- `rowOK`, omitted row entry: `4` passes the parity test, is not in the row, `5 ∣ xpow [5]`,
-- and no further kill applies (`L.all`).
example : LPF2.rowOK 11 2310 (10 ^ 20) [3, 5, 7, 11] [4, 3, 1] (3, [], [5], [], []) = false := by
  decide +kernel
-- `rowOK`: `XU = 10 ^ 19` is not a multiple of `xpow [5] = 10 ^ 20`.
example : LPF2.rowOK 11 2310 (10 ^ 19) [3, 5, 7, 11] [4, 3, 1] (3, [4], [5], [], []) = false := by
  decide +kernel
-- `rowOK`: the further kill `(5, 1)` fails `killOK`, since `gcd(121, 2310) = 11`.
example : LPF2.rowOK 11 2310 (10 ^ 20) [3, 5, 7, 11] [4, 3, 1]
    (3, [], [5], [], [(5, 1)]) = false := by decide +kernel
-- Wrong modulus product: with `M = 210`, which omits `11`, the same kill passes `killOK`; the
-- premise `2 * P.prod = M` of `exists_primeFactor_gt_of_cert` rejects `210`.
example : LPF2.killOK 210 3 5 1 = true := by decide +kernel
example : 2 * [3, 5, 7, 11].prod ≠ 210 := by decide +kernel
-- Prime coverage of `primesUpTo_eq_filter`: `primeBy` with the trial list `[2, 5]`, which omits
-- `3`, accepts `9`; the premise needs every prime up to `K` in the list, and `[2, 3]` rejects it.
example : LPF2.primeBy [2, 5] 9 = true ∧ LPF2.primeBy [2, 3] 9 = false := by decide +kernel
example : LPF.primesUpTo 11 = [3, 5, 7, 11] := by decide +kernel
-- `LPF.search` for `B = 11`: fuel `3` closes every branch; fuel `2` is exhausted (`0 => false`).
example : LPF.search 11 [3, 5, 7, 11] 2310 480 [] 3 [] [] [] = true := by decide +kernel
example : LPF.search 11 [3, 5, 7, 11] 2310 480 [] 2 [] [] [] = false := by decide +kernel

/-! ## The fast search step for two large primes (`OddPerfect.SLP.expandF`, `runF`) -/

-- Equality of search states is decided through a long product type; the default instance search
-- size is too small for it.
set_option synthInstance.maxSize 2048

-- Tiny states for `B = 5`, `M = 30`. A closed state: the exact entries `3 ^ 2 5 ^ 2 7 ^ 2`
-- give the lower abundancy `22971 / 11025 ≥ 2`.
example : SLP.expandF 5 30 10 ([(3, 3, 2), (5, 3, 2), (7, 3, 2)], 0, 0, 0, 0, 0, false) =
    some [] := by decide +kernel
example : SLP.expandF 5 30 10 ([(3, 3, 2), (5, 3, 2), (7, 3, 2)], 0, 0, 0, 0, 0, false) =
    SLP.expand 5 30 10 ([(3, 3, 2), (5, 3, 2), (7, 3, 2)], 0, 0, 0, 0, 0, false) := by
  decide +kernel
-- A failing state with entry code `4` (treated as dividing, but never picked): no undecided
-- entry, no pinned prime, no entry of code `2`, so the step is stuck (`none`).
example : SLP.expandF 5 30 10 ([(3, 4, 0), (5, 4, 0), (7, 4, 0)], 0, 0, 0, 0, 0, false) =
    none := by decide +kernel
example : SLP.expandF 5 30 10 ([(3, 4, 0), (5, 4, 0), (7, 4, 0)], 0, 0, 0, 0, 0, false) =
    SLP.expand 5 30 10 ([(3, 4, 0), (5, 4, 0), (7, 4, 0)], 0, 0, 0, 0, 0, false) := by
  decide +kernel
-- The same entries with code `2` are picked by `pickBest`; the two steps still agree.
example : SLP.expandF 5 30 10 ([(3, 2, 0), (5, 2, 0), (7, 2, 0)], 0, 0, 0, 0, 0, false) =
    SLP.expand 5 30 10 ([(3, 2, 0), (5, 2, 0), (7, 2, 0)], 0, 0, 0, 0, 0, false) := by
  decide +kernel
-- Child order at an undecided entry (window `W = 0`): first `3` divides with the least exponent
-- `2`, then `3` is excluded; the bounds become `lo = 1`, `hi = 3`.
example : SLP.expandF 5 30 0 ([(3, 0, 0)], 0, 0, 0, 0, 0, false) =
    some [([(3, 2, 2)], 0, 1, 3, 0, 0, false), ([(3, 1, 0)], 0, 1, 3, 0, 0, false)] := by
  decide +kernel
example : SLP.expandF 5 30 0 ([(3, 0, 0)], 0, 0, 0, 0, 0, false) =
    SLP.expand 5 30 0 ([(3, 0, 0)], 0, 0, 0, 0, 0, false) := by decide +kernel
-- `runF`: zero fuel returns the stack unchanged; a stuck state gives `none`; three steps agree
-- with `run`.
example : SLP.runF 5 30 0 0 [([(3, 0, 0)], 0, 0, 0, 0, 0, false)] =
    some [([(3, 0, 0)], 0, 0, 0, 0, 0, false)] := by decide +kernel
example : SLP.runF 5 30 10 2 [([(3, 4, 0), (5, 4, 0), (7, 4, 0)], 0, 0, 0, 0, 0, false)] =
    none := by decide +kernel
example : SLP.runF 5 30 0 3 [([(3, 0, 0)], 0, 0, 0, 0, 0, false)] =
    SLP.run 5 30 0 3 [([(3, 0, 0)], 0, 0, 0, 0, 0, false)] := by decide +kernel

/-! ## The mixed index tree checker (`OddPerfect.MixedIndex.chk`) -/

-- Accepted tiny tree: `3 ^ 2 5 11 ^ 2 13 ^ 2` is abundant.
example : MixedIndex.chk [] [11, 13] [] 0 0 (.abund [(11, 2), (13, 2)]) = true := by
  decide +kernel
-- `11` is not a known prime factor (`entOK`: `K.contains`).
example : MixedIndex.chk [] [13] [] 0 0 (.abund [(11, 2), (13, 2)]) = false := by
  decide +kernel
-- Capacity of an entry: exponent `4` needs a recorded index divisor `k ≥ 5` (`entOK`).
example : MixedIndex.chk [] [11, 13] [] 0 0 (.abund [(11, 4), (13, 2)]) = false := by
  decide +kernel
-- Accepted node at `11`: index `3` is shut by `7 ∣ 133`; index `5` records `(11, 5)`, which
-- allows the exponent `4`; index `7` forces the certified prime `43 ∣ 1948717`.
example : MixedIndex.chk [43] [11, 13] [] 0 0 (.node 11 (.shut 11 3)
    (.force 11 5 [] (.abund [(11, 4), (13, 2)]))
    (.force 11 7 [43] (.abund [(11, 2), (13, 2)]))) = true := by decide +kernel
-- The same tree with `43` missing from the certified primes (`P.contains r`).
example : MixedIndex.chk [] [11, 13] [] 0 0 (.node 11 (.shut 11 3)
    (.force 11 5 [] (.abund [(11, 4), (13, 2)]))
    (.force 11 7 [43] (.abund [(11, 2), (13, 2)]))) = false := by decide +kernel
-- Wrong prime: `47` is certified but does not divide `1948717` (`geomS p (k - 1) % r == 0`).
example : MixedIndex.chk [47] [11, 13] [] 0 0 (.node 11 (.shut 11 3)
    (.force 11 5 [] (.abund [(11, 4), (13, 2)]))
    (.force 11 7 [47] (.abund [(11, 2), (13, 2)]))) = false := by decide +kernel
-- Branches out of order: the branch for index `3` is a rule for index `5` (`isAt p 3 c3`).
example : MixedIndex.chk [43] [11, 13] [] 0 0 (.node 11
    (.force 11 5 [] (.abund [(11, 4), (13, 2)])) (.shut 11 3)
    (.force 11 7 [43] (.abund [(11, 2), (13, 2)]))) = false := by decide +kernel
-- Capacity rule for `3`: `3 ∣ 183 = σ(13 ^ 2)` shuts only with another known sender of `3`:
-- rejected with no sender, accepted with the sender `11`, rejected with the sender `13` itself.
example : MixedIndex.chk [] [13] [] 0 0 (.shut 13 3) = false := by decide +kernel
example : MixedIndex.chk [] [13] [] 11 0 (.shut 13 3) = true := by decide +kernel
example : MixedIndex.chk [] [13] [] 13 0 (.shut 13 3) = false := by decide +kernel
-- `force` at a second sender of `3`: accepted while no sender is known, rejected once the
-- sender `11` is known (`geomS p (k - 1) % 3 != 0 || a3 == 0`).
example : MixedIndex.chk [61] [11, 13] [] 0 0 (.force 13 3 [61] (.abund [(11, 2), (13, 2)])) =
    true := by decide +kernel
example : MixedIndex.chk [61] [11, 13] [] 11 0 (.force 13 3 [61] (.abund [(11, 2), (13, 2)])) =
    false := by decide +kernel
-- Raw behavior: `chk` trusts `P`; with the composite `183` listed it is forced. `chk_sound`
-- assumes that every element of `P` is prime.
example : MixedIndex.chk [183] [11, 13] [] 0 0
    (.force 13 3 [183] (.abund [(11, 2), (13, 2)])) = true := by decide +kernel
-- Raw behavior: a root rule is not tied to `K`; `chk_sound` assumes that every root rule
-- `isAt p k` has `p ∈ K` and `k ∣ v_p(N) + 1`, and the final tree has a `node` root.
example : MixedIndex.chk [] [] [] 0 0 (.shut 11 3) = true := by decide +kernel
-- Certified primes of the data module (`MixedIndex.primeB`): `101` has a Pratt entry; `91`
-- fails trial division; `183` has no entry. A bad Pratt entry: `5` has order `25` modulo `101`.
example : MixedIndex.primeB 101 = true := by decide +kernel
example : [91, 183].any MixedIndex.primeB = false := by decide +kernel
example : Pratt.check [(101, 5, [2, 2, 5, 5])] = false := by decide +kernel

/-! ## The mixed index tree checker with cuts (`OddPerfect.MixedIndexThree.chk3`) -/

-- Accepted tree with a cut. Fixed part `3 ^ 2 5`; index `3` of `11` is shut by `7 ∣ 133`;
-- index `5` records `(11, 5)` and makes `11` the sender of `5`, as `5 ∣ 16105`, then cuts; the
-- cut state `([11, 13], [(11, 5)], [], 11)` is in `Acc`; index `7` forces `43 ∣ 1948717`.
example : MixedIndexThree.chk3 [43] [(3, 2), (5, 1)] 0 false [([11, 13], [(11, 5)], [], 11)]
    [11, 13] [] [] 0 (.node 11 (.shut 11 3) (.force 11 5 [] .cut)
      (.force 11 7 [43] (.abund [(11, 2), (13, 2)]))) = true := by decide +kernel
-- The same tree with `Acc` empty: the cut has no excluded state to match (`Acc.contains`).
example : MixedIndexThree.chk3 [43] [(3, 2), (5, 1)] 0 false []
    [11, 13] [] [] 0 (.node 11 (.shut 11 3) (.force 11 5 [] .cut)
      (.force 11 7 [43] (.abund [(11, 2), (13, 2)]))) = false := by decide +kernel
-- Stated cut state does not match the state reached: the sender of `5` is given as `0`.
example : MixedIndexThree.chk3 [43] [(3, 2), (5, 1)] 0 false [([11, 13], [(11, 5)], [], 0)]
    [11, 13] [] [] 0 (.node 11 (.shut 11 3) (.force 11 5 [] .cut)
      (.force 11 7 [43] (.abund [(11, 2), (13, 2)]))) = false := by decide +kernel
-- Cut state that drops the known prime `13`.
example : MixedIndexThree.chk3 [43] [(3, 2), (5, 1)] 0 false [([11], [(11, 5)], [], 11)]
    [11, 13] [] [] 0 (.node 11 (.shut 11 3) (.force 11 5 [] .cut)
      (.force 11 7 [43] (.abund [(11, 2), (13, 2)]))) = false := by decide +kernel
-- A chunk is checked from its own state: `11 ^ 4` is allowed from the state reached after
-- the index `5` of `11`, and rejected from a start state that does not record that index
-- (`entOK`).
example : MixedIndexThree.chk3 [] [(3, 2), (5, 1)] 0 false []
    [11, 13] [(11, 5)] [] 11 (.abund [(11, 4), (13, 2)]) = true := by decide +kernel
example : MixedIndexThree.chk3 [] [(3, 2), (5, 1)] 0 false []
    [11, 13] [] [] 11 (.abund [(11, 4), (13, 2)]) = false := by decide +kernel
-- Abundancy bound on the wrong side: `σ(3 ^ 2 5 11 ^ 2) = 10374 < 2 3 ^ 2 5 11 ^ 2 = 10890`.
example : MixedIndexThree.chk3 [] [(3, 2), (5, 1)] 0 false []
    [11, 13] [] [] 0 (.abund [(11, 2)]) = false := by decide +kernel
-- Branch list that omits the index `7`: the third branch repeats the rule for index `5`
-- (`isAt p 7 t7`).
example : MixedIndexThree.chk3 [43] [(3, 2), (5, 1)] 0 false [([11, 13], [(11, 5)], [], 11)]
    [11, 13] [] [] 0 (.node 11 (.shut 11 3) (.force 11 5 [] .cut)
      (.force 11 5 [] .cut)) = false := by decide +kernel
-- Forced prime missing from the certified primes (`P.contains r`).
example : MixedIndexThree.chk3 [] [(3, 2), (5, 1)] 0 false [([11, 13], [(11, 5)], [], 11)]
    [11, 13] [] [] 0 (.node 11 (.shut 11 3) (.force 11 5 [] .cut)
      (.force 11 7 [43] (.abund [(11, 2), (13, 2)]))) = false := by decide +kernel
-- Cap at `3`: `3 ∣ 183 = σ(13 ^ 2)`. With the sender `11` known, `13` and the special component
-- give `3` senders, so the cap `2` shuts; the cap `3` does not, nor the cap `0` (off).
example : MixedIndexThree.chk3 [] [] 2 false [] [13] [] [11] 0 (.shut 13 3) = true := by
  decide +kernel
example : MixedIndexThree.chk3 [] [] 3 false [] [13] [] [11] 0 (.shut 13 3) = false := by
  decide +kernel
example : MixedIndexThree.chk3 [] [] 0 false [] [13] [] [11] 0 (.shut 13 3) = false := by
  decide +kernel
-- Cap at `3` with `13` itself listed as the known sender: it is not counted twice (`nd`).
example : MixedIndexThree.chk3 [] [] 2 false [] [13] [] [13] 0 (.shut 13 3) = false := by
  decide +kernel
-- Raw behavior: `chk3` trusts `P`; with the composite `183` listed it is forced.
-- `chk3_sound` assumes that every element of `P` is prime.
example : MixedIndexThree.chk3 [183] [(3, 2), (5, 1)] 0 false [] [11, 13] [] [] 0
    (.force 13 3 [183] (.abund [(11, 2), (13, 2)])) = true := by decide +kernel
-- Certified primes of the data modules (`MixedIndexThree.primeB`): `1017061` has a Pratt entry;
-- `1891 = 31 61` fails trial division; `1000001 = 101 9901` is above `10 ^ 6` and has no entry.
example : MixedIndexThree.primeB 1017061 = true := by decide +kernel
example : [1891, 1000001].any MixedIndexThree.primeB = false := by decide +kernel
-- Pratt entries: the entry of `1017061` is accepted; the composite `1017147 = 3 339049`, with
-- `1017146 = 2 13 19 29 71` factored correctly, fails `18 ^ 1017146 ≡ 1`.
example : Pratt.checkAux [] [(1017061, 18, [2, 2, 3, 5, 11, 23, 67])] = true := by
  decide +kernel
example : Pratt.checkAux [] [(1017147, 18, [2, 13, 19, 29, 71])] = false := by decide +kernel

end CheckerControls

/-! ## The two exception checker engine (`OddPerfect.TwoExcEngine.go`, `check`, `checkV`) -/

namespace CheckerControls.Engine

open OddPerfect.TwoExcEngine

/-- Exponent 2 at 3, two exceptions, landed facts off. -/
def pA : Params := { E := 2, MHIT := 0, KCAP := 64, landed := false }
/-- As `pA` with the landed facts on. -/
def pL : Params := { pA with landed := true }
/-- No exception allowed. -/
def p0 : Params := { pA with E := 0 }
/-- Exponent 4 at 3, every other exception of exponent 4 (the family S2a). -/
def p4e : Params := { E := 3, MHIT := 0, KCAP := 64, landed := false, V3 := 4, e4 := true }
/-- The parameters of the published certificate of the family S1 (exponent 6 at 3). -/
def pS1 : Params :=
  { E := 2, MHIT := 1000000000000000000000000000000, KCAP := 64, landed := false, V3 := 6,
    e4 := true }
/-- A recognizer that accepts every state. It does not satisfy the hypothesis `hdone` of
`check_sound` and `checkV_sound`: the controls that use it isolate a Boolean guard and are not
sound certificates. -/
def doneAll : List Key → ℕ → Bool := fun _ _ => true
/-- A record without items that hands its state to `done`. -/
def stub : Cert := .apply [] (.closed .ext)
/-- A key list with the special prime `5` (not exact) and the squares `3, 7, 11, 17`. -/
def ksS : List Key :=
  [⟨3, .sq, []⟩, ⟨5, .fr true 2 false 1 false, []⟩, ⟨7, .sq, []⟩, ⟨11, .sq, []⟩,
    ⟨17, .sq, []⟩]
/-- A square key. -/
def sqKey (p : ℕ) : Key := ⟨p, .sq, []⟩
/-- The odd primes from `3` through `997` (167 numbers). -/
def oddPrimesTo997 : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
    193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
    293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401,
    409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509,
    521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631,
    641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
    757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877,
    881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]
/-- The state of the deficient leaf of record 342 of
`scripts/ExcessFour/cert_ex_S1_100000_nojump_nolanded.jsonl`, as the Python mirror of the
checker computes it (the record stores no state). -/
def ksS1 : List Key :=
  [⟨3, .fr false 7 false 6 true, [(1093, 1), (5, 1)]⟩,
    ⟨5, .fr true 2 false 1 false, [(398581, 1)]⟩,
    ⟨1093, .sq, [(3, 1)]⟩, ⟨398581, .fr false 5 true 4 true, [(1093, 1)]⟩]
/-- The leaf data of that record, as `scripts/TwoExceptionTwo/engine.py` (`defdata_trivial`)
translates it. -/
def ddS1 : DefData :=
  { k := 24, B := 1000000, rs := [], rx := 1000001, mL := (1, 1), mM := (1, 10000000000000),
    comps := [] }

-- `paramsOK`: the exponent of 3 is 2 or an even number at least 4.
example : [2, 4, 6, 36].all (fun v => paramsOK { pA with V3 := v }) = true := by decide +kernel
example : [0, 1, 3, 5, 7, 35].any (fun v => paramsOK { pA with V3 := v }) = false := by
  decide +kernel
-- `Params.lan`: the landed facts are used only when asked for and with exponent 2 at 3.
example : pL.lan = true := by decide +kernel
example : [pA, { pL with V3 := 4 }, { pL with V3 := 6 }].any Params.lan = false := by
  decide +kernel
-- The root role of 3: a square for `V3 = 2`, an exact exception of exponent `V3` otherwise.
example : root3 pA = .sq ∧ rootKeysV pA = rootKeys := by decide +kernel
example : root3 pS1 = .fr false 7 false 6 true ∧
    rootKeysV p4e = [⟨3, .fr false 5 false 4 true, []⟩] := by decide +kernel
-- `budget3`: 2 for a square, `kmin` for an exact exception; none for a free prime that is not
-- exact or is the special prime.
example : budget3 .sq = some 2 ∧ budget3 (root3 pS1) = some 6 := by decide +kernel
example : [Role.fr false 7 false 6 false, .fr true 2 false 1 true, .fr true 6 false 5 false].all
    (fun r => (budget3 r).isNone) = true := by decide +kernel
-- 3 consumes exception budget exactly when `V3 ≠ 2`: with `E = 1` and `V3 = 6` no exception role
-- is left for `7`; with `V3 = 2` both classes of `7 ≡ 1 (mod 3)` are offered.
example : nexc (rootKeysV pS1) = 1 ∧ nexc (rootKeysV pA) = 0 := by decide +kernel
example : rolesOf { pA with E := 1, V3 := 6 } (rootKeysV { pA with E := 1, V3 := 6 }) 7 =
    [.sq] := by decide +kernel
example : rolesOf { pA with E := 1 } (rootKeysV { pA with E := 1 }) 7 =
    [.sq, .fr false 1 true 4 false, .fr false 3 false 8 false] := by decide +kernel
-- Ordinary and special roles: `13 ≡ 1 (mod 4)` and `≡ 1 (mod 3)` gets both special classes and
-- both exception classes; `5 ≡ 2 (mod 3)` one of each.
example : rolesOf pA rootKeys 13 = [.sq, .fr true 2 true 1 false, .fr true 6 false 5 false,
    .fr false 1 true 4 false, .fr false 3 false 8 false] := by decide +kernel
example : rolesOf pA rootKeys 5 = [.sq, .fr true 2 false 1 false, .fr false 1 false 4 false] := by
  decide +kernel
-- With the landed facts, `5` and `17 ≡ 8 (mod 9)` cannot be special, and the special class of
-- `29 ≡ 2 (mod 3)` gets `no3`.
example : rolesOf pL rootKeys 5 = [.sq, .fr false 1 false 4 false] ∧
    rolesOf pL rootKeys 17 = [.sq, .fr false 1 false 4 false] := by decide +kernel
example : rolesOf pL rootKeys 29 = [.sq, .fr true 2 true 1 false, .fr false 1 false 4 false] := by
  decide +kernel
-- The landed shortcut is off for `V3 ≠ 2` even when `landed`: `5` may be special again.
example : rolesOf { pL with V3 := 4 } (rootKeysV { pL with V3 := 4 }) 5 =
    [.sq, .fr true 2 false 1 false, .fr false 1 false 4 false] := by decide +kernel
-- Once the special prime is a key, no special role is offered.
example : rolesOf pA [⟨3, .sq, []⟩, ⟨5, .fr true 2 false 1 false, []⟩] 13 =
    [.sq, .fr false 1 true 4 false, .fr false 3 false 8 false] := by decide +kernel
-- `e4`: an exception other than 3 has the single role of exponent exactly 4; 3 keeps the general
-- class.
example : rolesOf p4e (rootKeysV p4e) 13 = [.sq, .fr true 2 true 1 false, .fr true 6 false 5 false,
    .fr false 5 true 4 true] := by decide +kernel
example : rolesOf p4e [] 7 = [.sq, .fr false 5 true 4 true] ∧
    rolesOf p4e [] 3 = [.sq, .fr false 1 false 4 false] := by decide +kernel
-- The guards of `check` and `checkV` (with `doneAll`, see its docstring): `check` only for
-- `V3 = 2` without `e4`; `checkV` for every admissible `V3`.
example : check pA primeB doneAll stub = true := by decide +kernel
example : [{ pA with V3 := 4 }, { pA with e4 := true }, p4e, pS1].any
    (fun P => check P primeB doneAll stub) = false := by decide +kernel
example : [pA, { pA with e4 := true }, p4e, pS1].all
    (fun P => checkV P primeB doneAll stub) = true := by decide +kernel
example : [{ pA with V3 := 0 }, { pA with V3 := 3 }, { p4e with V3 := 5 }].any
    (fun P => checkV P primeB doneAll stub) = false := by decide +kernel
-- Old `check` versus `checkV` on the same term: both start from `rootKeys` at `x = 5` when
-- `V3 = 2`; for `V3 = 6`, `checkV` starts from `rootKeysV pS1` and not from `rootKeys`. Like
-- `doneAll`, these recognizers do not satisfy `hdone`: they isolate the root state only.
example : check pA primeB (fun ks x => ks == rootKeys && x == 5) stub = true ∧
    checkV pA primeB (fun ks x => ks == rootKeys && x == 5) stub = true := by decide +kernel
example : checkV pS1 primeB (fun ks x => ks == rootKeys && x == 5) stub = false ∧
    checkV pS1 primeB (fun ks x => ks == rootKeysV pS1 && x == 5) stub = true := by
  decide +kernel
-- Malformed first constructors: the root must be a record.
example : [Cert.leaf, .ext, .closed .ext, .apply [] .ext, .force .nil, .abundant].any
    (checkV pA primeB doneAll) = false := by decide +kernel
example : [Cert.leaf, .ext, .closed .ext, .apply [] .ext, .force .nil, .abundant].any
    (check pA primeB doneAll) = false := by decide +kernel
-- Contributions of the root record (component 3, `σ(3 ^ 2) = 13`): `13 ^ 1` is accepted and
-- left pending, and it is no contradiction (the outcome `.nil` fails).
example : go pA primeB doneAll (.apply rootKeys 5 [] 3) (.apply [(13, 1)] (.closed .ext)) = true :=
  by decide +kernel
example : go pA primeB doneAll (.apply rootKeys 5 [] 3) (.apply [(13, 1)] .nil) = false := by
  decide +kernel
-- An excessive contribution `13 ^ 2 ∤ 13`, a duplicated one (merged to `13 ^ 2`), a zero weight.
example : go pA primeB doneAll (.apply rootKeys 5 [] 3) (.apply [(13, 2)] (.closed .ext)) = false :=
  by decide +kernel
example : go pA primeB doneAll (.apply rootKeys 5 [] 3)
    (.apply [(13, 1), (13, 1)] (.closed .ext)) = false := by decide +kernel
example : go pA primeB doneAll (.apply rootKeys 5 [] 3) (.apply [(13, 0)] (.closed .ext)) = false :=
  by decide +kernel
-- A prime below `x` that is not a key is a contradiction, if the oracle certifies it.
example : go pA primeB doneAll (.apply rootKeys 17 [] 3) (.apply [(13, 1)] .nil) = true := by
  decide +kernel
example : go pA (fun _ => false) doneAll (.apply rootKeys 17 [] 3)
    (.apply [(13, 1)] (.closed .ext)) = false := by decide +kernel
-- A square key over its budget 2 is a contradiction. The earlier contribution `(5, 2)` is made
-- up: this isolates the budget guard.
example : go pA primeB doneAll (.apply [⟨3, .sq, []⟩, ⟨13, .sq, [(5, 2)]⟩] 5 [] 3)
    (.apply [(13, 1)] .nil) = true := by decide +kernel
example : go pA primeB doneAll (.apply [⟨3, .sq, []⟩, ⟨13, .sq, [(5, 1)]⟩] 5 [] 3)
    (.apply [(13, 1)] .nil) = false := by decide +kernel
-- Role lists: with `E = 0` the forced prime `13` has three roles (square and two special
-- classes); exactly three children are accepted, two or four are not.
example : go p0 primeB doneAll (.apply rootKeys 5 [] 3)
    (.apply [(13, 1)] (.force (.cons stub (.cons stub (.cons stub .nil))))) = true := by
  decide +kernel
example : go p0 primeB doneAll (.apply rootKeys 5 [] 3)
    (.apply [(13, 1)] (.force (.cons stub (.cons stub .nil)))) = false := by decide +kernel
example : go p0 primeB doneAll (.apply rootKeys 5 [] 3)
    (.apply [(13, 1)] (.force (.cons stub (.cons stub (.cons stub (.cons stub .nil)))))) = false :=
  by decide +kernel
-- Nothing pending: no prime to force.
example : go p0 primeB doneAll (.apply rootKeys 5 [] 3) (.apply [] (.force (.cons stub .nil))) =
    false := by decide +kernel
-- Senders. `5` has order 16 modulo 17 and is special (`D = 2`), so `4 ∣ lcm 2 16` and it
-- cannot send to 17.
example : go p0 primeB doneAll (.out ksS 19 []) (.receipt 17 (.cons (.inf 5 16) .nil)) = true := by
  decide +kernel
-- `5` has order 5 modulo 11; `lcm 2 5 = 10` is admissible, so it is not infeasible, and the
-- feasible sender branch is accepted (with `doneAll`), but not with a wrong order.
example : go p0 primeB doneAll (.out ksS 19 []) (.receipt 11 (.cons (.inf 5 5) .nil)) = false := by
  decide +kernel
example : go p0 primeB doneAll (.out ksS 19 []) (.receipt 11 (.cons (.snd 5 5 stub) .nil)) = true :=
  by decide +kernel
example : go p0 primeB doneAll (.out ksS 19 []) (.receipt 11 (.cons (.snd 5 4 stub) .nil)) =
    false := by decide +kernel
-- A truncated sender list, a sender that is not the next free key.
example : go p0 primeB doneAll (.out ksS 19 []) (.receipt 11 .nil) = false := by decide +kernel
example : go p0 primeB doneAll (.out ksS 19 []) (.receipt 11 (.cons (.snd 3 5 stub) .nil)) =
    false := by decide +kernel
-- The receiver must be `≡ 2 (mod 3)` (`5` has order 6 modulo 7 and could send), and the
-- exceptions must be complete (`nexc ksS = 0 < 2`).
example : go p0 primeB doneAll (.out ksS 19 []) (.receipt 7 (.cons (.snd 5 6 stub) .nil)) =
    false := by decide +kernel
example : go pA primeB doneAll (.out ksS 19 []) (.receipt 17 (.cons (.inf 5 16) .nil)) = false := by
  decide +kernel
-- Splits of the free prime `5` (`D = 2`, `kmin = 1`): exact exponent 1, or the next admissible
-- exponent `5` (`6 ≡ 2 (mod 4)`). The recognizers read the new role only and do not satisfy
-- `hdone`.
example : go p0 primeB (fun ks _ => (findKey 5 ks).any fun k =>
    k.role == .fr true 2 false 1 true || k.role == .fr true 2 false 5 false) (.step ksS 19)
    (.split 5 stub stub) = true := by decide +kernel
example : go p0 primeB (fun ks _ => (findKey 5 ks).any fun k => k.role == .fr true 2 false 1 false)
    (.step ksS 19) (.split 5 stub stub) = false := by decide +kernel
-- Invalid splits: at a square key, at a prime that is not a key, at an exact key.
example : [11, 13].any (fun p => go p0 primeB doneAll (.step ksS 19) (.split p stub stub)) =
    false := by decide +kernel
example : go pS1 primeB doneAll (.step (rootKeysV pS1) 5) (.split 3 stub stub) = false := by
  decide +kernel
-- The scan: from `5` past the keys `5, 7, 11` to `13`.
example : scanNext ksS 5 = some 13 := by decide +kernel
-- The scan fuel: `scanNext` is the scan with exactly 1000 positions (pinned by definition).
example (ks : List Key) (x : ℕ) : scanNext ks x = scanAux ks 1000 x := rfl
-- With a key at every odd prime through 997, the scan from `3` (positions 3 to 1002) finds
-- nothing, and it finds `997` once its key is removed. Each costs about 4 s of kernel time.
example : scanNext (oddPrimesTo997.map sqKey) 3 = none := by decide +kernel
example : scanNext ((oddPrimesTo997.erase 997).map sqKey) 3 = some 997 := by decide +kernel
-- A real deficient leaf (record 342 of the S1 certificate, `x = 251`), directly and through the
-- step that scans from `242` to `251`.
example : deficientB pS1 ksS1 251 ddS1 = true := by decide +kernel
example : go pS1 primeB (fun _ _ => false) (.step ksS1 242) (.check ddS1) = true := by
  decide +kernel
-- The same leaf with one damaged witness. A zero denominator (this also makes `Sd = 0`, so the
-- tests `Sn < Sd` and `Sn < 3 * Sd` of both paths fail as well; the guards cannot be
-- separated).
example : [{ ddS1 with mL := (1, 0) }, { ddS1 with mM := (1, 0) }].any
    (deficientB pS1 ksS1 251) = false := by decide +kernel
-- Underestimated tail witnesses: `m_M = 10 ^ -14` and `m_L = 10 ^ -3` are too small.
example : [{ ddS1 with mM := (1, 100000000000000) }, { ddS1 with mL := (1, 1000) }].any
    (deficientB pS1 ksS1 251) = false := by decide +kernel
-- Wrong Rankin exponents: `k = 0` fails only `3 ≤ k`; `k = 6` fails only the bound on `m_M`.
example : [{ ddS1 with k := 0 }, { ddS1 with k := 6 }].any (deficientB pS1 ksS1 251) = false := by
  decide +kernel
-- `r_x = B` violates `B < r_x`.
example : deficientB pS1 ksS1 251 { ddS1 with rx := 1000000 } = false := by decide +kernel
-- The leaf needs the key 3 with a budget.
example : deficientB pS1 ksS1.tail 251 ddS1 = false := by decide +kernel
-- The Padé path of the final test. With `m_M = 2/9753` the same leaf has
-- `S = 252^2 * 2/(251^2 * 9753) ≈ 2.06702 * 10^-4` and `U0 ≈ 1.99959` (`u = 0`, `c + d = 16`, no
-- hits). The old path fails: `U0/(1 - S) ≥ 2`, as the literal test below shows. The Padé path
-- accepts: `U0 (S^2 + 4 S + 6)/(6 - 2 S) < 2`. Only the Padé path accepts for `S` from about
-- `2.06683 * 10^-4` (the old path fails from there on) to about `2.06705 * 10^-4` (exact
-- rational arithmetic).
example : (decide (252 ^ 2 * 2 < 251 * 251 * 9753) &&
    decide ((hiProd pS1 ksS1).1 * (251 * 251 + 251 + 1) ^ 16 * (251 * 251 * 9753) <
      2 * ((hiProd pS1 ksS1).2 * 251 ^ 32 * (251 * 251 * 9753 - 252 ^ 2 * 2)))) = false := by
  decide +kernel
example : deficientB pS1 ksS1 251 { ddS1 with mM := (2, 9753) } = true := by decide +kernel
example : go pS1 primeB (fun _ _ => false) (.step ksS1 242) (.check { ddS1 with mM := (2, 9753) }) =
    true := by decide +kernel
-- Both paths reject: `m_M = 1/2` (`S ≈ 0.504`, both product tests fail), `m_M = 3/2`
-- (`1 ≤ S ≈ 1.512 < 3`: only the Padé path is tried, and its product test fails), `m_M = 3`
-- (`S ≈ 3.024 ≥ 3`, both guards on `S` fail).
example : [{ ddS1 with mM := (1, 2) }, { ddS1 with mM := (3, 2) }, { ddS1 with mM := (3, 1) }].any
    (deficientB pS1 ksS1 251) = false := by decide +kernel

end CheckerControls.Engine
