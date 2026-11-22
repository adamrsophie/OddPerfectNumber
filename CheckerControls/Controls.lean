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

end CheckerControls
