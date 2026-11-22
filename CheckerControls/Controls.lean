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

end CheckerControls
