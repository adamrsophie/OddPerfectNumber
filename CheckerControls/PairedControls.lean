import OddPerfect.TwoExcEngineCode

/-!
# Paired controls of the two exception engine helpers

Regression controls, not part of the library: nothing imports this file and the library build
never compiles it. It is checked by `sh CheckerControls/run.sh`.

This whole file is the output of `python3 -I scripts/TwoExceptionTwo/paired.py emit`, unchanged
(`paired.py check FILE` compares a file with it). Each `example` fixes the value of one low level
helper of `OddPerfect/TwoExcEngineCode.lean` on one input vector; the value on the right is the
value that the Python mirror `scripts/TwoExceptionTwo/engine.py` computes on the same input. So
the kernel checks that the two sides agree on every vector. The pairs (Lean, then Python):
`findDiv` and `find_div`; `smallPrime` and `primeB` (table `PMASK` below 4096) and
`small_prime`; `powModE` and `pow_mod_e`; `pfacs` and `pfacs`; `ordOK` and `ord_ok`; `findKey`
and `key_find`; `lookupW` and `lookup_w`; `lookupP` and `lookup_p`; `qrTable` and `qrPass` and
`QR_MODS`, `QR_SETS` and `qr_pass`; `newton` and `newton`; `sqrtIfSq` and
`square_root_if_square`.

Where the mirror rejects (raises `Reject`) instead of returning a value, the Lean value is the
one that the rejection mirrors: for `square_root_if_square` a root `s` is `some (some s)`, the
result `None` (not a square) is `some none`, and a rejection (Newton did not settle) is the outer
`none`; for `ord_ok` a rejection (a factor list that fails its check) is `false`. A key of the
mirror `[p, role, cs]` is the key `⟨p, role, cs⟩`, and its `None` is `none`. The values of
`qrBits` are the bits of the masks of `qrTable` at `z`, on the Python side membership of `z` in
`QR_SETS`. Long numbers are written as `2 ^ a + b` or `(2 ^ a + b) ^ 2 + c`.
-/

namespace CheckerControls.Paired

open OddPerfect.TwoExcEngine

/-- The test bits of the square filter at `z`, one per modulus of `qrTable`. -/
def qrBits (z : ℕ) : List ℕ :=
  qrTable.map fun mm => Nat.land (Nat.shiftRight mm.2 (z % mm.1)) 1

/-- The empty key list. -/
def ksNil : List Key :=
  []

/-- A key list of the lookup vectors. -/
def ksA : List Key :=
  [⟨3, .sq, []⟩,
    ⟨5, (.fr true 2 false 1 false), [(13, 1)]⟩,
    ⟨7, .sq, [(3, 1), (5, 2)]⟩]

/-- A key list of the lookup vectors. -/
def ksDup : List Key :=
  [⟨7, .sq, []⟩,
    ⟨7, (.fr false 1 false 4 false), [(3, 1)]⟩]

/-- A key list of the lookup vectors. -/
def ksZero : List Key :=
  [⟨0, .sq, []⟩]

/-! ## Paired with engine.py: Trial division (`TwoExcEngine.findDiv`, `smallPrime`) -/

-- no fuel
example : findDiv 0 91 2 = 0 := by decide +kernel
-- out of domain: n = 0
example : findDiv 1 0 2 = 0 := by decide +kernel
-- out of domain: n = 1
example : findDiv 1 1 2 = 1 := by decide +kernel
-- start d = 0: 7 % 0 = 7, then 7 % 1 = 0
example : findDiv 2 7 0 = 1 := by decide +kernel
-- n = d = 0: 0 % 0 = 0
example : findDiv 1 0 0 = 0 := by decide +kernel
-- the divisor 7 of 91 = 7 * 13: fuel exactly enough
example : findDiv 6 91 2 = 7 := by decide +kernel
-- one step short
example : findDiv 5 91 2 = 0 := by decide +kernel
-- the prime 97: fuel exactly enough to pass its square root
example : findDiv 9 97 2 = 97 := by decide +kernel
-- one step short
example : findDiv 8 97 2 = 0 := by decide +kernel
-- start above the square root
example : findDiv 1 25 6 = 25 := by decide +kernel
-- start above the least divisor
example : findDiv 2 10 3 = 10 := by decide +kernel
-- 65537 ^ 2 from 65536: fuel exactly enough
example : findDiv 2 4295098369 65536 = 65537 := by decide +kernel
-- one step short
example : findDiv 1 4295098369 65536 = 0 := by decide +kernel
-- the prime 4295098403 from 65537: fuel exactly enough
example : findDiv 2 4295098403 65537 = 4295098403 := by decide +kernel
-- one step short
example : findDiv 1 4295098403 65537 = 0 := by decide +kernel
-- the prime 1073741789 below 2 ^ 30: fuel exactly enough
example : findDiv 32767 1073741789 2 = 1073741789 := by decide +kernel
-- one step short
example : findDiv 32766 1073741789 2 = 0 := by decide +kernel
example : smallPrime 0 = false := by decide +kernel
example : smallPrime 1 = false := by decide +kernel
example : smallPrime 2 = true := by decide +kernel
example : smallPrime 4 = false := by decide +kernel
example : smallPrime 91 = false := by decide +kernel
example : smallPrime 97 = true := by decide +kernel
example : smallPrime 4093 = true := by decide +kernel
example : smallPrime 65537 = true := by decide +kernel
-- the largest prime below 2 ^ 30
example : smallPrime 1073741789 = true := by decide +kernel
-- 2 ^ 30 - 1, divisible by 3
example : smallPrime 1073741823 = false := by decide +kernel

/-! ## Paired with engine.py: The prime table (`TwoExcEngine.primeB`, `PMASK`) -/

example : primeB 0 = false := by decide +kernel
example : primeB 1 = false := by decide +kernel
example : primeB 2 = true := by decide +kernel
example : primeB 4 = false := by decide +kernel
example : primeB 4093 = true := by decide +kernel
-- the last entry of the table
example : primeB 4095 = false := by decide +kernel
-- the first number above the table
example : primeB 4096 = false := by decide +kernel
-- 17 * 241
example : primeB 4097 = false := by decide +kernel
example : primeB 4099 = true := by decide +kernel
example : primeB 65537 = true := by decide +kernel
-- the number of table primes
example : (List.range 4096).countP primeB = 564 := by decide +kernel
-- the sum of the table primes
example : ((List.range 4096).filter primeB).sum = 1070091 := by decide +kernel
-- a hash of the ordered table primes
example : ((List.range 4096).filter primeB).foldl (fun a p => (a * 4099 + p) % 1000000007) 0 =
    121701987 := by decide +kernel

/-! ## Paired with engine.py: Orders (`TwoExcEngine.powModE`, `pfacs`, `ordOK`) -/

example : powModE 3 0 7 = 1 := by decide +kernel
-- modulus 1
example : powModE 3 0 1 = 0 := by decide +kernel
example : powModE 0 0 5 = 1 := by decide +kernel
example : powModE 2 10 1000 = 24 := by decide +kernel
-- base above the modulus
example : powModE 100 3 7 = 1 := by decide +kernel
-- out of domain: modulus 0, where a % 0 = a
example : powModE 5 3 0 = 125 := by decide +kernel
-- modulus 0
example : powModE 7 1 0 = 7 := by decide +kernel
-- modulus 1
example : powModE 2 100 1 = 0 := by decide +kernel
-- an exponent above 2 ^ 64
example : powModE 3 (2 ^ 64 + 13) 1000003 = 372792 := by decide +kernel
example : powModE 10 1000000000000000000 999999937 = 312824744 := by decide +kernel
-- out of domain
example : pfacs 0 = [] := by decide +kernel
-- out of domain
example : pfacs 1 = [] := by decide +kernel
example : pfacs 12 = [2, 2, 3] := by decide +kernel
example : pfacs 360 = [2, 2, 2, 3, 3, 5] := by decide +kernel
example : pfacs 1001 = [7, 11, 13] := by decide +kernel
-- 97 * 103
example : pfacs 9991 = [97, 103] := by decide +kernel
-- the order of 3 modulo 7
example : ordOK 6 3 7 = true := by decide +kernel
-- the order of 2 modulo 7
example : ordOK 3 2 7 = true := by decide +kernel
-- not a multiple of the order
example : ordOK 3 3 7 = false := by decide +kernel
-- a multiple of the order
example : ordOK 12 3 7 = false := by decide +kernel
-- a base above the modulus
example : ordOK 6 10 7 = true := by decide +kernel
-- g = 1 modulo p: d must be p
example : ordOK 7 8 7 = true := by decide +kernel
-- d = 0
example : ordOK 0 3 7 = false := by decide +kernel
-- g = 0
example : ordOK 1 0 7 = false := by decide +kernel
example : ordOK 16 5 17 = true := by decide +kernel
-- modulus 2, g = 1 modulo 2, d = 1
example : ordOK 1 3 2 = false := by decide +kernel
-- modulus 2, g = 1 modulo 2, d = 2
example : ordOK 2 3 2 = true := by decide +kernel
-- out of domain: modulus 1, where 1 % 1 = 0
example : ordOK 1 5 1 = true := by decide +kernel
-- modulus 1, d = 2
example : ordOK 2 5 1 = false := by decide +kernel
-- out of domain: modulus 0, where 1 % 0 = 1
example : ordOK 0 1 0 = true := by decide +kernel
-- modulus 0
example : ordOK 5 2 0 = false := by decide +kernel

/-! ## Paired with engine.py: Lookups (`TwoExcEngine.findKey`, `lookupW`, `lookupP`) -/

example : findKey 3 ksA = some ⟨3, .sq, []⟩ := by decide +kernel
example : findKey 5 ksA = some ⟨5, (.fr true 2 false 1 false), [(13, 1)]⟩ := by decide +kernel
example : findKey 7 ksA = some ⟨7, .sq, [(3, 1), (5, 2)]⟩ := by decide +kernel
-- absent
example : findKey 11 ksA = none := by decide +kernel
-- absent, 0
example : findKey 0 ksA = none := by decide +kernel
-- empty list
example : findKey 3 ksNil = none := by decide +kernel
-- the prime twice: the first key
example : findKey 7 ksDup = some ⟨7, .sq, []⟩ := by decide +kernel
-- a key 0
example : findKey 0 ksZero = some ⟨0, .sq, []⟩ := by decide +kernel
-- the component twice: the first weight
example : lookupW 3 [(3, 1), (5, 2), (3, 4)] = 1 := by decide +kernel
example : lookupW 5 [(3, 1), (5, 2), (3, 4)] = 2 := by decide +kernel
-- absent
example : lookupW 7 [(3, 1), (5, 2), (3, 4)] = 0 := by decide +kernel
-- component 0
example : lookupW 0 [(0, 9)] = 9 := by decide +kernel
-- empty list
example : lookupW 3 [] = 0 := by decide +kernel
-- the pair twice: the first weight
example : lookupP 13 3 [(13, 3, 1), (13, 5, 2), (7, 3, 1), (13, 3, 5)] = 1 := by decide +kernel
example : lookupP 7 3 [(13, 3, 1), (13, 5, 2), (7, 3, 1), (13, 3, 5)] = 1 := by decide +kernel
-- the prime without the component
example : lookupP 7 5 [(13, 3, 1), (13, 5, 2), (7, 3, 1), (13, 3, 5)] = 0 := by decide +kernel
-- the component without the prime
example : lookupP 5 3 [(13, 3, 1), (13, 5, 2), (7, 3, 1), (13, 3, 5)] = 0 := by decide +kernel
-- empty list
example : lookupP 13 3 [] = 0 := by decide +kernel

/-! ## Paired with engine.py: The square filter (`TwoExcEngine.qrPass`, `qrTable`) -/

-- the moduli of the filter
example : qrTable.map Prod.fst = [33263, 7429, 5005, 1763, 2491, 3599, 4757] := by decide +kernel
example : qrPass 0 = true := by decide +kernel
example : qrPass 1 = true := by decide +kernel
-- a square
example : qrPass 1000000 = true := by decide +kernel
-- the least nonsquare that passes
example : qrPass 860574 = true := by decide +kernel
-- fails only modulo 33263
example : qrPass 15794 = false := by decide +kernel
-- fails only modulo 7429
example : qrPass 126494 = false := by decide +kernel
-- fails only modulo 5005
example : qrPass 50879 = false := by decide +kernel
-- fails only modulo 1763
example : qrPass 108339 = false := by decide +kernel
-- fails only modulo 2491
example : qrPass 758234 = false := by decide +kernel
-- fails only modulo 3599
example : qrPass 524195 = false := by decide +kernel
-- fails only modulo 4757
example : qrPass 182919 = false := by decide +kernel
-- a nonsquare that passes
example : qrPass ((2 ^ 50 + 3) ^ 2 + 92990138354449826827902565) = true := by decide +kernel
-- a large nonsquare that passes
example : qrPass ((2 ^ 500 + 1) ^ 2 + 92990138354449826827902565) = true := by decide +kernel
example : qrBits 860574 = [1, 1, 1, 1, 1, 1, 1] := by decide +kernel
example : qrBits 15794 = [0, 1, 1, 1, 1, 1, 1] := by decide +kernel
example : qrBits 126494 = [1, 0, 1, 1, 1, 1, 1] := by decide +kernel
example : qrBits 50879 = [1, 1, 0, 1, 1, 1, 1] := by decide +kernel
example : qrBits 108339 = [1, 1, 1, 0, 1, 1, 1] := by decide +kernel
example : qrBits 758234 = [1, 1, 1, 1, 0, 1, 1] := by decide +kernel
example : qrBits 524195 = [1, 1, 1, 1, 1, 0, 1] := by decide +kernel
example : qrBits 182919 = [1, 1, 1, 1, 1, 1, 0] := by decide +kernel

/-! ## Paired with engine.py: Square roots (`TwoExcEngine.newton`, `sqrtIfSq`) -/

-- no fuel
example : newton 0 7 5 = 5 := by decide +kernel
-- start 0: 7 / 0 = 0
example : newton 1 7 0 = 0 := by decide +kernel
-- start below the root: no step
example : newton 5 100 3 = 3 := by decide +kernel
-- start at the root
example : newton 5 100 10 = 10 := by decide +kernel
-- z = 0 from 2 ^ 51: fuel exactly enough
example : newton 52 0 (2 ^ 51) = 0 := by decide +kernel
-- one step short
example : newton 51 0 (2 ^ 51) = 1 := by decide +kernel
-- a square from 2 ^ 51: fuel exactly enough
example : newton 34 1000000000000 (2 ^ 51) = 1000000 := by decide +kernel
-- one step short
example : newton 33 1000000000000 (2 ^ 51) = 1000972 := by decide +kernel
-- a nonsquare from 2 ^ 51: fuel exactly enough
example : newton 50 99 (2 ^ 51) = 9 := by decide +kernel
-- one step short
example : newton 49 99 (2 ^ 51) = 10 := by decide +kernel
-- 2 ^ 102 from itself: fuel exactly enough
example : newton 56 (2 ^ 102) (2 ^ 102) = 2251799813685248 := by decide +kernel
-- one step short
example : newton 55 (2 ^ 102) (2 ^ 102) = 2251799813685305 := by decide +kernel
-- 2 ^ 784 from itself: the fuel of sqrtIfSq is enough
example : newton 400 (2 ^ 784) (2 ^ 784) = 2 ^ 392 := by decide +kernel
-- one step short
example : newton 399 (2 ^ 784) (2 ^ 784) = 2 ^ 392 + 13347530 := by decide +kernel
example : sqrtIfSq 0 = some (some 0) := by decide +kernel
example : sqrtIfSq 1 = some (some 1) := by decide +kernel
example : sqrtIfSq 99 = some none := by decide +kernel
example : sqrtIfSq 100 = some (some 10) := by decide +kernel
-- passes the filter, rejected by Newton
example : sqrtIfSq 860574 = some none := by decide +kernel
-- rejected by the filter
example : sqrtIfSq 15794 = some none := by decide +kernel
example : sqrtIfSq 1000000000000 = some (some 1000000) := by decide +kernel
-- below 2 ^ 102: Newton starts at 2 ^ 51
example : sqrtIfSq ((2 ^ 51 - 1) ^ 2 - 1) = some none := by decide +kernel
example : sqrtIfSq ((2 ^ 51 - 1) ^ 2) = some (some 2251799813685247) := by decide +kernel
example : sqrtIfSq ((2 ^ 51 - 1) ^ 2 + 1) = some none := by decide +kernel
-- passes the filter
example : sqrtIfSq ((2 ^ 51 - 1) ^ 2 + 92990138354449826827902565) = some none := by decide +kernel
example : sqrtIfSq (2 ^ 102 - 1) = some none := by decide +kernel
-- from 2 ^ 102 on Newton starts at z
example : sqrtIfSq (2 ^ 102) = some (some 2251799813685248) := by decide +kernel
example : sqrtIfSq (2 ^ 102 + 1) = some none := by decide +kernel
example : sqrtIfSq ((2 ^ 51 + 1) ^ 2 - 1) = some none := by decide +kernel
example : sqrtIfSq ((2 ^ 51 + 1) ^ 2) = some (some 2251799813685249) := by decide +kernel
example : sqrtIfSq ((2 ^ 51 + 1) ^ 2 + 1) = some none := by decide +kernel
-- passes the filter
example : sqrtIfSq ((2 ^ 51 + 1) ^ 2 + 92990138354449826827902565) = some none := by decide +kernel
example : sqrtIfSq ((2 ^ 50 + 3) ^ 2) = some (some 1125899906842627) := by decide +kernel
-- passes the filter
example : sqrtIfSq ((2 ^ 50 + 3) ^ 2 + 92990138354449826827902565) = some none := by decide +kernel
-- Newton settles in exactly 400 steps
example : sqrtIfSq (2 ^ 784) = some (some (2 ^ 392)) := by decide +kernel
-- Newton needs 401 steps: the outer none
example : sqrtIfSq (2 ^ 786) = none := by decide +kernel
-- a large square: the outer none
example : sqrtIfSq ((2 ^ 500 + 1) ^ 2) = none := by decide +kernel
-- a large nonsquare that passes the filter: the outer none
example : sqrtIfSq ((2 ^ 500 + 1) ^ 2 + 92990138354449826827902565) = none := by decide +kernel

end CheckerControls.Paired
