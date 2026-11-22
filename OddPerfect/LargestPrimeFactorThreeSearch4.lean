import OddPerfect.LargestPrimeFactorThreeRows1
import OddPerfect.LargestPrimeFactorThreeRows2
import OddPerfect.LargestPrimeFactorThreeRows3

/-!
# Part 4 of 4 of the search for the largest prime factor bound `200000`

Subtrees of the search `LPF.search` for the bound `200000`, each run whole by the kernel; the module
`LargestPrimeFactorThreeFinal` joins them with the steps above them. The cut was chosen outside
Lean (`scripts/LargestPrimeFactor/gen6.py`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace OddPerfect

namespace LPF3

/-- A subtree of the search for the bound `200000` (1372 nodes). -/
theorem sub200000_6 : LPF.search 200000 primes200000 bigM200000 bigD200000
    ((certs200000_1 ++ certs200000_2 ++ certs200000_3).map fun c => (c.1, c.2.1)) 998 [(3, 6)] [1093] [] = true := by
  decide +kernel

/-- A subtree of the search for the bound `200000` (1226 nodes). -/
theorem sub200000_7 : LPF.search 200000 primes200000 bigM200000 bigD200000
    ((certs200000_1 ++ certs200000_2 ++ certs200000_3).map fun c => (c.1, c.2.1)) 999 [] [] [3] = true := by
  decide +kernel

/-- A subtree of the search for the bound `200000` (1117 nodes). -/
theorem sub200000_8 : LPF.search 200000 primes200000 bigM200000 bigD200000
    ((certs200000_1 ++ certs200000_2 ++ certs200000_3).map fun c => (c.1, c.2.1)) 998 [(3, 8)] [13, 757] [] = true := by
  decide +kernel

/-- A subtree of the search for the bound `200000` (1117 nodes). -/
theorem sub200000_9 : LPF.search 200000 primes200000 bigM200000 bigD200000
    ((certs200000_1 ++ certs200000_2 ++ certs200000_3).map fun c => (c.1, c.2.1)) 998 [(3, 26)] [13, 109, 433, 757, 8209] [] = true := by
  decide +kernel

/-- A subtree of the search for the bound `200000` (721 nodes). -/
theorem sub200000_10 : LPF.search 200000 primes200000 bigM200000 bigD200000
    ((certs200000_1 ++ certs200000_2 ++ certs200000_3).map fun c => (c.1, c.2.1)) 998 [(3, 4)] [11] [] = true := by
  decide +kernel

end LPF3

end OddPerfect

#print axioms OddPerfect.LPF3.sub200000_6
#print axioms OddPerfect.LPF3.sub200000_7
#print axioms OddPerfect.LPF3.sub200000_8
#print axioms OddPerfect.LPF3.sub200000_9
#print axioms OddPerfect.LPF3.sub200000_10
