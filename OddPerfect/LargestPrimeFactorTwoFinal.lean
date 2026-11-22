import OddPerfect.LargestPrimeFactorTwoRows1
import OddPerfect.LargestPrimeFactorTwoRows2
import OddPerfect.LargestPrimeFactorTwoRows3
import OddPerfect.LargestPrimeFactorTwoRows4
import OddPerfect.LargestPrimeFactorTwoRows5
import OddPerfect.LargestPrimeFactorTwoRows6
import OddPerfect.LargestPrimeFactorTwoRows7
import OddPerfect.LargestPrimeFactorTwoRows8
import OddPerfect.LargestPrimeFactorTwoRows9

/-!
# The largest prime factor of an odd perfect number exceeds `100000`

The search `LPF.search` of `OddPerfect.LargestPrimeFactor` is run by the kernel for the bound
`100000` with the table read off the certificates of the modules
`LargestPrimeFactorTwoRows1` .. `LargestPrimeFactorTwoRows9`, and
`LPF2.exists_primeFactor_gt_of_cert` turns the accepted search into the theorem. Much larger
bounds are published (Hagis and Cohen `10 ^ 6`, Jenkins `10 ^ 7`, Goto and Ohno `10 ^ 8`);
they are not proved here.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace OddPerfect

namespace LPF2

/-- All row certificates for the bound `100000`. -/
def certs100000 : List (ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) := certs100000_1 ++ certs100000_2 ++ certs100000_3 ++ certs100000_4 ++ certs100000_5 ++ certs100000_6 ++ certs100000_7 ++ certs100000_8 ++ certs100000_9

/-- The search for the bound `100000` with the table of `certs100000` succeeds. -/
theorem search100000 : LPF.search 100000 primes100000 bigM100000 bigD100000
    (certs100000.map fun c => (c.1, c.2.1)) 1000 [] [] [] = true := by decide +kernel

end LPF2

/-- The largest prime factor of an odd perfect number exceeds `100000`. The search table and its
row certificates were found outside Lean and are checked by the kernel. Much larger bounds
are published (Goto and Ohno: `10 ^ 8`); they are not proved here. -/
theorem exists_primeFactor_gt_100000 {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, 100000 < p :=
  LPF2.exists_primeFactor_gt_of_cert LPF2.primesUpTo100000_eq LPF2.bigM100000_eq LPF2.bigD100000_eq
    (by decide) rfl LPF2.listL100000_ok
    (by simp only [LPF2.certs100000, List.all_append, LPF2.certs100000_1_ok, LPF2.certs100000_2_ok, LPF2.certs100000_3_ok, LPF2.certs100000_4_ok, LPF2.certs100000_5_ok, LPF2.certs100000_6_ok, LPF2.certs100000_7_ok, LPF2.certs100000_8_ok, LPF2.certs100000_9_ok,
      Bool.and_true]) LPF2.search100000 h

end OddPerfect

#print axioms OddPerfect.LPF2.search100000
#print axioms OddPerfect.exists_primeFactor_gt_100000
