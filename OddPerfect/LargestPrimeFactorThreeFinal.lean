import OddPerfect.LargestPrimeFactorThreeSearch1
import OddPerfect.LargestPrimeFactorThreeSearch2
import OddPerfect.LargestPrimeFactorThreeSearch3
import OddPerfect.LargestPrimeFactorThreeSearch4

/-!
# The largest prime factor of an odd perfect number exceeds `200000`

The search `LPF.search` of `OddPerfect.LargestPrimeFactor` for the bound `200000`, with the table
read off the certificates of the modules `LargestPrimeFactorThreeRows1` ..
`LargestPrimeFactorThreeRows3`, is assembled here from its top steps (`LPF3.search_nil`,
`LPF3.search_cons_old`, `LPF3.search_cons_all`) and the subtrees run by the kernel in the modules
`LargestPrimeFactorThreeSearch1` .. `LargestPrimeFactorThreeSearch4`.
`LPF3.exists_primeFactor_gt_of_cert3` turns the accepted search into the theorem. The search
table, the certificates and the cut were found outside Lean and are checked by the kernel.
Much larger bounds are published (Hagis and Cohen `10 ^ 6`, Jenkins `10 ^ 7`, Goto and Ohno `10 ^ 8`);
they are not proved here.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace OddPerfect

namespace LPF3

/-- All row certificates for the bound `200000`. -/
def certs200000 : List (ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) := certs200000_1 ++ certs200000_2 ++ certs200000_3

private theorem node200000_1 : LPF.search 200000 primes200000 bigM200000 bigD200000
    (certs200000.map fun c => (c.1, c.2.1)) 999 [] [3] [] = true :=
  search_cons_all (es := [2, 4, 6, 8, 10, 14, 16, 26, 48]) (by decide +kernel) (by decide +kernel)
    fun e he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (by rw [show LPF.newPrimes primes200000 (LPF.gs 3 2) ++ [] = [13] by decide +kernel]; exact sub200000_3)
    · exact Or.inr (by rw [show LPF.newPrimes primes200000 (LPF.gs 3 4) ++ [] = [11] by decide +kernel]; exact sub200000_10)
    · exact Or.inr (by rw [show LPF.newPrimes primes200000 (LPF.gs 3 6) ++ [] = [1093] by decide +kernel]; exact sub200000_6)
    · exact Or.inr (by rw [show LPF.newPrimes primes200000 (LPF.gs 3 8) ++ [] = [13, 757] by decide +kernel]; exact sub200000_8)
    · exact Or.inr (by rw [show LPF.newPrimes primes200000 (LPF.gs 3 10) ++ [] = [23, 3851] by decide +kernel]; exact sub200000_4)
    · exact Or.inr (by rw [show LPF.newPrimes primes200000 (LPF.gs 3 14) ++ [] = [11, 13, 4561] by decide +kernel]; exact sub200000_5)
    · exact Or.inr (by rw [show LPF.newPrimes primes200000 (LPF.gs 3 16) ++ [] = [1871, 34511] by decide +kernel]; exact sub200000_2)
    · exact Or.inr (by rw [show LPF.newPrimes primes200000 (LPF.gs 3 26) ++ [] = [13, 109, 433, 757, 8209] by decide +kernel]; exact sub200000_9)
    · exact Or.inr (by rw [show LPF.newPrimes primes200000 (LPF.gs 3 48) ++ [] = [491, 1093, 4019, 8233, 51157, 131713] by decide +kernel]; exact sub200000_1)

/-- The search for the bound `200000` with the table of `certs200000` succeeds. -/
theorem search200000 : LPF.search 200000 primes200000 bigM200000 bigD200000
    (certs200000.map fun c => (c.1, c.2.1)) 1000 [] [] [] = true :=
  search_nil (by decide +kernel) node200000_1 sub200000_7

end LPF3

/-- The largest prime factor of an odd perfect number exceeds `200000`. The search table and its
row certificates were found outside Lean and are checked by the kernel. Much larger bounds are published (Hagis and Cohen `10 ^ 6`, Jenkins `10 ^ 7`, Goto and Ohno `10 ^ 8`);
they are not proved here. -/
theorem exists_primeFactor_gt_200000 {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, 200000 < p :=
  LPF3.exists_primeFactor_gt_of_cert3 LPF3.primesUpTo200000_eq LPF3.bigM200000_eq LPF3.bigD200000_eq
    (by decide) (K := 447) (by decide) (by decide) LPF3.bigQ200000_eq LPF3.listDR200000_ok rfl
    LPF3.listL200000_ok
    (by simp only [LPF3.certs200000, List.all_append, LPF3.certs200000_1_ok, LPF3.certs200000_2_ok, LPF3.certs200000_3_ok, Bool.and_true]) LPF3.search200000 h

end OddPerfect

#print axioms OddPerfect.LPF3.search200000
#print axioms OddPerfect.exists_primeFactor_gt_200000
