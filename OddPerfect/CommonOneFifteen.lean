import OddPerfect.CommonOneFifteenPrime

/-!
# Common exponent families: the common `115` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves that the common `115`
family is impossible, with the table of `OddPerfect.CommonOneFifteenData`, the primality in
`OddPerfect.CommonOneFifteenPrime`, and the reach and
abundance checkers of `OddPerfect.CommonFiveSeven`. We did not locate a published proof of
this case.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The blocked candidates. -/
def cand115 (b : ℕ) : Bool := b % 12 == 1

/-- Reach checks for the blocked source nodes, part 0. -/
theorem reach115_0 :
    src115_0.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 1. -/
theorem reach115_1 :
    src115_1.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 2. -/
theorem reach115_2 :
    src115_2.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 3. -/
theorem reach115_3 :
    src115_3.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 4. -/
theorem reach115_4 :
    src115_4.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 5. -/
theorem reach115_5 :
    src115_5.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 6. -/
theorem reach115_6 :
    src115_6.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 7. -/
theorem reach115_7 :
    src115_7.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 8. -/
theorem reach115_8 :
    src115_8.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 9. -/
theorem reach115_9 :
    src115_9.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 10. -/
theorem reach115_10 :
    src115_10.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 11. -/
theorem reach115_11 :
    src115_11.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 12. -/
theorem reach115_12 :
    src115_12.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 13. -/
theorem reach115_13 :
    src115_13.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 14. -/
theorem reach115_14 :
    src115_14.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 15. -/
theorem reach115_15 :
    src115_15.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 16. -/
theorem reach115_16 :
    src115_16.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 17. -/
theorem reach115_17 :
    src115_17.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 18. -/
theorem reach115_18 :
    src115_18.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 19. -/
theorem reach115_19 :
    src115_19.all (fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b) = true := by
  decide +kernel

/-- Reach check with no source blocked. -/
theorem reach115_none : reach nodes115 rows115 2 tm115 3 0 = true := by decide +kernel

/-- Every blocked source node passes the reach check. -/
theorem hcand115 : ∀ b ∈ nodes115.take rows115.length, cand115 b = true →
    reach nodes115 rows115 2 tm115 3 b = true := by
  intro b hb hcb
  have := all_of_parts (f := fun b => !cand115 b || reach nodes115 rows115 2 tm115 3 b)
    _ src115_eq (by
    exact List.forall_mem_cons.mpr ⟨reach115_0, List.forall_mem_cons.mpr ⟨reach115_1,
      List.forall_mem_cons.mpr ⟨reach115_2, List.forall_mem_cons.mpr ⟨reach115_3,
      List.forall_mem_cons.mpr ⟨reach115_4, List.forall_mem_cons.mpr ⟨reach115_5,
      List.forall_mem_cons.mpr ⟨reach115_6, List.forall_mem_cons.mpr ⟨reach115_7,
      List.forall_mem_cons.mpr ⟨reach115_8, List.forall_mem_cons.mpr ⟨reach115_9,
      List.forall_mem_cons.mpr ⟨reach115_10, List.forall_mem_cons.mpr ⟨reach115_11,
      List.forall_mem_cons.mpr ⟨reach115_12, List.forall_mem_cons.mpr ⟨reach115_13,
      List.forall_mem_cons.mpr ⟨reach115_14, List.forall_mem_cons.mpr ⟨reach115_15,
      List.forall_mem_cons.mpr ⟨reach115_16, List.forall_mem_cons.mpr ⟨reach115_17,
      List.forall_mem_cons.mpr ⟨reach115_18, List.forall_mem_cons.mpr ⟨reach115_19, fun _ h =>
      absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) b hb
  simpa [hcb] using this

/-- Abundance: the target primes with fourth powers, and with any one of them `≡ 1 (mod 12)` to
the first power. -/
theorem ab115 : abOK2 vals115 (fun b : ℕ => b % 12 == 1) P115 G115 = true := by decide +kernel

end FamInst

open FamInst in
/-- The common `115` family is impossible. Let `N` be an odd perfect number with special prime
`q`. Then `115 ∣ v_p(N) + 1` cannot hold for every ordinary prime `p`. Here `5 ∣ N`,
`23 ∣ N` and `q ≡ 1 (mod 12)`; the forcing table from the seeds `5, 23` reaches all target primes whichever
source node `≡ 1 (mod 12)` is special, and they give an abundant divisor. We did not locate a
published proof of this case. -/
theorem not_common_one_fifteen {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 115 ∣ N.factorization p + 1) : False := by
  have hexp5 : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 5 ∣ 115).trans (hexp p hp hpq)
  have hexp23 : ∀ p ∈ N.primeFactors, p ≠ q → 23 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 23 ∣ 115).trans (hexp p hp hpq)
  have h5N := (five_dvd_and_ne_special_of_common h hq hodd hexp5).1
  have h23N := dvd_of_dvd_succ h hq hodd (by norm_num) (by norm_num) hexp23
  have hq12 := special_mod_twelve_of_common_five h hq hodd hexp5
  have hcq : cand115 q = true := by simp [cand115, hq12]
  have hcq' : (fun b : ℕ => b % 12 == 1) q = true := by simp [hq12]
  have hseed : ∀ t ∈ nodes115.take 2, t ∣ N := by
    intro t ht
    have : nodes115.take 2 = [5, 23] := by decide +kernel
    rw [this] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h5N
    · exact h23N
  exact false_of_reach h hexp (by norm_num) hcq hcq' nodes115_prime nodes115_ne2 hseed
    (by decide +kernel) hrows115 hcand115 reach115_none vals115_sel vals115_nodup PG115 ab115

/-- The ordinary exponents of an odd perfect number cannot all equal one `E` with
`115 ∣ E + 1`. -/
theorem not_all_exponents_eq_of_one_fifteen_dvd_succ {N q E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : 115 ∣ E + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = E) : False :=
  not_common_one_fifteen h hq hodd fun p hp hpq => hexp p hp hpq ▸ hE

end OddPerfect

#print axioms OddPerfect.FamInst.reach115_0
#print axioms OddPerfect.FamInst.reach115_1
#print axioms OddPerfect.FamInst.reach115_2
#print axioms OddPerfect.FamInst.reach115_3
#print axioms OddPerfect.FamInst.reach115_4
#print axioms OddPerfect.FamInst.reach115_5
#print axioms OddPerfect.FamInst.reach115_6
#print axioms OddPerfect.FamInst.reach115_7
#print axioms OddPerfect.FamInst.reach115_8
#print axioms OddPerfect.FamInst.reach115_9
#print axioms OddPerfect.FamInst.reach115_10
#print axioms OddPerfect.FamInst.reach115_11
#print axioms OddPerfect.FamInst.reach115_12
#print axioms OddPerfect.FamInst.reach115_13
#print axioms OddPerfect.FamInst.reach115_14
#print axioms OddPerfect.FamInst.reach115_15
#print axioms OddPerfect.FamInst.reach115_16
#print axioms OddPerfect.FamInst.reach115_17
#print axioms OddPerfect.FamInst.reach115_18
#print axioms OddPerfect.FamInst.reach115_19
#print axioms OddPerfect.FamInst.reach115_none
#print axioms OddPerfect.FamInst.hcand115
#print axioms OddPerfect.FamInst.ab115
#print axioms OddPerfect.not_common_one_fifteen
#print axioms OddPerfect.not_all_exponents_eq_of_one_fifteen_dvd_succ
