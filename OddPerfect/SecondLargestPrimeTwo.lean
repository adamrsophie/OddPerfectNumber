import OddPerfect.SecondLargestPrimeData1
import OddPerfect.SecondLargestPrimeData2
import OddPerfect.SecondLargestPrimeData3
import OddPerfect.SecondLargestPrimeData4
import OddPerfect.SecondLargestPrimeData5
import OddPerfect.SecondLargestPrimeData6
import OddPerfect.SecondLargestPrimeData7
import OddPerfect.SecondLargestPrimeData8
import OddPerfect.SecondLargestPrimeData9

/-!
# Two prime factors above `72`

A formalization of a known type of result: lower bounds for the second largest prime factor
of an odd perfect number (Iannucci proved such bounds with far larger constants). We show that
an odd perfect number has two distinct prime factors above `72`, with the search engine of
`OddPerfect.SecondLargestPrime`, started from the lower bound `10001` for the large prime given
by `exists_primeFactor_gt`. The kernel checked steps of the search are in the modules
`SecondLargestPrimeData1` to `SecondLargestPrimeData9`.
-/

namespace OddPerfect

namespace SLP

/-- A certified initial stack, with lower bound `10001` for the large prime, gives two distinct
prime factors above `B`. The initial entries `st` are given explicitly and checked. -/
theorem exists_two_of_cert_from {B : ℕ} {st : List Ent}
    (hst : (primesUpTo B).map (fun q => (q, 0, 0)) = st) (hB : B ≤ 10000)
    (hc : Cert B [(st, 0, 10001, 0, 0, 0, false)]) {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧ B < p ∧ B < r := by
  subst hst
  obtain ⟨P0, hP0, hgt⟩ := exists_primeFactor_gt h
  by_contra hne
  have c : Ctx N B P0 :=
    ⟨h, Nat.prime_of_mem_primeFactors hP0, Nat.dvd_of_mem_primeFactors hP0, by omega,
      fun r hr hrP => le_of_not_gt fun hlt => hne ⟨P0, hP0, r, hr, Ne.symm hrP, by omega, hlt⟩⟩
  refine hc N P0 c _ (List.mem_singleton_self _) ⟨by rw [List.map_map]; exact List.map_id _,
    ?_, Or.inl rfl, show 10001 ≤ P0 by omega, Or.inl rfl, Or.inl rfl⟩
  intro e he
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp he
  exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩

private def st72 : List Ent :=
  [(3, 0, 0), (5, 0, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0), (59, 0, 0), (61, 0, 0), (67, 0, 0), (71, 0, 0)]

private theorem st72_eq : (primesUpTo 72).map (fun q => (q, 0, 0)) = st72 := by decide +kernel

private theorem cert72 : Cert 72 [(st72, 0, 10001, 0, 0, 0, false)] :=
  Data1.cert_first (Data2.cert_first (Data3.cert_first (Data4.cert_first (Data5.cert_first (Data6.cert_first (Data7.cert_first (Data8.cert_first (Data9.cert_first (cert_nil 72)))))))))

end SLP

/-- An odd perfect number has two distinct prime factors above `72`. -/
theorem exists_two_primeFactors_gt_72 {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧ 72 < p ∧ 72 < r :=
  SLP.exists_two_of_cert_from SLP.st72_eq (by norm_num) SLP.cert72 h

end OddPerfect

#print axioms OddPerfect.SLP.exists_two_of_cert_from
#print axioms OddPerfect.exists_two_primeFactors_gt_72
