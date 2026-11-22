import OddPerfect.SecondLargestPrimeFastData1
import OddPerfect.SecondLargestPrimeFastData2
import OddPerfect.SecondLargestPrimeFastData3
import OddPerfect.SecondLargestPrimeFastData4
import OddPerfect.SecondLargestPrimeFastData5
import OddPerfect.SecondLargestPrimeFastData6
import OddPerfect.SecondLargestPrimeFastData7
import OddPerfect.SecondLargestPrimeFastData8
import OddPerfect.SecondLargestPrimeFastData9

/-!
# Two prime factors above `72`

A formalization of a known type of result: lower bounds for the second largest prime factor
of an odd perfect number. Iannucci proved such bounds with far larger constants (the second
largest prime factor exceeds `10 ^ 4`); those published bounds are not proved here. We show that
an odd perfect number has two distinct prime factors above `72`, with the search engine of
`OddPerfect.SecondLargestPrime`, started from the lower bound `10001` for the large prime given
by `exists_primeFactor_gt`. The steps of the search were found outside Lean and are checked
again by the kernel in the modules `SecondLargestPrimeFastData1` to
`SecondLargestPrimeFastData9`, with the fast step of `OddPerfect.SecondLargestPrimeFast`.
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
  FastData1.cert_first (FastData2.cert_first (FastData3.cert_first (FastData4.cert_first (FastData5.cert_first (FastData6.cert_first (FastData7.cert_first (FastData8.cert_first (FastData9.cert_first (cert_nil 72)))))))))

end SLP

/-- An odd perfect number has two distinct prime factors above `72`. -/
theorem exists_two_primeFactors_gt_72 {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧ 72 < p ∧ 72 < r :=
  SLP.exists_two_of_cert_from SLP.st72_eq (by norm_num) SLP.cert72 h

/-- An odd perfect number has two distinct prime factors above `58`. -/
theorem exists_two_primeFactors_gt {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧ 58 < p ∧ 58 < r := by
  obtain ⟨p, hp, r, hr, hpr, h1, h2⟩ := exists_two_primeFactors_gt_72 h
  exact ⟨p, hp, r, hr, hpr, by omega, by omega⟩

end OddPerfect

#print axioms OddPerfect.SLP.exists_two_of_cert_from
#print axioms OddPerfect.exists_two_primeFactors_gt_72
#print axioms OddPerfect.exists_two_primeFactors_gt
