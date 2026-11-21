
end FamInst

open FamInst in
/-- The common `55` family is impossible. Let `N` be an odd perfect number with special prime
`q`. Then `55 ∣ v_p(N) + 1` cannot hold for every ordinary prime `p`. Here `5 ∣ N`, `11 ∣ N` and
`q ≡ 1 (mod 12)`; the forcing table from the seeds `5, 11` reaches all target primes whichever
source node `≡ 1 (mod 12)` is special, and they give an abundant divisor. We did not locate a
published proof of this case. -/
theorem not_common_fifty_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 55 ∣ N.factorization p + 1) : False := by
  have hexp5 : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 5 ∣ 55).trans (hexp p hp hpq)
  have hexp11 : ∀ p ∈ N.primeFactors, p ≠ q → 11 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 11 ∣ 55).trans (hexp p hp hpq)
  have h5N := (five_dvd_and_ne_special_of_common h hq hodd hexp5).1
  have h11N := dvd_of_dvd_succ h hq hodd (by norm_num) (by norm_num) hexp11
  have hq12 := special_mod_twelve_of_common_five h hq hodd hexp5
  have hcq : cand55 q = true := by simp [cand55, hq12]
  have hcq' : (fun b : ℕ => b % 12 == 1) q = true := by simp [hq12]
  have hseed : ∀ t ∈ nodes55.take 2, t ∣ N := by
    intro t ht
    have : nodes55.take 2 = [5, 11] := by decide +kernel
    rw [this] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h5N
    · exact h11N
  exact false_of_reach h hexp (by norm_num) hcq hcq' nodes55_prime nodes55_ne2 hseed
    (by decide +kernel) hrows55 hcand55 reach55_none vals55_sel vals55_nodup PG55 ab55

/-- The ordinary exponents of an odd perfect number cannot all equal one `E` with
`55 ∣ E + 1`. -/
theorem not_all_exponents_eq_of_fifty_five_dvd_succ {N q E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : 55 ∣ E + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = E) : False :=
  not_common_fifty_five h hq hodd fun p hp hpq => hexp p hp hpq ▸ hE

end OddPerfect
