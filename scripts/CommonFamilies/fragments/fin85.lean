
end FamInst

open FamInst in
/-- The common `85` family is impossible. Let `N` be an odd perfect number with special prime
`q`. Then `85 ∣ v_p(N) + 1` cannot hold for every ordinary prime `p`. Here `5 ∣ N`, `17 ∣ N` and
`q ≡ 1 (mod 12)`; the forcing table from the seeds `5, 17` reaches all target primes whichever
source node `≡ 1 (mod 12)` is special, and they give an abundant divisor. We did not locate a
published proof of this case. -/
theorem not_common_eighty_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 85 ∣ N.factorization p + 1) : False := by
  have hexp5 : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 5 ∣ 85).trans (hexp p hp hpq)
  have hexp17 : ∀ p ∈ N.primeFactors, p ≠ q → 17 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 17 ∣ 85).trans (hexp p hp hpq)
  have h5N := (five_dvd_and_ne_special_of_common h hq hodd hexp5).1
  have h17N := dvd_of_dvd_succ h hq hodd (by norm_num) (by norm_num) hexp17
  have hq12 := special_mod_twelve_of_common_five h hq hodd hexp5
  have hcq : cand85 q = true := by simp [cand85, hq12]
  have hcq' : (fun b : ℕ => b % 12 == 1) q = true := by simp [hq12]
  have hseed : ∀ t ∈ nodes85.take 2, t ∣ N := by
    intro t ht
    have : nodes85.take 2 = [5, 17] := by decide +kernel
    rw [this] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h5N
    · exact h17N
  exact false_of_reach h hexp (by norm_num) hcq hcq' nodes85_prime nodes85_ne2 hseed
    (by decide +kernel) hrows85 hcand85 reach85_none vals85_sel vals85_nodup PG85 ab85

/-- The ordinary exponents of an odd perfect number cannot all equal one `E` with
`85 ∣ E + 1`. -/
theorem not_all_exponents_eq_of_eighty_five_dvd_succ {N q E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : 85 ∣ E + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = E) : False :=
  not_common_eighty_five h hq hodd fun p hp hpq => hexp p hp hpq ▸ hE

end OddPerfect
