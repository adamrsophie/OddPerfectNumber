
end FamInst

open FamInst in
/-- The common `65` family is impossible (known; Evans and Pearlman 2007). Let `N` be an odd
perfect number with special prime `q`. Then `65 ∣ v_p(N) + 1` cannot hold for every ordinary
prime `p`. Here `5 ∣ N`, `13 ∣ N` and `q ≡ 1 (mod 12)`. If `q = 13`, then `7 ∣ 13 + 1` divides
`N` and the seeds are `5, 13, 7` with the rows of `13` blocked; otherwise `13` is ordinary, the
seeds are `5, 13`, and every source node `≡ 1 (mod 12)` other than `13` is blocked in turn. In
both cases the target primes give an abundant divisor. -/
theorem not_common_sixty_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 65 ∣ N.factorization p + 1) : False := by
  have hexp5 : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 5 ∣ 65).trans (hexp p hp hpq)
  have hexp13 : ∀ p ∈ N.primeFactors, p ≠ q → 13 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 13 ∣ 65).trans (hexp p hp hpq)
  have h5N := (five_dvd_and_ne_special_of_common h hq hodd hexp5).1
  have h13N := dvd_of_dvd_succ h hq hodd (by norm_num) (by norm_num) hexp13
  have hq12 := special_mod_twelve_of_common_five h hq hodd hexp5
  have hcq' : (fun b : ℕ => b % 12 == 1) q = true := by simp [hq12]
  by_cases hq13 : q = 13
  · subst hq13
    have h7N : 7 ∣ N := (prime_dvd_of_dvd_succ_special h hq hodd (by norm_num) (by norm_num)
      (by norm_num : 7 ∣ 13 + 1)).1
    have hseed : ∀ t ∈ nodes65.take 3, t ∣ N := by
      intro t ht
      have : nodes65.take 3 = [5, 13, 7] := by decide +kernel
      rw [this] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact h5N
      · exact h13N
      · exact h7N
    exact false_of_reach h hexp (by norm_num) (by simp [cand65A]) hcq' nodes65_prime nodes65_ne2
      hseed (by decide +kernel) hrows65 hcand65A reach65A_none vals65_sel vals65_nodup PG65 ab65
  · have hseed : ∀ t ∈ nodes65.take 2, t ∣ N := by
      intro t ht
      have : nodes65.take 2 = [5, 13] := by decide +kernel
      rw [this] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact h5N
      · exact h13N
    exact false_of_reach h hexp (by norm_num) (by simp [cand65B, hq12, hq13]) hcq'
      nodes65_prime nodes65_ne2 hseed (by decide +kernel) hrows65 hcand65B reach65B_none
      vals65_sel vals65_nodup PG65 ab65

/-- The ordinary exponents of an odd perfect number cannot all equal one `E` with
`65 ∣ E + 1`. -/
theorem not_all_exponents_eq_of_sixty_five_dvd_succ {N q E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : 65 ∣ E + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = E) : False :=
  not_common_sixty_five h hq hodd fun p hp hpq => hexp p hp hpq ▸ hE

end OddPerfect
