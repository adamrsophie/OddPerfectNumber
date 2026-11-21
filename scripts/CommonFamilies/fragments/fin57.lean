
end FamInst

open FamInst in
/-- In the common `5` family, `7 ∤ N` (known; Evans and Pearlman 2007). Let `N` be an odd
perfect number with special prime `q` and `5 ∣ v_p(N) + 1` for every ordinary prime `p`. Then
`5 ∣ N` and `q ≡ 1 (mod 12)`; if `7 ∣ N`, the forcing table from the seeds `5, 7` reaches all
target primes whichever source node `≡ 1 (mod 12)` is special, and they give an abundant
divisor. -/
theorem not_seven_dvd_of_common_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1) : ¬ 7 ∣ N := by
  intro h7N
  have h5N := (five_dvd_and_ne_special_of_common h hq hodd hexp).1
  have hq12 := special_mod_twelve_of_common_five h hq hodd hexp
  have hcq : cand57 q = true := by simp [cand57, hq12]
  have hcq' : (fun b : ℕ => b % 12 == 1) q = true := by simp [hq12]
  have hseed : ∀ t ∈ nodes57.take 2, t ∣ N := by
    intro t ht
    have : nodes57.take 2 = [5, 7] := by decide +kernel
    rw [this] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h5N
    · exact h7N
  exact false_of_reach h hexp le_rfl hcq hcq' nodes57_prime nodes57_ne2 hseed
    (by decide +kernel) hrows57 hcand57 reach57_none vals57_sel vals57_nodup PG57 ab57

end OddPerfect
