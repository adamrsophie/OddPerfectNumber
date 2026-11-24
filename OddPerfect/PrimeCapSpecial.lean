import OddPerfect.PrimeCapFamily

/-!
# The special exponent when the special prime is the largest prime factor

Restricted family results; no novelty is claimed, and whether they are in the literature was
not verified.

Let `N` be an odd perfect number with special prime `q`, and assume that `q` is the largest
prime factor of `N` and that every other prime factor has exponent `2` or `4`. Then the special
exponent `a = e_q` is `1` or `5` (`special_exponent_eq_one_or_five`). The ledger at `q` reads
`a = Σ_p v_q(σ(p ^ e_p))`. The row of `q` is prime to `q`; the rows of exponent `2` give at most
`2` and the rows of exponent `4` at most `6` (`primeSenderCap`, the senders are distinct primes
below `q`). So `a ≤ 8`, and `a ≡ 1 (mod 4)`.

Under the extra hypothesis `¬ 3 ∣ N`, kept explicit, the exponent is `1`
(`special_exponent_eq_one_of_not_three_dvd`): for `q` prime to `3`,
`3 ∣ 1 + q + ⋯ + q ^ 5`, so `a = 5` would put weight on the prime `3`.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Let `N` be an odd perfect number with special prime `q` (odd exponent), where `q` is the
largest prime factor and every other prime factor has exponent `2` or `4`. Then
`e_q = 1` or `e_q = 5`. Restricted family result. -/
theorem special_exponent_eq_one_or_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hmax : ∀ p ∈ N.primeFactors, p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q = 1 ∨ N.factorization q = 5 := by
  have hqm : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨k, hk⟩ := hodd; omega)
  have hbig : 200000 < q := by
    obtain ⟨p, hp, hlt⟩ := exists_primeFactor_gt_200000 h
    exact lt_of_lt_of_le hlt (hmax p hp)
  have hb := factorization_le_sum_of_cap h hqm hmax {2, 4} (fun e => primeSenderCap (e + 1))
    (by
      intro e he U hU
      have hnd : ¬ q ∣ e + 1 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      have h3 : 3 ≤ e + 1 ∧ e + 1 ≤ 11 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        omega
      exact sum_factorization_geom_sum_le_primeSenderCap hq hnd h3.1 h3.2 U hU)
    (fun p hp hpq => Or.inr (by simpa using hexp p hp hpq))
  have hc : ∑ e ∈ ({2, 4} : Finset ℕ), primeSenderCap (e + 1) = 8 := by decide
  have h4 := (special_mod_four h hq hodd).2
  omega

/-- Let `N` be an odd perfect number with special prime `q` (odd exponent), where `q` is the
largest prime factor and every other prime factor has exponent `2` or `4`. If moreover
`¬ 3 ∣ N` (an explicit hypothesis), then `e_q = 1`. Restricted family result. -/
theorem special_exponent_eq_one_of_not_three_dvd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hmax : ∀ p ∈ N.primeFactors, p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) :
    N.factorization q = 1 := by
  rcases special_exponent_eq_one_or_five h hq hodd hmax hexp with h1 | h5
  · exact h1
  exfalso
  have hqm : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by rw [h5]; norm_num)
  have hq3 : ¬ 3 ∣ q := fun hd => h3 (hd.trans (Nat.dvd_of_mem_primeFactors hqm))
  have hsum := sigmaWeight_sum_eq h.2 Nat.prime_three (by norm_num)
  rw [Nat.factorization_eq_zero_of_not_dvd h3] at hsum
  have hw := (Finset.sum_eq_zero_iff.mp hsum) q hqm
  unfold sigmaWeight at hw
  rw [h5, sigma_one_apply_prime_pow hq] at hw
  have key : ∀ x : ZMod 3, x ≠ 0 → ∑ i ∈ Finset.range (5 + 1), x ^ i = 0 := by decide
  have hx : (q : ZMod 3) ≠ 0 := fun h0 => hq3 ((ZMod.natCast_eq_zero_iff q 3).mp h0)
  have hdvd : 3 ∣ ∑ i ∈ Finset.range (5 + 1), q ^ i := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact key _ hx
  have hne : ∑ i ∈ Finset.range (5 + 1), q ^ i ≠ 0 := by
    rw [Finset.sum_range_succ']
    simp
  have := Nat.Prime.factorization_pos_of_dvd Nat.prime_three hne hdvd
  omega

end OddPerfect

#print axioms OddPerfect.special_exponent_eq_one_or_five
#print axioms OddPerfect.special_exponent_eq_one_of_not_three_dvd
