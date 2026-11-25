import OddPerfect.EulerIndexPairOutside

/-!
# Two prime Euler index: twice each outside prime power fits in `q + 1`

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. `eulerIndex_pair_outside_prod_dvd` gives `2 ∏ p ^ v_p(N) ∣ q + 1` over the primes
`p ∣ N` outside `{q, r, s}`. Keeping the factor `2` for a single such `p` gives
`2 p ^ v_p(N) ≤ q + 1`; since `v_p(N) ≥ 2` and `p ≥ 3`, this yields `(p + 1) ^ 2 ≤ q`, which
sharpens `p ^ 2 ≤ q + 1` of `eulerIndex_pair_outside_sq_le`.

This is a restricted result (special exponent 1, Euler index supported on exactly two primes).
It does not exclude this case. Its novelty has not been verified.
-/

namespace OddPerfect

variable {N q m r s : ℕ}

/-- **Outside primes, with the factor two.** In the setting of
`eulerIndex_pair_outside_prod_dvd`, every prime `p ∣ N` outside `{q, r, s}` has
`2 p ^ v_p(N) ≤ q + 1` and `(p + 1) ^ 2 ≤ q`. This is a restricted result (special exponent 1,
index supported on exactly two primes); it does not exclude this case. Its novelty has not
been verified. -/
theorem eulerIndex_pair_outside_succ_sq_le (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∀ p ∈ N.primeFactors \ {q, r, s},
      2 * p ^ N.factorization p ≤ q + 1 ∧ (p + 1) ^ 2 ≤ q := by
  intro p hp
  have hD := eulerIndex_pair_outside_prod_dvd h hq hN hqm hr hs hrs hJ
  have h1 : 2 * p ^ N.factorization p ∣ q + 1 :=
    (Nat.mul_dvd_mul_left 2 (Finset.dvd_prod_of_mem _ hp)).trans hD
  have hle := Nat.le_of_dvd (by omega) h1
  refine ⟨hle, ?_⟩
  rw [Finset.mem_sdiff] at hp
  obtain ⟨hpN, hpO⟩ := hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpO
  have hpq := hpO.1
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have hp2 : p ≠ 2 := by
    rintro rfl; exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hpN)
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hpm : p ∣ m := by
    rcases (Nat.Prime.dvd_mul hpp).mp (hN ▸ Nat.dvd_of_mem_primeFactors hpN) with hd | hd
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp hq).mp hd) hpq
    · exact hpp.dvd_of_dvd_pow hd
  have hpos := hpp.factorization_pos_of_dvd hm hpm
  have hg : 2 ≤ N.factorization p := by
    rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
      hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq), zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    omega
  have hsq : p ^ 2 ≤ p ^ N.factorization p := Nat.pow_le_pow_right hpp.pos hg
  have h3 : 3 ≤ p := by have := hpp.two_le; omega
  nlinarith

end OddPerfect

#print axioms OddPerfect.eulerIndex_pair_outside_succ_sq_le
