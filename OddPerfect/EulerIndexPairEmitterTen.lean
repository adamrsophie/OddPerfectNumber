import OddPerfect.EulerIndexPairSixParity
import OddPerfect.HalfSigmaSix
import OddPerfect.EulerIndexPairEmitterSix

/-!
# Two prime Euler index: emitter exponent at least 10 in the branch `v = 0`

Restricted result; no published source was checked; novelty not verified.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, labeled `(t, u)` with `σ(t ^ e) = q u ^ v` and `σ(u ^ f) = t ^ j`
(`e = v_t(N)`, `f = v_u(N)`).

* `eulerIndex_pair_emitter_ten`: in the branch `v = 0`, `e ≥ 10`; in the branch `v = 1`,
  `u = e + 1 ≥ 7`. The branch `v = 0` with `e = 6` would make `σ(t ^ 6) + 1` twice a square
  (`eulerIndex_pair_six_half_square`), which no odd prime allows
  (`sigma_prime_pow_six_add_one_ne_two_mul_sq`); `e = 8` is impossible since `e + 1` is prime.
  The branch `v = 1` has `e ≥ 6` by `eulerIndex_pair_emitter_six`, whose labeling agrees
  with the one used here: a swapped labeling gives `q ∣ t ^ j`, so `q = t`, and then
  `t ∣ σ(t ^ e)`, which is false.

The case is not excluded: `v = 0` with `e ≥ 10` and `v = 1` with `e ≥ 6` remain. The odd
perfect number conjecture is open, and nothing here decides it.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N q m r s : ℕ}

/-- **Two prime index: emitter exponent at least 10 when `v = 0`, at least 6 when `v = 1`.**
Restricted result; no published source was checked; novelty not verified. This case is not
excluded here. -/
theorem eulerIndex_pair_emitter_ten (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ t.Prime ∧ t ≠ 2 ∧ ∃ v j,
      σ 1 (t ^ N.factorization t) = q * u ^ v ∧ 0 < j ∧ Odd j ∧
      σ 1 (u ^ N.factorization u) = t ^ j ∧ j < N.factorization t ∧
      (N.factorization t + 1).Prime ∧
      ((v = 0 ∧ σ 1 (t ^ N.factorization t) = q ∧ 10 ≤ N.factorization t) ∨
        (v = 1 ∧ u = N.factorization t + 1 ∧ 7 ≤ u ∧ t % u = 1 ∧ q % u = 1 ∧
          q + 1 = 2 * (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2)) := by
  obtain ⟨t, u, htu, hne, ht, ht2, v, j, hA, hj, hjo, hB, hje, hp, hcases⟩ :=
    eulerIndex_pair_ten_le_of_no_six h hq hN hqm hr hs hrs hJ
      (fun p hp hp2 z => sigma_prime_pow_six_add_one_ne_two_mul_sq hp hp2)
  obtain ⟨t', u', htu', -, v', j', hA', -, -, -, -, -, h6, -⟩ :=
    eulerIndex_pair_emitter_six h hq hN hqm hr hs hrs hJ
  have htt : t' = t := by
    have ht' : t' ∈ ({t, u} : Finset ℕ) := by rw [htu, ← htu']; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
    rcases ht' with h1 | h1
    · exact h1
    · exfalso
      rw [h1, hB] at hA'
      have hqt : q ∣ t := hq.dvd_of_dvd_pow (Dvd.intro _ hA'.symm)
      have hqt' := (Nat.prime_dvd_prime_iff_eq hq ht).mp hqt
      have hdvd : t ∣ σ 1 (t ^ N.factorization t) := by
        rw [hA, hqt']; exact Dvd.intro _ rfl
      exact (Nat.Prime.coprime_iff_not_dvd ht).mp (coprime_sigma_prime_pow ht _).symm hdvd
  rw [htt] at h6
  refine ⟨t, u, htu, hne, ht, ht2, v, j, hA, hj, hjo, hB, hje, hp, ?_⟩
  rcases hcases with hl | ⟨hv, hu, -, h1, h2, h3⟩
  · exact Or.inl hl
  · exact Or.inr ⟨hv, hu, by omega, h1, h2, h3⟩

end OddPerfect

#print axioms OddPerfect.eulerIndex_pair_emitter_ten
