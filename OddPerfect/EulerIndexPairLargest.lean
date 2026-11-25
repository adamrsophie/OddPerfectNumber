import OddPerfect.EulerIndexPairPrimeLength
import OddPerfect.EulerIndexSupport
import OddPerfect.LedgerPrime

/-!
# Two prime Euler index: the special prime is the largest prime

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. `eulerIndex_pair_prime_length` labels them `(t, u)` with `σ(t ^ e) = q u ^ v`,
`σ(u ^ f) = t ^ j`, `0 < j < e` (`e = v_t(N)`, `f = v_u(N)`), and either `σ(t ^ e) = q`, or
`v = 1`, `u = e + 1` and `t ≡ 1 (mod u)`.

* `eulerIndex_pair_special_largest`: every prime factor of `N` is at most `q`. If `v = 0`,
  then `t < σ(t ^ e) = q` and `u < σ(u ^ f) = t ^ j < t ^ e < q`. If `v = 1`, then `u ≥ 3`,
  `t ≥ u + 1` and `t u < t ^ 2 ≤ t ^ e < σ(t ^ e) = q u`, so `u < t < q`. The other primes lie
  below `q` by the landed `eulerIndex_pair_outside_sq_le`.
* `three_le_card_primeFactors_eulerIndex_of_special_lt`: for special exponent 1, a prime factor
  of `N` above `q` forces at least three prime factors of the Euler index (at least two by the
  landed `two_le_card_primeFactors_eulerIndex_of_exponent_one`).

These are restricted results (special exponent 1). The first does not exclude the case of an
index with two prime factors. The second is a lower bound only for odd perfect numbers with
special exponent 1 and a prime factor above the special prime; whether the special prime can
be the largest prime factor is open, so the bound is not claimed for every odd perfect number.
Their novelty has not been verified.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairLargest

/-- `p ^ e < σ(p ^ e)` for `e ≠ 0`. -/
private theorem eipl_pow_lt_sigma {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    p ^ e < σ 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  have : p ^ 0 ≤ ∑ i ∈ Finset.range e, p ^ i :=
    Finset.single_le_sum (f := fun i => p ^ i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.pos_of_ne_zero he))
  simp only [pow_zero] at this
  omega

end EulerIndexPairLargest

open EulerIndexPairLargest

variable {N q m r s : ℕ}

/-- **Two prime index: the special prime is the largest prime.** Let `N = q m ^ 2` be an odd
perfect number with special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index
`J = σ(m ^ 2) / q` has exactly the two prime factors `r ≠ s`. Then every prime factor of `N`
is at most `q`. This is a restricted result (special exponent 1, index supported on exactly
two primes); it does not exclude this case. Its novelty has not been verified. -/
theorem eulerIndex_pair_special_largest (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) : ∀ p ∈ N.primeFactors, p ≤ q := by
  intro p hp
  by_cases hpq : p = q
  · exact hpq.le
  by_cases hprs : p = r ∨ p = s
  swap
  · have hout : p ∈ N.primeFactors \ {q, r, s} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact (eulerIndex_pair_outside_sq_le h hq hN hqm hr hs hrs hJ p hout).2.le
  obtain ⟨t, u, htu, -, v, j, hA, hj, -, hB, hje, -, hcase⟩ :=
    eulerIndex_pair_prime_length h hq hN hqm hr hs hrs hJ
  have hptu : p = t ∨ p = u := by
    have : p ∈ ({t, u} : Finset ℕ) := by
      rw [htu]; simp only [Finset.mem_insert, Finset.mem_singleton]; exact hprs
    simpa using this
  have ht : t.Prime := by
    have : t ∈ ({r, s} : Finset ℕ) := by rw [← htu]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl <;> assumption
  have hu : u.Prime := by
    have : u ∈ ({r, s} : Finset ℕ) := by rw [← htu]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl <;> assumption
  set e := N.factorization t with he
  have he0 : e ≠ 0 := by omega
  have hte : t ^ e < σ 1 (t ^ e) := eipl_pow_lt_sigma ht he0
  -- `t < q` and `u < q` in both branches
  have hlt : t < q ∧ u < q := by
    rcases hcase with ⟨-, hq0⟩ | ⟨hv, hue, htu1, -, -⟩
    · have htq : t < q := hq0 ▸ lt_sigma_prime_pow ht he0
      have hf0 : N.factorization u ≠ 0 := by
        intro h0
        rw [h0, sigma_one_apply_prime_pow hu, Finset.sum_range_one, pow_zero] at hB
        have := Nat.one_lt_pow hj.ne' ht.one_lt
        omega
      have h1 := lt_sigma_prime_pow hu hf0
      have h2 : t ^ j < t ^ e := Nat.pow_lt_pow_right ht.one_lt hje
      refine ⟨htq, ?_⟩
      rw [hB] at h1
      rw [hq0] at hte
      omega
    · rw [hv, pow_one] at hA
      have hu3 : 3 ≤ u := by omega
      have htu' : u + 1 ≤ t := by
        have hd := Nat.div_add_mod t u
        rw [htu1] at hd
        rcases Nat.eq_zero_or_pos (t / u) with h0 | h0
        · rw [h0, mul_zero, zero_add] at hd
          exact absurd hd.symm ht.one_lt.ne'
        · nlinarith
      have h2 : t ^ 2 ≤ t ^ e := Nat.pow_le_pow_right ht.pos (by omega)
      have h4 : t * u < t ^ 2 := by
        rw [sq]; exact Nat.mul_lt_mul_of_pos_left (by omega) ht.pos
      have h3 : t * u < q * u := by
        rw [← hA]; omega
      have htq : t < q := Nat.lt_of_mul_lt_mul_right h3
      exact ⟨htq, by omega⟩
  rcases hptu with rfl | rfl
  · exact hlt.1.le
  · exact hlt.2.le

/-- **Special exponent 1, a prime above the special prime: at least three index primes.** Let
`N = q m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and `q ∤ m`. If some
prime factor of `N` exceeds `q`, then the Euler index `σ(m ^ 2) / q` has at least three prime
factors. This is a restricted result (special exponent 1, a prime factor above `q`); whether
`q` can be the largest prime factor is open, so the bound is not claimed for every odd perfect
number. Its novelty has not been verified. -/
theorem three_le_card_primeFactors_eulerIndex_of_special_lt (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) {p : ℕ} (hp : p ∈ N.primeFactors) (hlt : q < p) :
    3 ≤ (eulerIndex q 1 m).primeFactors.card := by
  have h2 := two_le_card_primeFactors_eulerIndex_of_exponent_one h hq hN hqm
  by_contra h3
  have hc : (eulerIndex q 1 m).primeFactors.card = 2 := by omega
  obtain ⟨r, s, hrs, hJ⟩ := Finset.card_eq_two.mp hc
  have hr : r.Prime := Nat.prime_of_mem_primeFactors
    (show r ∈ (eulerIndex q 1 m).primeFactors by rw [hJ]; simp)
  have hs : s.Prime := Nat.prime_of_mem_primeFactors
    (show s ∈ (eulerIndex q 1 m).primeFactors by rw [hJ]; simp)
  have := eulerIndex_pair_special_largest h hq hN hqm hr hs hrs hJ p hp
  omega

end OddPerfect

#print axioms OddPerfect.eulerIndex_pair_special_largest
#print axioms OddPerfect.three_le_card_primeFactors_eulerIndex_of_special_lt
