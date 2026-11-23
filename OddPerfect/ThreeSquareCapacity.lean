import OddPerfect.Network
import OddPerfect.Phi3
import OddPerfect.SpecialPrime
import OddPerfect.ForcingClosed

/-!
# Exponent two at the prime three and the capacity of three

Let `N` be an odd perfect number with `3 ^ 2` exactly dividing `N`. Call a prime factor `p`
of `N` good when it is not the special prime, `p ≡ 1 (mod 3)` and `3 ∣ v_p(N) + 1`. Then
`p ^ 2 + p + 1` divides the divisor sum of the full `p` component, so it sends at least one
factor `3` and every prime factor of `p ^ 2 + p + 1` divides `N`. The incoming weights at `3`
add up to `v_3(N) = 2`, so at most two good primes exist. A short chain of forced primes,
starting from `σ(3 ^ 2) = 13`, always produces three good primes among
`7, 13, 19, 31, 61, 97, 127, 331` unless one of these primes, not the special prime, has
`3 ∤ v_p(N) + 1`.

The hypothesis family is restricted. Nothing is claimed about odd perfect numbers in general
beyond the stated consequence: an odd perfect number with `3 ^ 2` exactly dividing it is
divisible by the fourth power of one of the eight primes above. Novelty of this statement
was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

/-- `phi3 p` divides the divisor sum of the `p` component when `3 ∣ v_p(N) + 1`. -/
private theorem phi3_dvd_sigma_comp {p : ℕ} (hp : p.Prime) (h3 : 3 ∣ N.factorization p + 1) :
    phi3 p ∣ σ 1 (p ^ N.factorization p) := by
  rw [← sigma_prime_sq hp]
  exact ForcingClosed.sigma_prime_pow_dvd_of_dvd hp h3

/-- An odd prime factor of `phi3 p` divides `N` when `3 ∣ v_p(N) + 1`. -/
private theorem dvd_of_dvd_phi3_comp (h : OddPerfect N) {p : ℕ} (hp : p.Prime)
    (h3 : 3 ∣ N.factorization p + 1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrd : r ∣ phi3 p) : r ∣ N :=
  OPNStarter.force_prime h.perfect hp rfl hr hr2 (hrd.trans (phi3_dvd_sigma_comp hp h3))

/-- A prime `p ≡ 1 (mod 3)` with `3 ∣ v_p(N) + 1` sends weight at least one to `3`. -/
private theorem one_le_sigmaWeight_three {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1)
    (h3 : 3 ∣ N.factorization p + 1) : 1 ≤ sigmaWeight N p 3 := by
  unfold sigmaWeight
  have hd : 3 ∣ σ 1 (p ^ N.factorization p) :=
    ((three_dvd_phi3_iff p).2 hp3).trans (phi3_dvd_sigma_comp hp h3)
  exact (Nat.prime_three.dvd_iff_one_le_factorization
    (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne').1 hd

/-- The data of a good prime: prime, divides `N`, `1` modulo `3`, and `3 ∣ v_p(N) + 1`. -/
private def Good (N p : ℕ) : Prop :=
  p.Prime ∧ p ∣ N ∧ p % 3 = 1 ∧ 3 ∣ N.factorization p + 1

/-- Capacity: with `v_3(N) = 2` there are no three distinct good primes. -/
private theorem false_of_three_good (h : OddPerfect N) (h3 : N.factorization 3 = 2)
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Good N a) (hb : Good N b) (hc : Good N c) : False := by
  have hsum := sigmaWeight_sum_eq h.perfect Nat.prime_three (by decide)
  have hsub : ({a, b, c} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.mem_primeFactors.2 ⟨ha.1, ha.2.1, h.ne_zero⟩
    · exact Nat.mem_primeFactors.2 ⟨hb.1, hb.2.1, h.ne_zero⟩
    · exact Nat.mem_primeFactors.2 ⟨hc.1, hc.2.1, h.ne_zero⟩
  have hle := Finset.sum_le_sum_of_subset (f := fun p => sigmaWeight N p 3) hsub
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc] at hle
  have wa := one_le_sigmaWeight_three ha.1 ha.2.2.1 ha.2.2.2 (N := N)
  have wb := one_le_sigmaWeight_three hb.1 hb.2.2.1 hb.2.2.2 (N := N)
  have wc := one_le_sigmaWeight_three hc.1 hc.2.2.1 hc.2.2.2 (N := N)
  omega

/-- Every prime of the list is prime. -/
private theorem prime_of_mem_list {p : ℕ}
    (hp : p ∈ ({7, 13, 19, 31, 61, 97, 127, 331} : Finset ℕ)) : p.Prime := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- A prime factor other than the special prime whose fourth power does not divide `N` has
exponent exactly `2`. -/
private theorem factorization_eq_two_of_not_pow_four (h : OddPerfect N) {q : ℕ}
    (hq : q.Prime) (hodd : Odd (N.factorization q)) {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    (hpN : p ∣ N) (h4 : ¬ p ^ 4 ∣ N) : N.factorization p = 2 := by
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hp hpq
  have h1 := (hp.dvd_iff_one_le_factorization h.ne_zero).1 hpN
  have h4' : ¬ 4 ≤ N.factorization p := fun hle =>
    h4 ((hp.pow_dvd_iff_le_factorization h.ne_zero).2 hle)
  omega

/-- Core form. Let `N` be an odd perfect number with special prime `q` and `v_3(N) = 2`.
If every prime `p` among `7, 13, 19, 31, 61, 97, 127, 331` that divides `N` and differs
from `q` has `3 ∣ v_p(N) + 1`, a contradiction follows: three distinct such primes would each
send a factor `3`, but only two are available. -/
theorem false_of_three_sq_of_index_three {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : N.factorization 3 = 2)
    (hA : ∀ p ∈ ({7, 13, 19, 31, 61, 97, 127, 331} : Finset ℕ), p ∣ N → p ≠ q →
      3 ∣ N.factorization p + 1) : False := by
  have G : ∀ p ∈ ({7, 13, 19, 31, 61, 97, 127, 331} : Finset ℕ), p % 3 = 1 → p ∣ N →
      p ≠ q → Good N p := fun p hpL hp3 hpN hpq =>
    ⟨prime_of_mem_list hpL, hpN, hp3, hA p hpL hpN hpq⟩
  have h13 : 13 ∣ N := OPNStarter.thirteen_dvd_of_three_sq h.perfect h3
  by_cases hq13 : q = 13
  · subst hq13
    have h7 := (prime_dvd_of_dvd_succ_special h hq hodd (r := 7) (by norm_num) (by norm_num)
      (by norm_num)).1
    have g7 := G 7 (by simp) (by norm_num) h7 (by norm_num)
    have h19 : 19 ∣ N := dvd_of_dvd_phi3_comp h g7.1 g7.2.2.2 (by norm_num) (by norm_num)
      (by decide)
    have g19 := G 19 (by simp) (by norm_num) h19 (by norm_num)
    have h127 : 127 ∣ N := dvd_of_dvd_phi3_comp h g19.1 g19.2.2.2 (by norm_num) (by norm_num)
      (by decide)
    have g127 := G 127 (by simp) (by norm_num) h127 (by norm_num)
    exact false_of_three_good h h3 (by norm_num) (by norm_num) (by norm_num) g7 g19 g127
  have g13 := G 13 (by simp) (by norm_num) h13 (Ne.symm hq13)
  have h61 : 61 ∣ N := dvd_of_dvd_phi3_comp h g13.1 g13.2.2.2 (by norm_num) (by norm_num)
    (by decide)
  by_cases hq61 : q = 61
  · subst hq61
    have h31 := (prime_dvd_of_dvd_succ_special h hq hodd (r := 31) (by norm_num) (by norm_num)
      (by norm_num)).1
    have g31 := G 31 (by simp) (by norm_num) h31 (by norm_num)
    have h331 : 331 ∣ N := dvd_of_dvd_phi3_comp h g31.1 g31.2.2.2 (by norm_num) (by norm_num)
      (by decide)
    have g331 := G 331 (by simp) (by norm_num) h331 (by norm_num)
    exact false_of_three_good h h3 (by norm_num) (by norm_num) (by norm_num) g13 g31 g331
  have g61 := G 61 (by simp) (by norm_num) h61 (Ne.symm hq61)
  have h97 : 97 ∣ N := dvd_of_dvd_phi3_comp h g61.1 g61.2.2.2 (by norm_num) (by norm_num)
    (by decide)
  by_cases hq97 : q = 97
  · subst hq97
    have h7 := (prime_dvd_of_dvd_succ_special h hq hodd (r := 7) (by norm_num) (by norm_num)
      (by norm_num)).1
    have g7 := G 7 (by simp) (by norm_num) h7 (by norm_num)
    exact false_of_three_good h h3 (by norm_num) (by norm_num) (by norm_num) g13 g61 g7
  have g97 := G 97 (by simp) (by norm_num) h97 (Ne.symm hq97)
  exact false_of_three_good h h3 (by norm_num) (by norm_num) (by norm_num) g13 g61 g97

/-- Headline. An odd perfect number with `3 ^ 2` exactly dividing it is divisible by the
fourth power of one of the primes `7, 13, 19, 31, 61, 97, 127, 331`. -/
theorem exists_pow_four_dvd_of_three_sq {N : ℕ} (h : OddPerfect N)
    (h3 : N.factorization 3 = 2) :
    ∃ p ∈ ({7, 13, 19, 31, 61, 97, 127, 331} : Finset ℕ), p ^ 4 ∣ N := by
  obtain ⟨q, hq, -, -, hk, -⟩ := exists_special_prime h
  have hodd : Odd (N.factorization q) := Nat.odd_iff.2 (by omega)
  by_contra hne
  push Not at hne
  refine false_of_three_sq_of_index_three h hq hodd h3 (fun p hpL hpN hpq => ?_)
  rw [factorization_eq_two_of_not_pow_four h hq hodd (prime_of_mem_list hpL) hpq hpN
    (hne p hpL)]

/-- Two exceptional primes. Let `N` be an odd perfect number with special prime `q` and
`v_3(N) = 2`, in which every prime factor other than `q`, `r₁` and `r₂` has exponent `2`.
Then one of `r₁`, `r₂` lies among `7, 13, 19, 31, 61, 97, 127, 331`, differs from `q`, and
its fourth power divides `N`. -/
theorem two_exceptions_three_sq_exception_mod_three {N q r₁ r₂ : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2)
    (h3 : N.factorization 3 = 2) :
    ∃ r, (r = r₁ ∨ r = r₂) ∧ r ∈ ({7, 13, 19, 31, 61, 97, 127, 331} : Finset ℕ) ∧ r ≠ q ∧
      r ^ 4 ∣ N := by
  by_contra hne
  push Not at hne
  refine false_of_three_sq_of_index_three h hq hodd h3 (fun p hpL hpN hpq => ?_)
  have hp := prime_of_mem_list hpL
  have h2 : N.factorization p = 2 := by
    by_cases hr : p = r₁ ∨ p = r₂
    · exact factorization_eq_two_of_not_pow_four h hq hodd hp hpq hpN (hne p hr hpL hpq)
    · push Not at hr
      exact hsq p (Nat.mem_primeFactors.2 ⟨hp, hpN, h.ne_zero⟩) hpq hr.1 hr.2
  rw [h2]

end OddPerfect

#print axioms OddPerfect.false_of_three_sq_of_index_three
#print axioms OddPerfect.exists_pow_four_dvd_of_three_sq
#print axioms OddPerfect.two_exceptions_three_sq_exception_mod_three
