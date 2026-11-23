import OddPerfect.Phi3
import OddPerfect.SpecialPrime
import OddPerfect.ForcingClosed
import OddPerfect.Spoof
import OddPerfect.MixedIndexCheck

/-!
# Exponent four at the prime three and the capacity of three

Let `N` be an odd perfect number with `3 ^ 4` exactly dividing `N`, and suppose every prime
`p` among `7, 11, 19, 31, 127, 5419` that divides `N` has `3 ∣ v_p(N) + 1`. Then
`p ^ 2 + p + 1` divides the divisor sum of the `p` component, so every odd prime factor of
`p ^ 2 + p + 1` divides `N`. The chain of forced primes is:

* `σ(3 ^ 4) = 121 = 11 ^ 2`, so `11 ∣ N`;
* `11 ^ 2 + 11 + 1 = 133 = 7 · 19`, so `7 ∣ N` and `19 ∣ N`;
* `19 ^ 2 + 19 + 1 = 381 = 3 · 127`, so `127 ∣ N`;
* `127 ^ 2 + 127 + 1 = 16257 = 3 · 5419`, so `5419 ∣ N` (`5419` is prime);
* `5419 ^ 2 + 5419 + 1 = 29370981 = 3 · 31 · 313 · 1009`, so `31 ∣ N`.

The five primes `7, 19, 31, 127, 5419` are `1` modulo `3`, so each sends a factor `3` into
`σ(N) = 2N`; but `v_3(N) = 4`. All six primes are `3` modulo `4`, so none is the special
prime, and no hypothesis about the special prime is needed in the core form.

Consequence: an odd perfect number with `3 ^ 4` exactly dividing it is divisible by `p ^ 4`
for some `p` among the six primes with `3 ∤ v_p(N) + 1`. Nothing is claimed about odd
perfect numbers in general beyond this. Whether this statement is in the literature was not
verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

/-- `phi3 p` divides the divisor sum of the `p` component when `3 ∣ v_p(N) + 1`. -/
private theorem phi3_dvd_sigma_comp_four {p : ℕ} (hp : p.Prime)
    (h3 : 3 ∣ N.factorization p + 1) : phi3 p ∣ σ 1 (p ^ N.factorization p) := by
  rw [← sigma_prime_sq hp]
  exact ForcingClosed.sigma_prime_pow_dvd_of_dvd hp h3

/-- An odd prime factor of `phi3 p` divides `N` when `3 ∣ v_p(N) + 1`. -/
private theorem dvd_of_dvd_phi3_comp_four (h : OddPerfect N) {p : ℕ} (hp : p.Prime)
    (h3 : 3 ∣ N.factorization p + 1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrd : r ∣ phi3 p) : r ∣ N :=
  OPNStarter.force_prime h.perfect hp rfl hr hr2 (hrd.trans (phi3_dvd_sigma_comp_four hp h3))

/-- A prime `p ≡ 1 (mod 3)` with `3 ∣ v_p(N) + 1` has `3 ∣ σ(p ^ v_p(N))`. -/
private theorem three_dvd_sigma_comp_four {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1)
    (h3 : 3 ∣ N.factorization p + 1) : 3 ∣ σ 1 (p ^ N.factorization p) :=
  ((three_dvd_phi3_iff p).2 hp3).trans (phi3_dvd_sigma_comp_four hp h3)

/-- Core form. Let `N` be an odd perfect number with `v_3(N) = 4`. If every prime `p` among
`7, 11, 19, 31, 127, 5419` that divides `N` has `3 ∣ v_p(N) + 1`, a contradiction follows:
the primes `7, 19, 31, 127, 5419` all divide `N` and each sends a factor `3`, but only four
are available. -/
theorem false_of_three_pow_four_of_index_three (h : OddPerfect N)
    (h3 : N.factorization 3 = 4)
    (hA : ∀ p ∈ ({7, 11, 19, 31, 127, 5419} : Finset ℕ), p ∣ N →
      3 ∣ N.factorization p + 1) : False := by
  have h11 : 11 ∣ N := OPNStarter.force_prime h.perfect Nat.prime_three h3 (by norm_num)
    (by norm_num) (by rw [Spoof.sigma_three_pow_four]; norm_num)
  have a11 := hA 11 (by simp) h11
  have h7 : 7 ∣ N := dvd_of_dvd_phi3_comp_four h (by norm_num) a11 (by norm_num) (by norm_num)
    (by decide)
  have h19 : 19 ∣ N := dvd_of_dvd_phi3_comp_four h (by norm_num) a11 (by norm_num) (by norm_num)
    (by decide)
  have a19 := hA 19 (by simp) h19
  have h127 : 127 ∣ N := dvd_of_dvd_phi3_comp_four h (by norm_num) a19 (by norm_num) (by norm_num)
    (by decide)
  have a127 := hA 127 (by simp) h127
  have h5419 : 5419 ∣ N := dvd_of_dvd_phi3_comp_four h (by norm_num) a127 (by norm_num)
    (by norm_num) (by decide)
  have a5419 := hA 5419 (by simp) h5419
  have h31 : 31 ∣ N := dvd_of_dvd_phi3_comp_four h (by norm_num) a5419 (by norm_num) (by norm_num)
    (by decide)
  have a7 := hA 7 (by simp) h7
  have a31 := hA 31 (by simp) h31
  have hsub : ({7, 19, 31, 127, 5419} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Nat.mem_primeFactors.2 ⟨by norm_num, h7, h.ne_zero⟩
    · exact Nat.mem_primeFactors.2 ⟨by norm_num, h19, h.ne_zero⟩
    · exact Nat.mem_primeFactors.2 ⟨by norm_num, h31, h.ne_zero⟩
    · exact Nat.mem_primeFactors.2 ⟨by norm_num, h127, h.ne_zero⟩
    · exact Nat.mem_primeFactors.2 ⟨by norm_num, h5419, h.ne_zero⟩
  have hc := MixedIndex.card_le_of_senders h.perfect Nat.prime_three (by norm_num) _ hsub
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact three_dvd_sigma_comp_four (by norm_num) (by norm_num) a7
      · exact three_dvd_sigma_comp_four (by norm_num) (by norm_num) a19
      · exact three_dvd_sigma_comp_four (by norm_num) (by norm_num) a31
      · exact three_dvd_sigma_comp_four (by norm_num) (by norm_num) a127
      · exact three_dvd_sigma_comp_four (by norm_num) (by norm_num) a5419)
  rw [h3] at hc
  exact absurd hc (by decide)

/-- Headline. An odd perfect number with `3 ^ 4` exactly dividing it is divisible by `p ^ 4`
for some `p` among `7, 11, 19, 31, 127, 5419` with `3 ∤ v_p(N) + 1`. -/
theorem exists_pow_four_dvd_of_three_pow_four (h : OddPerfect N)
    (h3 : N.factorization 3 = 4) :
    ∃ p ∈ ({7, 11, 19, 31, 127, 5419} : Finset ℕ), p ^ 4 ∣ N ∧
      ¬ 3 ∣ N.factorization p + 1 := by
  obtain ⟨q, hq, -, hq4, hk, -⟩ := exists_special_prime h
  have hodd : ∀ p ∈ ({7, 11, 19, 31, 127, 5419} : Finset ℕ), p.Prime ∧ p % 4 = 3 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  by_contra hne
  push Not at hne
  refine false_of_three_pow_four_of_index_three h h3 (fun p hpL hpN => ?_)
  by_contra h3p
  obtain ⟨hp, hp4⟩ := hodd p hpL
  have hpq : p ≠ q := by rintro rfl; omega
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq
    (Nat.odd_iff.2 (by omega)) hp hpq
  have h1 := (hp.dvd_iff_one_le_factorization h.ne_zero).1 hpN
  have h4 : 4 ≤ N.factorization p := by
    by_contra hlt
    have : N.factorization p = 2 := by omega
    exact h3p (by rw [this])
  exact h3p (hne p hpL ((hp.pow_dvd_iff_le_factorization h.ne_zero).2 h4))

end OddPerfect

#print axioms OddPerfect.false_of_three_pow_four_of_index_three
#print axioms OddPerfect.exists_pow_four_dvd_of_three_pow_four
