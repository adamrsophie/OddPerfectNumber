import OddPerfect.EulerIndexPair
import OddPerfect.SpecialPrime

/-!
# The two prime Euler index family and the prime 5

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1, `q ∤ m`,
and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors `r ≠ s`.
Then `5 ∤ v_5(N) + 1`.

Proof: if `q = 5` the exponent of 5 is 1. Otherwise `5 ∣ v_5(N) + 1` gives
`σ(5 ^ 4) = 781 = 11 * 71 ∣ σ(5 ^ v_5(N))`, which divides `σ(m ^ 2) = q J`. Since `q ≡ 1 (mod 4)`,
neither 11 nor 71 is `q`, so both divide `J` and `{r, s} = {11, 71}`. Both are `≡ 3 (mod 4)`,
which the landed `eulerIndex_pair_not_both_three_mod_four` excludes.

Restricted result; no published source was checked; novelty not verified. It does not exclude
the two prime index family.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairFive

/-- Divisor sum of a full prime power component divides the divisor sum of the number. -/
private lemma eipf_sigma_component_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    σ 1 (p ^ n.factorization p) ∣ σ 1 n := by
  have hcop := (Nat.coprime_ordCompl hp hn).pow_left (n.factorization p)
  calc σ 1 (ordProj[p] n) ∣ σ 1 (ordProj[p] n) * σ 1 (ordCompl[p] n) := dvd_mul_right _ _
    _ = σ 1 (ordProj[p] n * ordCompl[p] n) :=
      (isMultiplicative_sigma.map_mul_of_coprime hcop).symm
    _ = σ 1 n := by rw [Nat.ordProj_mul_ordCompl_eq_self]

/-- The exponent of a prime `p` in `q * m ^ 2`. -/
private lemma eipf_factorization {q m p : ℕ} (hq : q.Prime) (hm : m ≠ 0) :
    (q * m ^ 2).factorization p = (if q = p then 1 else 0) + (m ^ 2).factorization p := by
  rw [Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
    hq.factorization, Finsupp.single_apply]

end EulerIndexPairFive

open EulerIndexPairFive

variable {N q m r s : ℕ}

/-- **Two prime index, the exponent of 5.** Let `N = q m ^ 2` be an odd perfect number with
special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has
exactly the two prime factors `r ≠ s`. Then `5 ∤ v_5(N) + 1`: otherwise `11` and `71` both
divide `J`, and the two primes of `J` would both be `≡ 3 (mod 4)`. Restricted result; no
published source was checked; novelty not verified. -/
theorem eulerIndex_pair_not_five_dvd_succ (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) : ¬ 5 ∣ N.factorization 5 + 1 := by
  intro h5
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac := eipf_factorization (p := 5) hq hm
  rw [← hN] at hfac
  by_cases hq5 : q = 5
  · subst hq5
    have h0 : (m ^ 2).factorization 5 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (Nat.prime_five.dvd_of_dvd_pow hd))
    rw [ite_eq_left rfl, h0] at hfac
    omega
  rw [ite_eq_right hq5, zero_add] at hfac
  have hqf : N.factorization q = 1 := by
    have := eipf_factorization (p := q) hq hm
    rw [← hN, ite_eq_left rfl,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd))] at this
    exact this
  have hq4 := (special_mod_four h hq (by rw [hqf]; exact odd_one)).1
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hsig := sigma_sq_eq_mul_eulerIndex h hq hN1 hqm
  have hJ0 : eulerIndex q 1 m ≠ 0 := (odd_eulerIndex h hq hN1 hqm).pos.ne'
  have h781 : 781 ∣ q ^ 1 * eulerIndex q 1 m := by
    rw [← hsig]
    refine Dvd.dvd.trans ?_ (eipf_sigma_component_dvd (pow_ne_zero 2 hm) Nat.prime_five)
    refine Dvd.dvd.trans ?_ (OPNExample.sigma_prime_pow_dvd (a := 4) Nat.prime_five
      (by rw [← hfac]; exact h5))
    rw [sigma_one_apply_prime_pow Nat.prime_five]
    decide
  have hmem (t : ℕ) (ht : t.Prime) (ht4 : t % 4 = 3) (htd : t ∣ 781) :
      t ∈ ({r, s} : Finset ℕ) := by
    rw [← hJ, Nat.mem_primeFactors]
    refine ⟨ht, ?_, hJ0⟩
    rcases (Nat.Prime.dvd_mul ht).mp (htd.trans h781) with hd | hd
    · have := (Nat.prime_dvd_prime_iff_eq ht hq).mp (ht.dvd_of_dvd_pow hd)
      omega
    · exact hd
  have h11 := hmem 11 (by norm_num) (by norm_num) (by norm_num)
  have h71 := hmem 71 (by norm_num) (by norm_num) (by norm_num)
  apply eulerIndex_pair_not_both_three_mod_four h hq hN hqm hr hs hrs hJ
  simp only [Finset.mem_insert, Finset.mem_singleton] at h11 h71
  rcases h11 with h | h <;> rcases h71 with h' | h' <;> omega

end OddPerfect

#print axioms OddPerfect.eulerIndex_pair_not_five_dvd_succ
