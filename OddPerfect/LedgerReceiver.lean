import OddPerfect.LedgerOrders
import OddPerfect.LedgerThreeFree
import OddPerfect.Counting
import OddPerfect.SpecialPrime

/-!
# One receiver class

Conditional family results. Let `N` be an odd perfect number and `q` a number such that every
prime factor of `N` that is `≡ 1 (mod 3)` equals `q` (hypothesis `hrecv`).

* `receiver_eq_two`: if `p ∣ N` and `3 ∣ e_p + 1` then `p ≠ q` and `e_p = 2`. The divisors `3`
  and `e_p + 1` of `e_p + 1` are orders of `p` modulo receiver primes dividing `σ(p ^ e_p)`, all
  `≡ 1 (mod 3)` (`card_threeOrders_le`); the only candidate is `q`, so the two orders agree.
  For `p = q` there is no candidate at all, since `q ∤ σ(q ^ e_q)`; so `3 ∤ e_q + 1`.
* `two_mul_card_add_two_mul_card_le`: for any set `X` of prime factors with exponents at least
  4, `2 ω(N) + 2 |X| ≤ Ω(N) + 1`.
* `receiver_three_free`: if moreover `3 ∤ N` and `q` is the special prime, every ordinary prime
  factor is `≡ 2 (mod 3)`, so by `three_dvd_of_thirtyone_exceptional_mod_three` at least 32
  ordinary primes have `3 ∤ e_p + 1`; hence `ω(N) ≥ 33` and `Ω(N) ≥ 2 ω(N) + 63`.

Whether this is in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

variable {N q : ℕ}

/-- Under `hrecv`, the receivers of order divisible by 3 of a prime factor `p` lie in `{q}`,
and there are none when `p = q`. -/
theorem receiversIn_subset (hrecv : ∀ t ∈ N.primeFactors, t % 3 = 1 → t = q) (p : ℕ) :
    receiversIn N p (N.primeFactors.filter (· % 3 = 1)) ⊆ {q} := by
  intro t ht
  simp only [receiversIn, Finset.mem_filter] at ht
  exact Finset.mem_singleton.mpr (hrecv t ht.1.1 ht.1.2)

/-- **One receiver class.** Let `N` be an odd perfect number in which every prime factor
`≡ 1 (mod 3)` equals `q`. If `p ∣ N` and `3 ∣ e_p + 1`, then `p ≠ q` and `e_p = 2`.
Conditional family result; whether this is in the literature was not verified. -/
theorem receiver_eq_two (h : OddPerfect N) (hrecv : ∀ t ∈ N.primeFactors, t % 3 = 1 → t = q)
    {p : ℕ} (hp : p ∈ N.primeFactors) (h3 : 3 ∣ N.factorization p + 1) :
    p ≠ q ∧ N.factorization p = 2 := by
  have hcard := card_threeOrders_le h hp
  have h3mem : 3 ∈ threeOrders N p := by
    simp only [threeOrders, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨h3, by omega⟩, dvd_refl 3⟩
  have hpq : p ≠ q := by
    rintro rfl
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hempty : receiversIn N p (N.primeFactors.filter (· % 3 = 1)) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun t ht => ?_
      have htq := Finset.mem_singleton.mp (receiversIn_subset hrecv p ht)
      subst htq
      simp only [receiversIn, Finset.mem_filter] at ht
      exact hpp.one_lt.ne' ((coprime_sigma_prime_pow hpp _).symm.eq_one_of_dvd ht.2)
    rw [hempty, Finset.card_empty] at hcard
    exact absurd (Finset.card_pos.mpr ⟨3, h3mem⟩) (by omega)
  refine ⟨hpq, ?_⟩
  have hle := Finset.card_le_card (receiversIn_subset hrecv (N := N) (q := q) p)
  rw [Finset.card_singleton] at hle
  have hmem : N.factorization p + 1 ∈ threeOrders N p := by
    simp only [threeOrders, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_refl _, by omega⟩, h3⟩
  by_contra hne
  have hsub : ({3, N.factorization p + 1} : Finset ℕ) ⊆ threeOrders N p := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h3mem
    · exact hmem
  have := Finset.card_le_card hsub
  rw [Finset.card_pair (by omega)] at this
  omega

/-- Under `hrecv`, the prime `q` has `3 ∤ e_q + 1`.
Conditional family result; whether this is in the literature was not verified. -/
theorem receiver_not_three_dvd_succ (h : OddPerfect N)
    (hrecv : ∀ t ∈ N.primeFactors, t % 3 = 1 → t = q) : ¬ 3 ∣ N.factorization q + 1 := by
  intro h3
  have hqN : q ∈ N.primeFactors := by
    by_contra hq
    rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])] at h3
    omega
  exact (receiver_eq_two h hrecv hqN h3).1 rfl

/-- **Counting lemma.** For an odd perfect number `N` and a set `X` of prime factors whose
exponents are at least 4, `2 ω(N) + 2 |X| ≤ Ω(N) + 1`. -/
theorem two_mul_card_add_two_mul_card_le (h : OddPerfect N) {X : Finset ℕ}
    (hX : X ⊆ N.primeFactors) (hX4 : ∀ p ∈ X, 4 ≤ N.factorization p) :
    2 * N.primeFactors.card + 2 * X.card ≤ (∑ p ∈ N.primeFactors, N.factorization p) + 1 := by
  obtain ⟨s, hs, hsN, -, -, hev⟩ := exists_special_prime h
  have hsm : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs, hsN, h.ne_zero⟩
  have key : ∀ p ∈ N.primeFactors,
      2 + (if p ∈ X then 2 else 0) ≤ N.factorization p + (if p = s then 1 else 0) := by
    intro p hp
    obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
    have h1 : 1 ≤ N.factorization p := hpp.factorization_pos_of_dvd h.ne_zero hpN
    by_cases hpX : p ∈ X
    · have := hX4 p hpX
      simp only [if_pos hpX]
      omega
    · simp only [if_neg hpX]
      split_ifs with hps
      · omega
      · obtain ⟨j, hj⟩ := hev p hpp hps
        omega
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' N.primeFactors s
    (fun _ => 1), Finset.sum_ite_mem, Finset.inter_eq_right.mpr hX] at hsum
  simp only [Finset.sum_const, smul_eq_mul, if_pos hsm] at hsum
  omega

/-- **One receiver class, 3-free.** Let `N` be an odd perfect number with `3 ∤ N`, special prime
`q`, and every prime factor `≡ 1 (mod 3)` equal to `q`. Then at least 32 prime factors `p ≠ q`
have `3 ∤ e_p + 1`, `ω(N) ≥ 33` and `Ω(N) ≥ 2 ω(N) + 63`.
Conditional family result; whether this is in the literature was not verified. -/
theorem receiver_three_free (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (h3 : ¬ 3 ∣ N) (hrecv : ∀ t ∈ N.primeFactors, t % 3 = 1 → t = q) :
    32 ≤ ((N.primeFactors.erase q).filter (fun p => ¬ 3 ∣ N.factorization p + 1)).card ∧
      33 ≤ ω N ∧ 2 * ω N + 63 ≤ Ω N := by
  set X := (N.primeFactors.erase q).filter (fun p => ¬ 3 ∣ N.factorization p + 1) with hXdef
  have hmod : ∀ p ∈ N.primeFactors, p ≠ q → p % 3 = 2 := by
    intro p hp hpq
    have h0 : p % 3 ≠ 0 := fun h0 =>
      h3 ((Nat.dvd_of_mod_eq_zero h0).trans (Nat.dvd_of_mem_primeFactors hp))
    have h1 : p % 3 ≠ 1 := fun h1 => hpq (hrecv p hp h1)
    omega
  have hX32 : 32 ≤ X.card := by
    by_contra hlt
    exact h3 (three_dvd_of_thirtyone_exceptional_mod_three h hq hodd
      (Nat.le_of_lt_succ (not_le.mp hlt))
      fun p hp hpq _ => hmod p hp hpq)
  have hqN : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, ?_, h.ne_zero⟩
    by_contra hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hnd] at hodd
    exact absurd hodd (by decide)
  have hXsub : X ⊆ N.primeFactors.erase q := Finset.filter_subset _ _
  have hcard : X.card + 1 ≤ N.primeFactors.card := by
    have := Finset.card_le_card hXsub
    rw [Finset.card_erase_of_mem hqN] at this
    have := Finset.card_pos.mpr ⟨q, hqN⟩
    omega
  have hX4 : ∀ p ∈ X, 4 ≤ N.factorization p := by
    intro p hp
    obtain ⟨hp1, hp3⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp1
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hpN
    have h1 : 1 ≤ N.factorization p := hpp.factorization_pos_of_dvd h.ne_zero hpd
    obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hpp hpq
    have : N.factorization p ≠ 2 := fun h2 => hp3 (by rw [h2])
    omega
  have hcount := two_mul_card_add_two_mul_card_le h
    (hXsub.trans (Finset.erase_subset _ _)) hX4
  rw [cardDistinctFactors_eq_card_primeFactors, cardFactors_eq_sum_primeFactors]
  omega

end OddPerfect

#print axioms OddPerfect.receiversIn_subset
#print axioms OddPerfect.receiver_eq_two
#print axioms OddPerfect.receiver_not_three_dvd_succ
#print axioms OddPerfect.two_mul_card_add_two_mul_card_le
#print axioms OddPerfect.receiver_three_free
