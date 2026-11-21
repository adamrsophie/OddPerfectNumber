import OddPerfect.Euler
import OddPerfect.Network
import OddPerfect.Seed.ThreeFree

/-!
# Counting prime factors of an odd perfect number

Inequalities between `Ω N = ∑ p ∈ N.primeFactors, N.factorization p` and
`ω N = N.primeFactors.card` for an odd perfect number `N`.

* Euler bound: `2 ω ≤ Ω + 1`.
* The 3-adic ledger: exponent 2 primes that are `1 (mod 3)` each spend one unit of
  `v_3(N)`; in the 3-free case the divisor sum of an exponent 2 component lands on the
  special prime or on primes of exponent at least 4.
* A transfer bound: if `A₂` is the set of exponent 2 primes not `1 (mod 3)`, then every
  prime factor of `σ(p ^ 2)` for `p ∈ A₂` lies outside `A₂`, so conservation gives
  `|A₂| ≤ Ω - 2 |A₂|`.
* Combining: `12 ω ≤ 5 Ω + 6 v_3(N) + 9`; for `3 ∤ N` this is `12 ω ≤ 5 Ω + 9`, which beats
  the Euler bound as soon as `ω ≥ 3`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

/-- Bridge: `Ω N` is the sum of the exponents over the prime factors. -/
theorem cardFactors_eq_sum_primeFactors (N : ℕ) :
    Ω N = ∑ p ∈ N.primeFactors, N.factorization p := by
  rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]

/-- Bridge: `ω N` is the number of prime factors. -/
theorem cardDistinctFactors_eq_card_primeFactors (N : ℕ) :
    ω N = N.primeFactors.card := by
  rw [cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

private theorem sigma_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

private theorem one_le_fac {N p : ℕ} (hN : N ≠ 0) (hp : p ∈ N.primeFactors) :
    1 ≤ N.factorization p := by
  obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
  exact hpp.factorization_pos_of_dvd hN hpN

/-- Euler bound: every exponent is at least 2 except the special one, which is at least 1. -/
theorem two_mul_card_le_sum_factorization_add_one {N : ℕ} (h : OddPerfect N) :
    2 * N.primeFactors.card ≤ (∑ p ∈ N.primeFactors, N.factorization p) + 1 := by
  obtain ⟨q, hq, hqN, -, -, hev⟩ := exists_special_prime h
  have hqm : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩
  have key : ∀ p ∈ N.primeFactors, 2 ≤ N.factorization p + (if p = q then 1 else 0) := by
    intro p hp
    have h1 := one_le_fac h.ne_zero hp
    split_ifs with hpq
    · omega
    · obtain ⟨j, hj⟩ := hev p (Nat.prime_of_mem_primeFactors hp) hpq
      omega
  have hs := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' N.primeFactors q (fun _ => 1)] at hs
  simp only [Finset.sum_const, smul_eq_mul, if_pos hqm] at hs
  omega

/-- `σ(p ^ 2)` is divisible by 3 when `p ≡ 1 (mod 3)`. -/
private theorem three_dvd_of_mod_one {p : ℕ} (h : p % 3 = 1) : 3 ∣ 1 + p + p ^ 2 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [Nat.add_mod, Nat.pow_mod, h]

/-- Every prime factor of `1 + p + p ^ 2` is `1 (mod 3)` when `p` is not `1 (mod 3)`. -/
private theorem target_mod_three_of_ne {p t : ℕ} (hp : p % 3 ≠ 1) (ht : t.Prime)
    (hdiv : t ∣ 1 + p + p ^ 2) : t % 3 = 1 := by
  refine OPNThreeFree.target_mod_three ht ?_ hdiv
  rintro rfl
  have h1 : (1 + p + p ^ 2) % 3 = 1 := by
    rcases (by omega : p % 3 = 0 ∨ p % 3 = 2) with h | h <;> simp [Nat.add_mod, Nat.pow_mod, h]
  omega

/-- Step 2c: the divisor sum of an exponent 2 component has an odd prime factor, different
from `p`, which is a prime factor of `N`. -/
theorem exists_prime_dvd_sigma_sq {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (he : N.factorization p = 2) :
    ∃ t, t.Prime ∧ t ≠ 2 ∧ t ≠ p ∧ t ∣ σ 1 (p ^ 2) ∧ t ∈ N.primeFactors := by
  obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp (h.odd.of_dvd_nat hpN)
  have hm1 : 1 + p + p ^ 2 ≠ 1 := by have := hpp.two_le; omega
  have hmod : (1 + p + p ^ 2) % 2 = 1 := by simp [Nat.add_mod, Nat.pow_mod, hp2]
  set t := (1 + p + p ^ 2).minFac
  have ht : t.Prime := Nat.minFac_prime hm1
  have htd : t ∣ 1 + p + p ^ 2 := Nat.minFac_dvd _
  have ht2 : t ≠ 2 := by
    intro h2
    rw [h2] at htd
    omega
  have htp : t ≠ p := by
    intro htp
    rw [htp, show 1 + p + p ^ 2 = p * (1 + p) + 1 by ring] at htd
    exact hpp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right p _)).mp htd))
  have hts : t ∣ σ 1 (p ^ 2) := by rwa [sigma_sq hpp]
  exact ⟨t, ht, ht2, htp, hts, Nat.mem_primeFactors.mpr
    ⟨ht, OPNStarter.force_prime h.perfect hpp he ht ht2 hts, h.ne_zero⟩⟩

/-- Step 2a: each exponent 2 prime that is `1 (mod 3)` spends one unit of `v_3(N)`. -/
theorem card_sq_mod_three_eq_one_le {N : ℕ} (h : OddPerfect N) :
    {p ∈ N.primeFactors | N.factorization p = 2 ∧ p % 3 = 1}.card ≤ N.factorization 3 := by
  set S := {p ∈ N.primeFactors | N.factorization p = 2 ∧ p % 3 = 1}
  have hone : ∀ p ∈ S, 1 ≤ sigmaWeight N p 3 := by
    intro p hpS
    obtain ⟨hp, he, h1⟩ := Finset.mem_filter.mp hpS
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hne : σ 1 (p ^ N.factorization p) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
    refine (Nat.prime_three.dvd_iff_one_le_factorization hne).mp ?_
    rw [he, sigma_sq hpp]
    exact three_dvd_of_mod_one h1
  calc S.card = ∑ p ∈ S, 1 := Finset.card_eq_sum_ones S
    _ ≤ ∑ p ∈ S, sigmaWeight N p 3 := Finset.sum_le_sum hone
    _ ≤ ∑ p ∈ N.primeFactors, sigmaWeight N p 3 :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = N.factorization 3 := sigmaWeight_sum_eq h.perfect Nat.prime_three (by decide)

/-- Step 2b: if `3 ∤ N`, an exponent 2 prime is `2 (mod 3)`, and each prime factor of its
divisor sum is `1 (mod 3)`, divides `N`, and is either the special prime (odd exponent)
or has exponent at least 4. -/
theorem three_free_sq_transfer {N p t : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hp : p.Prime) (he : N.factorization p = 2) (ht : t.Prime) (hdiv : t ∣ σ 1 (p ^ 2)) :
    p % 3 = 2 ∧ t % 3 = 1 ∧ t ∣ N ∧ (Odd (N.factorization t) ∨ 4 ≤ N.factorization t) := by
  obtain ⟨hp3, htN, -, ht3, hne⟩ :=
    OPNThreeFree.exact_square_transfer h.perfect h3 hp he ht hdiv
  refine ⟨hp3, ht3, htN, ?_⟩
  have h1 := ht.factorization_pos_of_dvd h.ne_zero htN
  rcases Nat.even_or_odd (N.factorization t) with ⟨j, hj⟩ | ho
  · right; omega
  · exact Or.inl ho

/-- Transfer bound: let `A₂` be the exponent 2 primes not `1 (mod 3)`. For `p ∈ A₂` every
prime factor of `σ(p ^ 2)` is `1 (mod 3)`, hence outside `A₂`; conservation at the
receiving primes gives `|A₂| ≤ Ω - 2 |A₂|`. -/
theorem three_mul_card_sq_mod_three_ne_one_le {N : ℕ} (h : OddPerfect N) :
    3 * {p ∈ N.primeFactors | N.factorization p = 2 ∧ p % 3 ≠ 1}.card ≤
      ∑ p ∈ N.primeFactors, N.factorization p := by
  set A := {p ∈ N.primeFactors | N.factorization p = 2 ∧ p % 3 ≠ 1}
  have hAsub : A ⊆ N.primeFactors := Finset.filter_subset _ _
  set R := N.primeFactors \ A
  have hA2 : ∑ p ∈ A, N.factorization p = 2 * A.card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp => by simp [(Finset.mem_filter.mp hp).2.1]
  have hsplit : ∑ t ∈ R, N.factorization t + ∑ p ∈ A, N.factorization p =
      ∑ p ∈ N.primeFactors, N.factorization p := Finset.sum_sdiff hAsub
  have hone : ∀ p ∈ A, 1 ≤ ∑ t ∈ R, sigmaWeight N p t := by
    intro p hpA
    obtain ⟨hp, he, hp3⟩ := Finset.mem_filter.mp hpA
    have hpp := Nat.prime_of_mem_primeFactors hp
    obtain ⟨t, ht, -, -, hts, htN⟩ := exists_prime_dvd_sigma_sq h hp he
    have ht3 : t % 3 = 1 := target_mod_three_of_ne hp3 ht (by rwa [sigma_sq hpp] at hts)
    have htR : t ∈ R := Finset.mem_sdiff.mpr
      ⟨htN, fun htA => (Finset.mem_filter.mp htA).2.2 ht3⟩
    have hw : 1 ≤ sigmaWeight N p t := by
      have hne : σ 1 (p ^ N.factorization p) ≠ 0 :=
        (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
      refine (ht.dvd_iff_one_le_factorization hne).mp ?_
      rwa [he]
    exact hw.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) htR)
  have hcount : A.card ≤ ∑ t ∈ R, N.factorization t :=
    calc A.card = ∑ p ∈ A, 1 := Finset.card_eq_sum_ones A
      _ ≤ ∑ p ∈ A, ∑ t ∈ R, sigmaWeight N p t := Finset.sum_le_sum hone
      _ = ∑ t ∈ R, ∑ p ∈ A, sigmaWeight N p t := Finset.sum_comm
      _ ≤ ∑ t ∈ R, ∑ p ∈ N.primeFactors, sigmaWeight N p t :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum_of_subset hAsub
      _ = ∑ t ∈ R, N.factorization t := by
        refine Finset.sum_congr rfl fun t htR => ?_
        have htN := (Finset.mem_sdiff.mp htR).1
        obtain ⟨ht, htd, -⟩ := Nat.mem_primeFactors.mp htN
        refine sigmaWeight_sum_eq h.perfect ht ?_
        rintro rfl
        exact h.not_two_dvd htd
  omega

/-- Refined Euler count: an exponent 2 prime contributes 2, the special prime at least 1,
and every other prime at least 4. -/
private theorem four_mul_card_le {N : ℕ} (h : OddPerfect N) :
    4 * N.primeFactors.card ≤ (∑ p ∈ N.primeFactors, N.factorization p) +
      2 * {p ∈ N.primeFactors | N.factorization p = 2 ∧ p % 3 = 1}.card +
      2 * {p ∈ N.primeFactors | N.factorization p = 2 ∧ p % 3 ≠ 1}.card + 3 := by
  obtain ⟨q, hq, hqN, -, -, hev⟩ := exists_special_prime h
  have hqm : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩
  have key : ∀ p ∈ N.primeFactors, 4 ≤ N.factorization p +
      2 * (if N.factorization p = 2 ∧ p % 3 = 1 then 1 else 0) +
      2 * (if N.factorization p = 2 ∧ p % 3 ≠ 1 then 1 else 0) +
      3 * (if p = q then 1 else 0) := by
    intro p hp
    have h1 := one_le_fac h.ne_zero hp
    by_cases hpq : p = q
    · rw [if_pos hpq]
      split_ifs <;> omega
    · rw [if_neg hpq]
      obtain ⟨j, hj⟩ := hev p (Nat.prime_of_mem_primeFactors hp) hpq
      split_ifs <;> omega
  have hs := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.card_filter, ← Finset.card_filter,
    Finset.sum_ite_eq' N.primeFactors q (fun _ => 1)] at hs
  simp only [Finset.sum_const, smul_eq_mul, if_pos hqm] at hs
  omega

/-- Step 3, general form: for every odd perfect number,
`12 ω ≤ 5 Ω + 6 v_3(N) + 9`. -/
theorem twelve_mul_card_le {N : ℕ} (h : OddPerfect N) :
    12 * N.primeFactors.card ≤
      5 * (∑ p ∈ N.primeFactors, N.factorization p) + 6 * N.factorization 3 + 9 := by
  have h1 := four_mul_card_le h
  have h2 := card_sq_mod_three_eq_one_le h
  have h3 := three_mul_card_sq_mod_three_ne_one_le h
  omega

/-- Step 3, 3-free case: if `3 ∤ N` then `12 ω ≤ 5 Ω + 9`, that is `Ω ≥ (12 ω - 9) / 5`.
Since `ω ≥ 3`, this strictly improves the Euler bound `Ω ≥ 2 ω - 1`. -/
theorem twelve_mul_card_le_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    12 * N.primeFactors.card ≤ 5 * (∑ p ∈ N.primeFactors, N.factorization p) + 9 := by
  have := twelve_mul_card_le h
  rw [Nat.factorization_eq_zero_of_not_dvd h3] at this
  omega

/-- Step 3 in terms of `Ω` and `ω`: `12 ω(N) ≤ 5 Ω(N) + 6 v_3(N) + 9`. -/
theorem twelve_mul_omega_le {N : ℕ} (h : OddPerfect N) :
    12 * ω N ≤ 5 * Ω N + 6 * N.factorization 3 + 9 := by
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  exact twelve_mul_card_le h

/-- Step 3 in terms of `Ω` and `ω`, 3-free case: `12 ω(N) ≤ 5 Ω(N) + 9`. -/
theorem twelve_mul_omega_le_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    12 * ω N ≤ 5 * Ω N + 9 := by
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  exact twelve_mul_card_le_of_not_three_dvd h h3

/-- The Euler bound in terms of `Ω` and `ω`: `2 ω(N) ≤ Ω(N) + 1`. -/
theorem two_mul_omega_le {N : ℕ} (h : OddPerfect N) : 2 * ω N ≤ Ω N + 1 := by
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  exact two_mul_card_le_sum_factorization_add_one h

end OddPerfect

#print axioms OddPerfect.cardFactors_eq_sum_primeFactors
#print axioms OddPerfect.cardDistinctFactors_eq_card_primeFactors
#print axioms OddPerfect.two_mul_card_le_sum_factorization_add_one
#print axioms OddPerfect.exists_prime_dvd_sigma_sq
#print axioms OddPerfect.card_sq_mod_three_eq_one_le
#print axioms OddPerfect.three_free_sq_transfer
#print axioms OddPerfect.three_mul_card_sq_mod_three_ne_one_le
#print axioms OddPerfect.twelve_mul_card_le
#print axioms OddPerfect.twelve_mul_card_le_of_not_three_dvd
#print axioms OddPerfect.twelve_mul_omega_le
#print axioms OddPerfect.twelve_mul_omega_le_of_not_three_dvd
#print axioms OddPerfect.two_mul_omega_le
