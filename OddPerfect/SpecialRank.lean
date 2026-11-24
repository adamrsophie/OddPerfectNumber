import OddPerfect.Network
import OddPerfect.SpecialPrime

/-!
# The special exponent when one prime exceeds the special prime

Restricted result; whether it is in the literature was not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`.

* `lt_pow_mul_sigma_sub` (rational gap, in integers). Let `q` be an odd prime, `σ(M) < 2M`,
  `b < a`, and `q ^ (a - b) * M ∣ σ(q ^ a) * σ(M)`. Then `M < q ^ (b + 1) * (σ(M) - M)`.
  Write `σ(q ^ a) σ(M) = q ^ (a - b) M J` and `K = (q - 1) J - q ^ (b + 1)`. Then
  `q ^ (a - b) M K = q ^ (a + 1) (σ(M) - M) - σ(M)`, which exceeds `-q ^ (a - b) M`, so
  `K ≥ 0`; and `K ≠ 0`, since `q - 1 ≥ 2` divides `q ^ (b + 1) - 1` and so cannot divide
  `q ^ (b + 1)`. Hence `K ≥ 1`, which is the claim.
* `special_exponent_le_rank_two`. Let `P > q` be the largest prime factor, let every other
  prime factor be at most `q`, let `e = v_P(N)`, let every prime factor below `q` have
  exponent at most `D`, and let the rows `σ(u ^ e_u)` of the primes `u < q` carry at most `β`
  at `q`. Then `a ≤ max (β + e D - 1) ((e + 1) β + e - 1)`.
  If some row of a prime `u < q` is divisible by `P`, then `P < q ^ D`, so
  `σ(P ^ e) < (P + 1) ^ e ≤ q ^ (D e)`. Otherwise all of `v_P(N) = e` comes from the special
  row, so `P ^ e ∣ σ(q ^ a)`, and the rational gap with `M = P ^ e` gives `P - 1 < q ^ (b + 1)`
  for `b = a - v_q(σ(P ^ e)) ≤ β`, so `σ(P ^ e) < q ^ ((b + 1) e)`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Elementary bounds on divisor sums of prime powers -/

/-- Geometric identity for the divisor sum of a prime power, over the integers. -/
private theorem sigma_prime_pow_mul_sub_one {p k : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ k) : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul _ _

private theorem geom_le_succ_pow (p : ℕ) :
    ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), p ^ i ≤ (p + 1) ^ k
  | 0 => by simp
  | k + 1 => by
      have ih := geom_le_succ_pow p k
      have e : ∑ i ∈ Finset.range (k + 1 + 1), p ^ i =
          p * ∑ i ∈ Finset.range (k + 1), p ^ i + 1 := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp [pow_succ, mul_comm]
      have h1 : 1 ≤ (p + 1) ^ k := Nat.one_le_pow _ _ (by omega)
      rw [e, pow_succ]
      nlinarith

/-- `σ(p ^ k) ≤ (p + 1) ^ k` for a prime `p`. -/
theorem sigma_prime_pow_le_succ_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    σ 1 (p ^ k) ≤ (p + 1) ^ k := by
  rw [sigma_one_apply_prime_pow hp]
  exact geom_le_succ_pow p k

/-- `σ(p ^ k) < (p + 1) ^ k` for a prime `p` and `k ≥ 2`. -/
theorem sigma_prime_pow_lt_succ_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    σ 1 (p ^ k) < (p + 1) ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [sigma_one_apply_prime_pow hp]
  have ih := geom_le_succ_pow p j
  have e : ∑ i ∈ Finset.range (j + 1 + 1), p ^ i =
      p * ∑ i ∈ Finset.range (j + 1), p ^ i + 1 := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp [pow_succ, mul_comm]
  have h1 : 1 < (p + 1) ^ j := Nat.one_lt_pow (by omega) (by have := hp.two_le; omega)
  rw [e, pow_succ]
  nlinarith

private theorem sigma_prime_pow_lt_two_mul' {p : ℕ} (hp : p.Prime) (k : ℕ) :
    σ 1 (p ^ k) < 2 * p ^ k := by
  have hg := sigma_prime_pow_mul_sub_one (k := k) hp
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hpk : (0 : ℤ) < (p : ℤ) ^ k := by positivity
  zify
  rw [pow_succ] at hg
  nlinarith

private theorem le_sigma_one {M : ℕ} (hM : M ≠ 0) : M ≤ σ 1 M := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self M hM)

/-! ## The rational gap -/

/-- Rational gap, in integers. Let `q` be an odd prime, `σ(M) < 2 M`, `b < a`, and
`q ^ (a - b) * M ∣ σ(q ^ a) * σ(M)` (that is, `q ^ b σ(q ^ a M) / (q ^ a M)` is an integer).
Then `M < q ^ (b + 1) * (σ(M) - M)`. -/
theorem lt_pow_mul_sigma_sub {q M a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hM : σ 1 M < 2 * M) (hab : b < a) (hd : q ^ (a - b) * M ∣ σ 1 (q ^ a) * σ 1 M) :
    M < q ^ (b + 1) * (σ 1 M - M) := by
  have hM0 : M ≠ 0 := by rintro rfl; simp at hM
  have hle := le_sigma_one hM0
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
  rw [show b + c + 1 - b = c + 1 by omega] at hd
  obtain ⟨J, hJ⟩ := hd
  have hJ' : ((σ 1 (q ^ (b + c + 1)) : ℕ) : ℤ) * (σ 1 M : ℕ) =
      (q : ℤ) ^ (c + 1) * M * J := by exact_mod_cast hJ
  have hg := sigma_prime_pow_mul_sub_one (k := b + c + 1) hq
  have hq3 : (3 : ℤ) ≤ q := by
    have := hq.two_le
    have : 3 ≤ q := by omega
    exact_mod_cast this
  set S : ℤ := ((σ 1 M : ℕ) : ℤ) with hS
  set K : ℤ := ((q : ℤ) - 1) * J - (q : ℤ) ^ (b + 1) with hK
  have key : (q : ℤ) ^ (c + 1) * M * K = (q : ℤ) ^ (b + c + 2) * (S - M) - S := by
    rw [hK]
    linear_combination ((q : ℤ) - 1) * hJ'.symm + S * hg
  have hK0 : K ≠ 0 := by
    intro h0
    have h1 : ((q : ℤ) - 1) * J = (q : ℤ) ^ (b + 1) := by linear_combination h0
    have h2 : (q : ℤ) - 1 ∣ (q : ℤ) ^ (b + 1) := ⟨J, h1.symm⟩
    have h3 : (q : ℤ) - 1 ∣ (q : ℤ) ^ (b + 1) - 1 := by
      simpa using sub_dvd_pow_sub_pow (q : ℤ) 1 (b + 1)
    have h4 : (q : ℤ) - 1 ∣ 1 := by
      have := dvd_sub h2 h3
      simpa using this
    have := Int.le_of_dvd one_pos h4
    linarith
  have hX : (3 : ℤ) ≤ (q : ℤ) ^ (c + 1) :=
    hq3.trans (le_self_pow₀ (by linarith) (by omega))
  have hMpos : (1 : ℤ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM0
  have hSM : (M : ℤ) ≤ S := by rw [hS]; exact_mod_cast hle
  have hS2 : S < 2 * M := by rw [hS]; exact_mod_cast hM
  have hY : (0 : ℤ) ≤ (q : ℤ) ^ (b + c + 2) := by positivity
  have hKpos : 1 ≤ K := by
    by_contra hneg
    have hK1 : K ≤ -1 := by
      rcases lt_or_gt_of_ne hK0 with h | h
      · omega
      · omega
    have hXM : (0 : ℤ) ≤ (q : ℤ) ^ (c + 1) * M := by positivity
    have := mul_le_mul_of_nonneg_left hK1 hXM
    nlinarith
  have hlt : (q : ℤ) ^ (c + 1) * M < (q : ℤ) ^ (c + 1) * ((q : ℤ) ^ (b + 1) * (S - M)) := by
    have hXM : (0 : ℤ) ≤ (q : ℤ) ^ (c + 1) * M := by positivity
    have h1 := mul_le_mul_of_nonneg_left hKpos hXM
    have e : (q : ℤ) ^ (c + 1) * ((q : ℤ) ^ (b + 1) * (S - M)) =
        (q : ℤ) ^ (b + c + 2) * (S - M) := by ring
    rw [e]
    have hS0 : (0 : ℤ) < S := by linarith
    nlinarith
  have hfin := lt_of_mul_lt_mul_left hlt (by positivity)
  zify [hle]
  exact hfin

/-! ## Rank two -/

private theorem succ_le_pow_of_le {P q m : ℕ} (hP : P.Prime) (hq : q.Prime) (hqP : q < P)
    (hle : P ≤ q ^ m) : P + 1 ≤ q ^ m := by
  rcases Nat.lt_or_ge P (q ^ m) with h | h
  · omega
  · exfalso
    have heq : P = q ^ m := le_antisymm hle h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero] at heq
      exact hP.one_lt.ne' heq
    · have hd : q ∣ P := heq ▸ dvd_pow_self q hm.ne'
      have := (Nat.prime_dvd_prime_iff_eq hq hP).mp hd
      omega

private theorem lt_of_pow_le_lt {q w m X : ℕ} (hq : q.Prime) (h1 : q ^ w ≤ X)
    (h2 : X < q ^ m) : w < m :=
  (Nat.pow_lt_pow_iff_right hq.one_lt).mp (lt_of_le_of_lt h1 h2)

/-- Rank two bound on the special exponent. Let `N` be an odd perfect number with special
prime `q` (odd exponent `a = v_q(N)`), let `P > q` be a prime factor such that every other prime
factor is at most `q`, let every prime factor `p < q` have `v_p(N) ≤ D`, and let the rows
`σ(p ^ v_p(N))` of the prime factors `p < q` carry at most `β` at `q` in total. Then with
`e = v_P(N)`, `a ≤ max (β + e D - 1) ((e + 1) β + e - 1)`. Restricted result; novelty not
verified. -/
theorem special_exponent_le_rank_two {N q P D β : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hD : ∀ p ∈ N.primeFactors, p < q → N.factorization p ≤ D)
    (hβ : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ β) :
    N.factorization q ≤ max (β + N.factorization P * D - 1)
      ((N.factorization P + 1) * β + N.factorization P - 1) := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hPq : P ≠ q := by omega
  have hoddN : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  have hq2 : q ≠ 2 := fun h2 => by have := hoddN q hqmem; omega
  have hP2 : P ≠ 2 := fun h2 => by have := hoddN P hP; omega
  set a := N.factorization q with ha
  set e := N.factorization P with he
  set w := sigmaWeight N P q with hw
  -- the exponent of `P` is even and positive
  have he2 : 2 ≤ e := by
    obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hPp hPq
    have : 1 ≤ e := (hPp.dvd_iff_one_le_factorization h.ne_zero).mp
      (Nat.dvd_of_mem_primeFactors hP)
    omega
  -- the ledger at `q`
  have hsum := sigmaWeight_sum_eq h.2 hq hq2
  rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q)] at hsum
  have hrest : ∑ p ∈ N.primeFactors.filter (fun p => ¬ p < q), sigmaWeight N p q ≤ w := by
    have hsub : N.primeFactors.filter (fun p => ¬ p < q) ⊆ {q, P} := by
      intro p hp
      obtain ⟨hp, hpq⟩ := Finset.mem_filter.mp hp
      by_cases hpP : p = P
      · simp [hpP]
      · have := hsecond p hp hpP
        simp [show p = q by omega]
    refine (Finset.sum_le_sum_of_subset hsub).trans ?_
    rw [Finset.sum_pair hPq.symm, sigmaWeight_self hq]
    omega
  have haw : a ≤ β + w := by omega
  have hwa : w ≤ a := by
    have := Finset.single_le_sum (f := fun p => sigmaWeight N p q) (fun _ _ => Nat.zero_le _) hP
    have h2 := sigmaWeight_sum_eq h.2 hq hq2
    omega
  -- `q ^ w` divides `σ(P ^ e)`
  have hσP : σ 1 (P ^ e) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hPp.ne_zero)).ne'
  have hqw : q ^ w ∣ σ 1 (P ^ e) := Nat.ordProj_dvd _ _
  have hqwle : q ^ w ≤ σ 1 (P ^ e) := Nat.le_of_dvd (Nat.pos_of_ne_zero hσP) hqw
  have hσlt := sigma_prime_pow_lt_succ_pow hPp he2
  by_cases hc1 : ∃ u ∈ N.primeFactors, u < q ∧ P ∣ σ 1 (u ^ N.factorization u)
  · -- Case 1: the largest prime divides the row of a smaller prime
    obtain ⟨u, hu, huq, hPu⟩ := hc1
    have hup := Nat.prime_of_mem_primeFactors hu
    set k := N.factorization u with hk
    have hk1 : 1 ≤ k := (hup.dvd_iff_one_le_factorization h.ne_zero).mp
      (Nat.dvd_of_mem_primeFactors hu)
    have hkD : k ≤ D := hD u hu huq
    have h1 : P ≤ σ 1 (u ^ k) :=
      Nat.le_of_dvd (sigma_pos 1 _ (pow_ne_zero _ hup.ne_zero)) hPu
    have h2 := sigma_prime_pow_le_succ_pow hup k
    have h3 : (u + 1) ^ k ≤ q ^ k := Nat.pow_le_pow_left (by omega) k
    have h4 : q ^ k ≤ q ^ D := Nat.pow_le_pow_right hq.pos hkD
    have hPD : P + 1 ≤ q ^ D := succ_le_pow_of_le hPp hq hqP (by omega)
    have h5 : (P + 1) ^ e ≤ q ^ (D * e) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left hPD e
    have hwlt : w < D * e := lt_of_pow_le_lt hq hqwle (lt_of_lt_of_le hσlt h5)
    have : D * e = e * D := Nat.mul_comm _ _
    exact le_max_of_le_left (by omega)
  · -- Case 2: all of `v_P(N)` comes from the special row
    push Not at hc1
    have hsumP := sigmaWeight_sum_eq h.2 hPp hP2
    rw [Finset.sum_eq_single q] at hsumP
    · have hPe : P ^ e ∣ σ 1 (q ^ a) := by
        have := Nat.ordProj_dvd (σ 1 (q ^ a)) P
        unfold sigmaWeight at hsumP
        rwa [hsumP] at this
      have hcop : Nat.Coprime (q ^ w) (P ^ e) :=
        ((Nat.coprime_primes hq hPp).mpr hPq.symm).pow w e
      have hdvd : q ^ w * P ^ e ∣ σ 1 (q ^ a) * σ 1 (P ^ e) := by
        rw [mul_comm (σ 1 (q ^ a))]
        exact mul_dvd_mul hqw hPe
      rcases Nat.eq_zero_or_pos w with hw0 | hw0
      · have : β ≤ (e + 1) * β := Nat.le_mul_of_pos_left β (show 0 < e + 1 by omega)
        exact le_max_of_le_right (by omega)
      · set b := a - w with hb
        have hgap := lt_pow_mul_sigma_sub (M := P ^ e) (a := a) (b := b) hq hq2
          (sigma_prime_pow_lt_two_mul' hPp e) (by omega)
          (by rw [show a - b = w by omega]; exact hdvd)
        set Q := q ^ (b + 1) with hQ
        have hge : P ^ e ≤ σ 1 (P ^ e) := le_sigma_one (pow_ne_zero _ hPp.ne_zero)
        have hg := sigma_prime_pow_mul_sub_one (k := e) hPp
        have hPQ : P - 1 < Q := by
          have h3 : (3 : ℤ) ≤ P := by
            have := hPp.two_le
            have : 3 ≤ P := by omega
            exact_mod_cast this
          have hgap' :
              ((P ^ e : ℕ) : ℤ) < (Q : ℤ) * ((σ 1 (P ^ e) : ℕ) - (P ^ e : ℕ)) := by
            have := hgap
            zify [hge] at this
            exact this
          have hPe0 : (0 : ℤ) < ((P ^ e : ℕ) : ℤ) := by exact_mod_cast pow_pos hPp.pos e
          have hD : (((σ 1 (P ^ e) : ℕ) : ℤ) - (P ^ e : ℕ)) * ((P : ℤ) - 1) =
              ((P ^ e : ℕ) : ℤ) - 1 := by
            push_cast at hg ⊢
            rw [pow_succ] at hg
            linear_combination hg
          have hQ0 : (0 : ℤ) ≤ Q := by positivity
          by_contra hcon
          have hQle : (Q : ℤ) ≤ (P : ℤ) - 1 := by
            have : Q ≤ P - 1 := by omega
            have h1 : 1 ≤ P := hPp.one_lt.le
            zify [h1] at this
            exact this
          have hA := mul_lt_mul_of_pos_right hgap' (show (0 : ℤ) < (P : ℤ) - 1 by linarith)
          rw [mul_assoc, hD] at hA
          nlinarith
        have hPQ' : P + 1 ≤ q ^ (b + 1) := succ_le_pow_of_le hPp hq hqP (by omega)
        have h5 : (P + 1) ^ e ≤ q ^ ((b + 1) * e) := by
          rw [pow_mul]
          exact Nat.pow_le_pow_left hPQ' e
        have hwlt : w < (b + 1) * e := lt_of_pow_le_lt hq hqwle (lt_of_lt_of_le hσlt h5)
        have hbβ : b ≤ β := by omega
        have h6 : (b + 1) * e ≤ (β + 1) * e := Nat.mul_le_mul_right e (by omega)
        have h7 : (e + 1) * β + e = (β + 1) * e + β := by ring
        exact le_max_of_le_right (by omega)
    · intro p hp hpq
      by_cases hpP : p = P
      · rw [hpP]; exact sigmaWeight_self hPp
      · have hpq' : p < q := by have := hsecond p hp hpP; omega
        exact Nat.factorization_eq_zero_of_not_dvd (hc1 p hp hpq')
    · intro hq'
      exact absurd hqmem hq'

end OddPerfect

#print axioms OddPerfect.sigma_prime_pow_le_succ_pow
#print axioms OddPerfect.sigma_prime_pow_lt_succ_pow
#print axioms OddPerfect.lt_pow_mul_sigma_sub
#print axioms OddPerfect.special_exponent_le_rank_two
