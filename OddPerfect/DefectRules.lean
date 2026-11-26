import OddPerfect.ZeroDefect
import OddPerfect.EscapeRowUnique
import OddPerfect.Abundancy

/-!
# Rule lemmas for a case split on the support defect

Let `N` be an odd perfect number with special prime `q` and support defect
`Z = supportDefect N q` (`ExcessDefect`). This file collects, in a shape that a later certificate
checker can apply one node at a time, the rules that a finite case split on `Z ≤ K` uses:

* forced primes: an odd prime dividing `σ(p ^ v_p(N))` divides `N`
  (`mem_primeFactors_of_dvd_sigma_component`), also through `q + 1` for the special prime
  (`mem_primeFactors_of_dvd_succ_special`), with exponent lower bounds for the weights
  (`le_sigmaWeight_of_pow_dvd`, `le_sigmaWeight_special_of_pow_dvd`);
* capacity: distinct sources send at most `v_r(N)` to an odd prime `r`
  (`sum_sigmaWeight_le_factorization`);
* receivers: weights to a set of ordinary receivers bound `recvWeight` from below
  (`sum_sigmaWeight_le_recvWeight`);
* the master inequality: the costs of known ordinary primes and their receiver weights are at
  most `Z` (`defect_lower_bound`);
* abundancy: a product of prime powers below the exact powers divides `N`
  (`prod_pow_dvd_of_le_factorization`), so `σ(D) ≤ 2 * D` for it (`sigma_le_two_mul_of_dvd`,
  in product form `prod_geom_sum_le_two_mul_prod`).

As a test, two roots of the case split for `Z ≤ 2` are proved by hand:
`v_3(N) ≠ 4` and `v_3(N) ≠ 8`.

This module proves no bound for all odd perfect numbers by itself. The total excess is not
bounded, and the odd perfect number conjecture is open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem sigma_prime_pow_ne_zero {p e : ℕ} (hp : p.Prime) : σ 1 (p ^ e) ≠ 0 :=
  (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'

/-! ### Forced primes and weights -/

/-- Rule 1: an odd prime dividing the divisor sum of a full prime power component of `N` is a
prime factor of `N`. -/
theorem mem_primeFactors_of_dvd_sigma_component {N p r : ℕ} (h : OddPerfect N)
    (hp : p ∈ N.primeFactors) (hr : r.Prime) (hr2 : r ≠ 2)
    (hd : r ∣ σ 1 (p ^ N.factorization p)) : r ∈ N.primeFactors := by
  have hw : 1 ≤ sigmaWeight N p r :=
    hr.factorization_pos_of_dvd (sigma_prime_pow_ne_zero (Nat.prime_of_mem_primeFactors hp)) hd
  exact mem_primeFactors_of_sigmaWeight_ne_zero h.perfect hp hr2 (by omega)

/-- A lower bound for a weight from a prime power dividing the row. -/
theorem le_sigmaWeight_of_pow_dvd {N p r k : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hd : r ^ k ∣ σ 1 (p ^ N.factorization p)) : k ≤ sigmaWeight N p r :=
  (hr.pow_dvd_iff_le_factorization (sigma_prime_pow_ne_zero hp)).mp hd

/-- Rule 1 for the special prime, through `q + 1`. -/
theorem mem_primeFactors_of_dvd_succ_special {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hr2 : r ≠ 2) (hd : r ∣ q + 1) :
    r ∈ N.primeFactors := by
  have hq0 : N.factorization q ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos hq0, h.ne_zero⟩
  exact mem_primeFactors_of_dvd_sigma_component h hqN hr hr2
    (hd.trans (succ_dvd_sigma_special hq hodd))

/-- The weight of the special prime at `r` is at least the exponent of a power of `r` dividing
`q + 1`. -/
theorem le_sigmaWeight_special_of_pow_dvd {N q r k : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hd : r ^ k ∣ q + 1) :
    k ≤ sigmaWeight N q r :=
  le_sigmaWeight_of_pow_dvd hq hr (hd.trans (succ_dvd_sigma_special hq hodd))

/-! ### Capacity and receivers -/

/-- Rule 2: distinct sources send at most `v_r(N)` to an odd prime `r`. -/
theorem sum_sigmaWeight_le_factorization {N r : ℕ} (h : OddPerfect N) (hr : r.Prime)
    (hr2 : r ≠ 2) {S : Finset ℕ} (hS : S ⊆ N.primeFactors) :
    ∑ p ∈ S, sigmaWeight N p r ≤ N.factorization r := by
  rw [← sigmaWeight_sum_eq h.perfect hr hr2]
  exact Finset.sum_le_sum_of_subset hS

/-- Rule 4, receiver side: the weights from `p` to a set of ordinary receivers bound
`recvWeight N q p` from below. -/
theorem sum_sigmaWeight_le_recvWeight {N q p : ℕ} {R : Finset ℕ} (hR : R ⊆ ordReceivers N q) :
    ∑ r ∈ R, sigmaWeight N p r ≤ recvWeight N q p :=
  Finset.sum_le_sum_of_subset hR

/-! ### The master inequality -/

/-- Rules 3 and 4 together. `S₂` are known square primes and `S₄` known ordinary primes of
exponent at least 4 (the prime 3 may be in either, according to `v_3(N)`). The left side
collects the costs of the exponents, the receiver weights and the term for `3 ∤ N`. The escape
rows inside `S₂` contribute 0, since they send no weight to the receivers. -/
theorem defect_lower_bound {N q : ℕ} {S₂ S₄ : Finset ℕ} (h₂ : S₂ ⊆ squarePrimes N q)
    (h₄ : S₄ ⊆ highPrimes N q) :
    threeExcessDefect N
      + ∑ p ∈ S₄.filter (fun p => p ≠ 3), 3 * (N.factorization p / 2 - 2)
      + ∑ p ∈ S₄.filter (fun p => p % 3 = 2), N.factorization p
      + 2 * ∑ p ∈ S₄, sigmaWeight N p 3
      + ∑ p ∈ S₂, (recvWeight N q p - 1)
      + ∑ p ∈ S₄, recvWeight N q p + recvWeight N q q
      + (if 3 ∣ N then 0 else 4) ≤ supportDefect N q := by
  have hA : ∑ p ∈ S₄.filter (fun p => p ≠ 3), 3 * (N.factorization p / 2 - 2) ≤
      3 * highExcessDefect N q := by
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ h₄))
  have hB : ∑ p ∈ S₄.filter (fun p => p % 3 = 2), N.factorization p ≤ twoModThreeMass N q :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ h₄)
  have hC : ∑ p ∈ S₄, sigmaWeight N p 3 ≤ highThreeWeight N q :=
    Finset.sum_le_sum_of_subset h₄
  have hD : ∑ p ∈ S₂, (recvWeight N q p - 1) ≤ squareSurplus N q := by
    refine Finset.sum_le_sum_of_ne_zero fun p hp hne => Finset.mem_sdiff.mpr ⟨h₂ hp, ?_⟩
    intro hE
    rw [recvWeight_eq_zero_of_mem_escapeRows hE] at hne
    exact hne rfl
  have hE : ∑ p ∈ S₄, recvWeight N q p + recvWeight N q q ≤ highRecvWeight N q := by
    have hq : q ∉ highPrimes N q := by simp [highPrimes]
    unfold highRecvWeight
    rw [Finset.sum_insert hq]
    have := Finset.sum_le_sum_of_subset (f := recvWeight N q) h₄
    omega
  unfold supportDefect
  omega

/-! ### Abundancy -/

/-- Rule 5: a divisor `D` of an odd perfect number has `σ(D) ≤ 2 * D`. -/
theorem sigma_le_two_mul_of_dvd {N D : ℕ} (h : OddPerfect N) (hD : D ∣ N) : σ 1 D ≤ 2 * D := by
  have hD0 : D ≠ 0 := by rintro rfl; exact h.ne_zero (zero_dvd_iff.mp hD)
  have hle := abundancy_le_of_dvd h.ne_zero hD
  rw [(perfect_iff_abundancy_eq_two (Nat.pos_of_ne_zero h.ne_zero)).mp h.perfect] at hle
  unfold abundancy at hle
  have hpos : (0 : ℚ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD0
  rw [div_le_iff₀ hpos] at hle
  exact_mod_cast hle

/-- Rule 5, building the divisor: a product of prime powers below the exact powers divides
`N`. -/
theorem prod_pow_dvd_of_le_factorization {N : ℕ} (hN : N ≠ 0) {S : Finset ℕ} {f : ℕ → ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hf : ∀ p ∈ S, f p ≤ N.factorization p) : ∏ p ∈ S, p ^ f p ∣ N := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hsa : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hfa : ∀ p ∈ s, f p ≤ N.factorization p := fun p hp => hf p (Finset.mem_insert_of_mem hp)
    have hap := hS a (Finset.mem_insert_self a s)
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ (ih hsa hfa)
    · exact Nat.Coprime.prod_right fun p hp => Nat.coprime_pow_primes _ _ hap (hsa p hp)
        (fun e => ha (e ▸ hp))
    · exact (hap.pow_dvd_iff_le_factorization hN).mpr (hf a (Finset.mem_insert_self a s))

/-- Rule 5 in product form, with each `σ(p ^ f)` written as a geometric sum: for distinct primes
`p ∈ S` with `f p ≤ v_p(N)`, `∏ (1 + p + ... + p ^ f p) ≤ 2 * ∏ p ^ f p`. -/
theorem prod_geom_sum_le_two_mul_prod {N : ℕ} (h : OddPerfect N) {S : Finset ℕ} {f : ℕ → ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hf : ∀ p ∈ S, f p ≤ N.factorization p) :
    ∏ p ∈ S, ∑ i ∈ Finset.range (f p + 1), p ^ i ≤ 2 * ∏ p ∈ S, p ^ f p := by
  have hle := sigma_le_two_mul_of_dvd h (prod_pow_dvd_of_le_factorization h.ne_zero hS hf)
  have hcop : (S : Set ℕ).Pairwise (Function.onFun Nat.Coprime fun p => p ^ f p) :=
    fun a ha b hb hab => Nat.coprime_pow_primes _ _ (hS a ha) (hS b hb) hab
  rw [isMultiplicative_sigma.map_prod (fun p => p ^ f p) S hcop] at hle
  calc ∏ p ∈ S, ∑ i ∈ Finset.range (f p + 1), p ^ i = ∏ p ∈ S, σ 1 (p ^ f p) :=
        Finset.prod_congr rfl fun p hp => (sigma_one_apply_prime_pow (hS p hp)).symm
    _ ≤ 2 * ∏ p ∈ S, p ^ f p := hle

/-! ### Two roots of the case split for `Z ≤ 2` -/

private theorem two_le_of_ne {N q p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hp : p ∈ N.primeFactors) (hpq : p ≠ q) :
    2 ≤ N.factorization p := by
  obtain ⟨j, hj, hpos⟩ := even_pos_factorization_of_ne h hq hodd hp hpq
  omega

/-- `v_3(N) = 4` is impossible when the support defect is at most 2. -/
theorem factorization_three_ne_four_of_supportDefect_le_two {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hZ : supportDefect N q ≤ 2) :
    N.factorization 3 ≠ 4 := by
  intro hb
  have hq4 := (special_mod_four h hq hodd).1
  have h3P : 3 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega),
      h.ne_zero⟩
  -- `σ(3 ^ 4) = 11 ^ 2`
  have h11 : 11 ∈ N.primeFactors := mem_primeFactors_of_dvd_sigma_component h h3P
    (by norm_num) (by norm_num)
    (by rw [hb, sigma_one_apply_prime_pow Nat.prime_three]; decide)
  have hq11 : (11 : ℕ) ≠ q := by omega
  -- an exponent at least 4 at 11 costs at least 4, since `11 % 3 = 2`
  have e11 : N.factorization 11 = 2 := by
    have h2 := two_le_of_ne h hq hodd h11 hq11
    obtain ⟨j, hj, -⟩ := even_pos_factorization_of_ne h hq hodd h11 hq11
    by_contra hne
    have hX : 11 ∈ highPrimes N q :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hq11, h11⟩, by omega⟩
    have hm := defect_lower_bound (N := N) (q := q) (S₂ := ∅) (S₄ := {11})
      (Finset.empty_subset _) (Finset.singleton_subset_iff.mpr hX)
    simp only [Finset.filter_singleton, Finset.sum_singleton, Finset.sum_empty] at hm
    norm_num at hm hj hne h2
    omega
  -- `σ(11 ^ 2) = 7 * 19`
  have hσ11 : σ 1 (11 ^ N.factorization 11) = 133 := by
    rw [e11, sigma_one_apply_prime_pow (by norm_num)]; decide
  have h7 : 7 ∈ N.primeFactors := mem_primeFactors_of_dvd_sigma_component h h11
    (by norm_num) (by norm_num) (by rw [hσ11]; norm_num)
  have h19 : 19 ∈ N.primeFactors := mem_primeFactors_of_dvd_sigma_component h h11
    (by norm_num) (by norm_num) (by rw [hσ11]; norm_num)
  have e7 := two_le_of_ne h hq hodd h7 (by omega)
  have e19 := two_le_of_ne h hq hodd h19 (by omega)
  -- `D = 3 ^ 4 * 11 ^ 2 * 7 ^ 2 * 19 ^ 2` has `σ(D) / D = 127 / 63 > 2`
  have hle := prod_geom_sum_le_two_mul_prod h (S := {3, 11, 7, 19})
    (f := fun p => if p = 3 then 4 else 2)
    (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num)
    (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> simp <;> omega)
  exact absurd hle (by decide +kernel)

private theorem receiver_absurd {N q r : ℕ} (hZ : supportDefect N q ≤ 2)
    (hb : N.factorization 3 = 8)
    (h3 : 3 ∣ N) (h3X : 3 ∈ highPrimes N q) (hr : r ∈ N.primeFactors) (hrq : r ≠ q)
    (hr3 : r ≠ 3) (hr1 : r % 3 = 1) (hd : r ∣ σ 1 (3 ^ N.factorization 3)) : False := by
  have hR : r ∈ ordReceivers N q := Finset.mem_filter.mpr ⟨hr, hrq, hr3, hr1⟩
  have hw := le_sigmaWeight_of_pow_dvd (k := 1) Nat.prime_three (Nat.prime_of_mem_primeFactors hr)
    (by rw [pow_one]; exact hd)
  have hrw := sum_sigmaWeight_le_recvWeight (N := N) (p := 3) (Finset.singleton_subset_iff.mpr hR)
  rw [Finset.sum_singleton] at hrw
  have hm := defect_lower_bound (N := N) (q := q) (S₂ := ∅) (S₄ := {3})
    (Finset.empty_subset _) (Finset.singleton_subset_iff.mpr h3X)
  simp only [Finset.sum_singleton, Finset.sum_empty, if_pos h3] at hm
  unfold threeExcessDefect at hm
  rw [hb] at hm
  omega

/-- `v_3(N) = 8` is impossible when the support defect is at most 2. -/
theorem factorization_three_ne_eight_of_supportDefect_le_two {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hZ : supportDefect N q ≤ 2) :
    N.factorization 3 ≠ 8 := by
  intro hb
  have hq4 := (special_mod_four h hq hodd).1
  have h3 : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have h3P : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have h3X : 3 ∈ highPrimes N q :=
    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by omega, h3P⟩, by omega⟩
  -- `σ(3 ^ 8) = 13 * 757`
  have hσ : σ 1 (3 ^ N.factorization 3) = 9841 := by
    rw [hb, sigma_one_apply_prime_pow Nat.prime_three]; decide
  have h13 : 13 ∣ σ 1 (3 ^ N.factorization 3) := by rw [hσ]; norm_num
  have h757 : 757 ∣ σ 1 (3 ^ N.factorization 3) := by rw [hσ]; norm_num
  have hP13 := mem_primeFactors_of_dvd_sigma_component h h3P (by norm_num) (by norm_num) h13
  have hP757 := mem_primeFactors_of_dvd_sigma_component h h3P (by norm_num) (by norm_num) h757
  by_cases hq13 : q = 13
  · exact receiver_absurd hZ hb h3 h3X hP757 (by omega) (by norm_num) (by norm_num)
      h757
  · exact receiver_absurd hZ hb h3 h3X hP13 (Ne.symm hq13) (by norm_num) (by norm_num)
      h13

end OddPerfect

#print axioms OddPerfect.mem_primeFactors_of_dvd_sigma_component
#print axioms OddPerfect.le_sigmaWeight_of_pow_dvd
#print axioms OddPerfect.mem_primeFactors_of_dvd_succ_special
#print axioms OddPerfect.le_sigmaWeight_special_of_pow_dvd
#print axioms OddPerfect.sum_sigmaWeight_le_factorization
#print axioms OddPerfect.sum_sigmaWeight_le_recvWeight
#print axioms OddPerfect.defect_lower_bound
#print axioms OddPerfect.sigma_le_two_mul_of_dvd
#print axioms OddPerfect.prod_pow_dvd_of_le_factorization
#print axioms OddPerfect.prod_geom_sum_le_two_mul_prod
#print axioms OddPerfect.factorization_three_ne_four_of_supportDefect_le_two
#print axioms OddPerfect.factorization_three_ne_eight_of_supportDefect_le_two
