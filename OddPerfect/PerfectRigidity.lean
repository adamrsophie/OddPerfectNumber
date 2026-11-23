import OddPerfect.Basic

/-!
# Rigidity of perfect numbers

A proper nontrivial unitary divisor of a perfect number has a divisor sum strictly between
itself and twice itself. This forces a prime into its cofactor. Two perfect numbers with a
common prime and equal exponents at all common primes must coincide.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma BigOperators

/-- The divisor sum of a natural number greater than one exceeds the number. -/
private theorem rigidity_lt_sigma_one {n : ℕ} (hn : 1 < n) : n < σ 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have hmem := Nat.one_mem_properDivisors_iff_one_lt.mpr hn
  have hsum : 1 ≤ ∑ i ∈ n.properDivisors, i :=
    Finset.single_le_sum (fun (i : ℕ) (_ : i ∈ n.properDivisors) => Nat.zero_le i) hmem
  omega

/-- The divisor sums of a unitary divisor of a perfect number and its cofactor multiply to
twice their product. -/
private theorem rigidity_sigma_mul_cofactor {N B : ℕ} (hN : σ 1 N = 2 * N)
    (hB : B ∣ N) (hcop : Nat.Coprime B (N / B)) :
    σ 1 B * σ 1 (N / B) = (2 * B) * (N / B) := by
  calc
    σ 1 B * σ 1 (N / B) = σ 1 (B * (N / B)) :=
      ((isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop).symm
    _ = σ 1 N := by rw [Nat.mul_div_cancel' hB]
    _ = 2 * N := hN
    _ = (2 * B) * (N / B) := by rw [Nat.mul_assoc, Nat.mul_div_cancel' hB]

/-- Let `B` be a unitary divisor of a perfect number `N` with `1 < B < N`. Then `σ(B)` lies
strictly between `B` and `2 B`. -/
theorem sigma_unitary_divisor_bounds {N B : ℕ} (hN : σ 1 N = 2 * N) (hB : B ∣ N)
    (hcop : Nat.Coprime B (N / B)) (h1 : 1 < B) (hlt : B < N) :
    B < σ 1 B ∧ σ 1 B < 2 * B := by
  have hC : 1 < N / B := by
    by_contra hnot
    have hle : N / B ≤ 1 := by omega
    have hm := Nat.mul_le_mul_left B hle
    rw [Nat.mul_div_cancel' hB, Nat.mul_one] at hm
    exact (not_le_of_gt hlt) hm
  have hlow := rigidity_lt_sigma_one h1
  have hsig : 0 < σ 1 B := by omega
  refine ⟨hlow, Nat.lt_of_mul_lt_mul_right (a := N / B) ?_⟩
  calc
    σ 1 B * (N / B) < σ 1 B * σ 1 (N / B) :=
      Nat.mul_lt_mul_of_pos_left (rigidity_lt_sigma_one hC) hsig
    _ = (2 * B) * (N / B) := rigidity_sigma_mul_cofactor hN hB hcop

/-- Forced prime. Let `B` be a unitary divisor of a perfect number `N` with `1 < B < N`. Some
prime `r` divides `σ(B)` to a higher power than it divides `2 B`. -/
theorem exists_forced_prime {N B : ℕ} (hN : σ 1 N = 2 * N) (hB : B ∣ N)
    (hcop : Nat.Coprime B (N / B)) (h1 : 1 < B) (hlt : B < N) :
    ∃ r, r.Prime ∧ (2 * B).factorization r < (σ 1 B).factorization r := by
  obtain ⟨hlow, hupp⟩ := sigma_unitary_divisor_bounds hN hB hcop h1 hlt
  have hsig0 : σ 1 B ≠ 0 := by omega
  have htwoB0 : 2 * B ≠ 0 := by omega
  by_contra hnone
  have hle : ∀ r : ℕ, r.Prime → (σ 1 B).factorization r ≤ (2 * B).factorization r := by
    intro r hr
    exact le_of_not_gt (fun hgt => hnone ⟨r, hr, hgt⟩)
  obtain ⟨k, hk⟩ := (Nat.factorization_prime_le_iff_dvd hsig0 htwoB0).mp hle
  have hk2 : 2 ≤ k := by
    by_contra hsmall
    have hk1 : k ≤ 1 := by omega
    have hm := Nat.mul_le_mul_left (σ 1 B) hk1
    rw [← hk, Nat.mul_one] at hm
    exact (not_le_of_gt hupp) hm
  have hm := Nat.mul_le_mul_left (σ 1 B) hk2
  rw [← hk, Nat.mul_comm (σ 1 B) 2] at hm
  omega

/-- Every forced prime divides the cofactor `N / B`. -/
theorem forced_prime_dvd_cofactor {N B r : ℕ} (hN : σ 1 N = 2 * N) (hB : B ∣ N)
    (hcop : Nat.Coprime B (N / B)) (h1 : 1 < B) (hr : r.Prime)
    (h : (2 * B).factorization r < (σ 1 B).factorization r) : r ∣ N / B := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [Nat.zero_div, Nat.coprime_zero_right] at hcop
    omega
  have hB0 : B ≠ 0 := by omega
  have hC0 : N / B ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hB) (Nat.pos_of_ne_zero hB0)).ne'
  have hsig0 : σ 1 B ≠ 0 := (sigma_pos 1 B hB0).ne'
  have htwoB0 : 2 * B ≠ 0 := by omega
  have hdvd : σ 1 B ∣ (2 * B) * (N / B) := by
    rw [← rigidity_sigma_mul_cofactor hN hB hcop]
    exact dvd_mul_right _ _
  have hle := (Nat.factorization_le_iff_dvd hsig0 (mul_ne_zero htwoB0 hC0)).mpr hdvd r
  rw [Nat.factorization_mul htwoB0 hC0, Finsupp.add_apply] at hle
  apply (hr.dvd_iff_one_le_factorization hC0).mpr
  omega

/-- Rigidity. Two perfect numbers that have a common prime factor and the same exponent at
every common prime factor are equal. -/
theorem perfect_eq_of_factorization_eq_on_common {N N' : ℕ} (hN : σ 1 N = 2 * N)
    (hN' : σ 1 N' = 2 * N') (hN0 : N ≠ 0) (hN0' : N' ≠ 0)
    (hc : ∃ p, p.Prime ∧ p ∣ N ∧ p ∣ N')
    (h : ∀ p, p.Prime → p ∣ N → p ∣ N' → N.factorization p = N'.factorization p) :
    N = N' := by
  let B := Nat.gcd N N'
  have hBN : B ∣ N := Nat.gcd_dvd_left N N'
  have hBN' : B ∣ N' := Nat.gcd_dvd_right N N'
  have hle : B ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hBN
  have hle' : B ≤ N' := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0') hBN'
  have hB0 : B ≠ 0 := by
    intro hzero
    rw [hzero, zero_dvd_iff] at hBN
    exact hN0 hBN
  obtain ⟨p, hp, hpN, hpN'⟩ := hc
  have hB1 : 1 < B :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hB0) (Nat.dvd_gcd hpN hpN'))
  have hexp (q : ℕ) (hq : q.Prime) (hqB : q ∣ B) :
      B.factorization q = N.factorization q := by
    have he := h q hq (hqB.trans hBN) (hqB.trans hBN')
    change (Nat.gcd N N').factorization q = N.factorization q
    rw [Nat.factorization_gcd hN0 hN0', Finsupp.inf_apply, ← he, inf_idem]
  have hunitary (M : ℕ) (hM0 : M ≠ 0) (hBM : B ∣ M)
      (hfac : ∀ q : ℕ, q.Prime → q ∣ B → B.factorization q = M.factorization q) :
      Nat.Coprime B (M / B) := by
    by_contra hnot
    obtain ⟨q, hq, hqB, hqC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hC0 : M / B ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hBM) (Nat.pos_of_ne_zero hB0)).ne'
    have hpos := hq.factorization_pos_of_dvd hC0 hqC
    rw [Nat.factorization_div hBM, Finsupp.tsub_apply, hfac q hq hqB] at hpos
    omega
  have hcop := hunitary N hN0 hBN hexp
  have hcop' := hunitary N' hN0' hBN' fun q hq hqB =>
    (hexp q hq hqB).trans (h q hq (hqB.trans hBN) (hqB.trans hBN'))
  by_cases hEq : B = N
  · by_contra hne
    have hlt' : B < N' := lt_of_le_of_ne hle' (fun he => hne (hEq.symm.trans he))
    have hupp := (sigma_unitary_divisor_bounds hN' hBN' hcop' hB1 hlt').2
    rw [hEq, hN] at hupp
    exact (lt_irrefl _) hupp
  have hlt : B < N := lt_of_le_of_ne hle hEq
  by_cases hEq' : B = N'
  · have hupp := (sigma_unitary_divisor_bounds hN hBN hcop hB1 hlt).2
    rw [hEq', hN'] at hupp
    exact False.elim ((lt_irrefl _) hupp)
  have hlt' : B < N' := lt_of_le_of_ne hle' hEq'
  obtain ⟨r, hr, hforced⟩ := exists_forced_prime hN hBN hcop hB1 hlt
  have hrC := forced_prime_dvd_cofactor hN hBN hcop hB1 hr hforced
  have hrC' := forced_prime_dvd_cofactor hN' hBN' hcop' hB1 hr hforced
  have hrB : r ∣ B :=
    Nat.dvd_gcd (hrC.trans (Nat.div_dvd_of_dvd hBN)) (hrC'.trans (Nat.div_dvd_of_dvd hBN'))
  exact False.elim ((Nat.not_coprime_of_dvd_of_dvd hr.one_lt hrB hrC) hcop)

end OddPerfect

#print axioms OddPerfect.sigma_unitary_divisor_bounds
#print axioms OddPerfect.exists_forced_prime
#print axioms OddPerfect.forced_prime_dvd_cofactor
#print axioms OddPerfect.perfect_eq_of_factorization_eq_on_common
