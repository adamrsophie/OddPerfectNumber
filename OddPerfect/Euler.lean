import OddPerfect.Basic

/-!
# Euler's form of an odd perfect number

Every odd perfect number has the form `q ^ k * m ^ 2` with `q` prime, `q ∤ m`, and
`q ≡ k ≡ 1 (mod 4)`. Consequences: `N ≡ 1 (mod 4)`, `N` is not a square, primes
`p ≡ 3 (mod 4)` divide `N` to an even power, and Touchard's congruence.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

/-- A geometric sum with ratio `≡ 1 (mod n)` is `≡ (e + 1) (mod n)`. -/
private lemma geom_mod {p n : ℕ} (e : ℕ) (h : p % n = 1) :
    (∑ i ∈ Finset.range (e + 1), p ^ i) % n = (e + 1) % n := by
  rw [Finset.sum_nat_mod]
  have h1 : 1 % n = 1 := by rw [← h, Nat.mod_mod]
  simp [Nat.pow_mod, h, h1]

/-- Pairing consecutive terms: if `n ∣ q + 1` and `k` is odd then `n` divides the sum. -/
private lemma dvd_geom_of_odd {q n k : ℕ} (hn : n ∣ q + 1) (hk : Odd k) :
    n ∣ ∑ i ∈ Finset.range (k + 1), q ^ i := by
  obtain ⟨j, rfl⟩ := hk
  induction j with
  | zero => simpa [Finset.sum_range_succ, add_comm] using hn
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 + 1 = 2 * j + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, add_assoc]
    refine dvd_add ih ?_
    rw [show q ^ (2 * j + 1 + 1) + q ^ (2 * j + 1 + 1 + 1) = q ^ (2 * j + 2) * (q + 1) by ring]
    exact dvd_mul_of_dvd_right hn _

/-- The core fact: exactly one prime has odd exponent, and its component sum has
`2`-adic valuation exactly one. -/
private lemma core (h : OddPerfect N) : ∃ q, q.Prime ∧ q ∣ N ∧
    2 ∣ σ 1 (q ^ N.factorization q) ∧ ¬ 4 ∣ σ 1 (q ^ N.factorization q) ∧
    ∀ p, p.Prime → p ≠ q → Even (N.factorization p) := by
  set f : ℕ → ℕ := fun p => (σ 1 (p ^ N.factorization p)).factorization 2 with hf
  have hbal := OPNStarter.valuation_balance h.perfect 2
  rw [Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd h.not_two_dvd] at hbal
  have hsum : ∑ p ∈ N.primeFactors, f p = 1 := hbal.symm
  have hne (p : ℕ) (hp : p.Prime) : σ 1 (p ^ N.factorization p) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'
  -- `f p ≥ 1` exactly when the component sum is even
  have hf1 (p : ℕ) (hp : p.Prime) : 1 ≤ f p ↔ 2 ∣ σ 1 (p ^ N.factorization p) := by
    simpa using (Nat.prime_two.pow_dvd_iff_le_factorization (hne p hp) (k := 1)).symm
  -- parity of a component sum for an odd prime
  have hpar (p : ℕ) (hp : p ∈ N.primeFactors) :
      2 ∣ σ 1 (p ^ N.factorization p) ↔ Odd (N.factorization p) := by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hodd : p % 2 = 1 := Nat.odd_iff.mp
      (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
    rw [sigma_one_apply_prime_pow hpp, Nat.dvd_iff_mod_eq_zero, geom_mod _ hodd, Nat.odd_iff]
    omega
  obtain ⟨q, hq, hq0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hle : f q ≤ 1 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hq
  refine ⟨q, hqp, Nat.dvd_of_mem_primeFactors hq, (hf1 q hqp).mp (by omega), ?_, ?_⟩
  · intro h4
    have := (Nat.prime_two.pow_dvd_iff_le_factorization (hne q hqp) (k := 2)).mp
      (by simpa using h4)
    change 2 ≤ f q at this
    omega
  · intro p hp hpq
    by_cases hpN : p ∈ N.primeFactors
    · rw [← Nat.not_odd_iff_even, ← hpar p hpN, ← hf1 p hp]
      intro h1
      have h2 : ∑ x ∈ {p, q}, f x ≤ ∑ x ∈ N.primeFactors, f x :=
        Finset.sum_le_sum_of_subset (by simp [Finset.insert_subset_iff, hpN, hq])
      rw [Finset.sum_pair hpq, hsum] at h2
      omega
    · rw [Finsupp.notMem_support_iff.mp hpN]
      exact ⟨0, rfl⟩

/-- Euler: an odd perfect number has a unique prime `q` of odd exponent, and
`q ≡ 1 (mod 4)` and its exponent is `≡ 1 (mod 4)`. -/
theorem exists_special_prime (h : OddPerfect N) :
    ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      ∀ p : ℕ, p.Prime → p ≠ q → Even (N.factorization p) := by
  obtain ⟨q, hq, hqN, h2, h4, hev⟩ := core h
  set e := N.factorization q
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (h.odd.of_dvd_nat hqN)
  rw [sigma_one_apply_prime_pow hq] at h2 h4
  have he : Odd e := by
    rw [Nat.dvd_iff_mod_eq_zero, geom_mod _ hodd] at h2
    exact Nat.odd_iff.mpr (by omega)
  have hq4 : q % 4 = 1 := by
    by_contra hne
    exact h4 (dvd_geom_of_odd (by omega) he)
  rw [Nat.dvd_iff_mod_eq_zero, geom_mod _ hq4] at h4
  rw [Nat.dvd_iff_mod_eq_zero, geom_mod _ hodd] at h2
  exact ⟨q, hq, hqN, hq4, by omega, hev⟩

/-- An odd perfect number has exactly one prime with odd exponent. -/
theorem existsUnique_odd_exponent (h : OddPerfect N) :
    ∃! q : ℕ, q.Prime ∧ Odd (N.factorization q) := by
  obtain ⟨q, hq, -, -, he, hev⟩ := exists_special_prime h
  refine ⟨q, ⟨hq, Nat.odd_iff.mpr (by omega)⟩, fun p ⟨hp, hpo⟩ => ?_⟩
  by_contra hpq
  exact (Nat.not_even_iff_odd.mpr hpo) (hev p hp hpq)

/-- Euler form: `N = q ^ k * m ^ 2` with `q` prime, `q ∤ m`, and `q ≡ k ≡ 1 (mod 4)`. -/
theorem exists_euler_form (h : OddPerfect N) :
    ∃ q k m : ℕ, q.Prime ∧ N = q ^ k * m ^ 2 ∧ ¬ q ∣ m ∧ q % 4 = 1 ∧ k % 4 = 1 := by
  obtain ⟨q, hq, -, hq4, hk, hev⟩ := exists_special_prime h
  set M := ordCompl[q] N
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos q h.ne_zero).ne'
  have hMf : M.factorization = N.factorization.erase q := Nat.factorization_ordCompl N q
  set m := M.factorization.prod fun p e => p ^ (e / 2)
  have hm : m ^ 2 = M := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hM0]
    simp only [m, Finsupp.prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpq : p ≠ q := by rintro rfl; simp [hMf] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [← pow_mul, hMf, Finsupp.erase_ne hpq, Nat.div_mul_cancel (hev p hpp hpq).two_dvd]
  refine ⟨q, N.factorization q, m, hq, ?_, fun hqm => ?_, hq4, hk⟩
  · rw [hm, Nat.ordProj_mul_ordCompl_eq_self]
  · exact Nat.not_dvd_ordCompl hq h.ne_zero (by have := dvd_pow hqm two_ne_zero; rwa [hm] at this)

private lemma sq_mod_of_not_dvd {m n : ℕ} (hn : n = 3 ∨ n = 4) (hm : m % n = 1 ∨ m % n = n - 1) :
    m ^ 2 % n = 1 := by
  rw [Nat.pow_mod]
  rcases hn with rfl | rfl <;> rcases hm with h | h <;> simp [h]

/-- An odd perfect number is `≡ 1 (mod 4)`. -/
theorem mod_four (h : OddPerfect N) : N % 4 = 1 := by
  obtain ⟨q, k, m, -, rfl, -, hq4, -⟩ := exists_euler_form h
  have hmo : m % 2 = 1 :=
    Nat.odd_iff.mp (h.odd.of_dvd_nat ((dvd_pow_self m two_ne_zero).mul_left _))
  rw [Nat.mul_mod, Nat.pow_mod, hq4, sq_mod_of_not_dvd (Or.inr rfl) (by omega)]
  simp

/-- An odd perfect number is not a perfect square. -/
theorem not_isSquare (h : OddPerfect N) : ¬ IsSquare N := by
  rintro ⟨r, rfl⟩
  obtain ⟨q, -, -, -, he, -⟩ := exists_special_prime h
  have hr : r ≠ 0 := by rintro rfl; exact h.ne_zero rfl
  rw [Nat.factorization_mul hr hr, Finsupp.add_apply] at he
  omega

/-- A prime `p ≡ 3 (mod 4)` dividing an odd perfect number divides it to at least the
second power. -/
theorem sq_dvd_of_prime_dvd_of_mod_four_eq_three {N p : ℕ} (h : OddPerfect N)
    (hp : p.Prime) (hpN : p ∣ N) (h3 : p % 4 = 3) : p ^ 2 ∣ N := by
  obtain ⟨q, -, -, hq4, -, hev⟩ := exists_special_prime h
  have he := hev p hp (by rintro rfl; omega)
  have h1 := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN
  rw [hp.pow_dvd_iff_le_factorization h.ne_zero]
  obtain ⟨j, hj⟩ := he
  omega

/-- Touchard: an odd perfect number is `≡ 1 (mod 12)` or `≡ 9 (mod 36)`. -/
theorem touchard (h : OddPerfect N) : N % 12 = 1 ∨ N % 36 = 9 := by
  have h4 := mod_four h
  by_cases h3 : 3 ∣ N
  · have h9 := sq_dvd_of_prime_dvd_of_mod_four_eq_three h Nat.prime_three h3 (by decide)
    right
    omega
  left
  suffices N % 3 = 1 by omega
  by_contra hne
  have h2 : N % 3 = 2 := by omega
  obtain ⟨q, k, m, hq, hN, hqm, -, hk⟩ := exists_euler_form h
  have hm3 : ¬ 3 ∣ m := fun h3m => h3 (hN ▸ (h3m.pow two_ne_zero).mul_left _)
  have hqk3 : q ^ k % 3 = 2 := by
    rw [hN, Nat.mul_mod, sq_mod_of_not_dvd (Or.inl rfl) (by omega)] at h2
    omega
  have hq3 : q % 3 = 2 := by
    rw [Nat.pow_mod] at hqk3
    rcases (by omega : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2) with h0 | h0 | h0
    · simp [h0, zero_pow (by omega : k ≠ 0)] at hqk3
    · simp [h0] at hqk3
    · exact h0
  have hfac : N.factorization q = k := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ (by rintro rfl; simp at hqm)),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  apply h3
  refine OPNStarter.force_prime h.perfect hq hfac Nat.prime_three (by decide) ?_
  rw [sigma_one_apply_prime_pow hq]
  exact dvd_geom_of_odd (by omega) (Nat.odd_iff.mpr (by omega))

end OddPerfect

#print axioms OddPerfect.exists_special_prime
#print axioms OddPerfect.existsUnique_odd_exponent
#print axioms OddPerfect.exists_euler_form
#print axioms OddPerfect.mod_four
#print axioms OddPerfect.not_isSquare
#print axioms OddPerfect.sq_dvd_of_prime_dvd_of_mod_four_eq_three
#print axioms OddPerfect.touchard
