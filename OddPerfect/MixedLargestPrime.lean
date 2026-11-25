import OddPerfect.MixedPaletteEdges

/-!
# The largest prime factor in the palette of exponents 2 and 4 without the primes 3 and 5

Restricted family results; the family is not excluded, and whether the results are in the
literature was not verified.

Let `N` be an odd perfect number with special prime `q` such that every other prime factor
has exponent `2` or `4`, let `3 ∤ N` and `5 ∤ N`, and let `P ≠ q` be the largest prime factor
of `N`. By the Main Theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81 (2012)) the least
prime factor exceeds `10 ^ 8` when every prime factor other than the special prime has
exponent `2` or `4`, so `3 ∤ N` and `5 ∤ N` hold in this family; that theorem is not
formalized here, and the two conditions are explicit hypotheses.

* If `v_P(N) = 4`, then `P ^ 3 ∣ σ(q ^ v_q(N))` (`mixed_largest_cube_dvd_sigma_special`). A row
  `σ(p ^ 4)` with `p ≠ q` is prime to `P`, since its prime divisors other than `q` have
  exponent `2`. A row `σ(p ^ 2)` with `p < P` is below `P ^ 2`, so it carries at most one unit
  of `P`; its prime `p` is `2 (mod 3)`, and by Zelinsky's lemma `shared_prime_le` two such rows
  cannot both reach `P`. The row of `P` is prime to `P`, and the valuation of `σ(N) = 2 N` at
  `P` leaves at least `3` for the row of `q`.
* If `v_q(N) = 1`, then `v_P(N) = 2` and `P ≡ 11 (mod 15)`
  (`mixed_largest_exponent_two_of_special_exponent_one`). Here `σ(q) = q + 1` is prime to `P`,
  so `v_P(N) ≠ 4`. Then `P ≡ 2 (mod 3)`, no square row reaches `P`, so some row `σ(p ^ 4)`
  does, and `P ≡ 1 (mod 5)`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem mlp_geom_three (u : ℕ) : ∑ i ∈ Finset.range 3, u ^ i = 1 + u + u ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- Two square senders: for a prime `P ≡ 1 (mod 3)` and distinct `u, v < P`, both
`2 (mod 3)`, `P` does not divide both `1 + u + u ^ 2` and `1 + v + v ^ 2`. A direct
consequence of `shared_prime_le`. -/
private theorem mlp_two_square_senders {P u v : ℕ} (hP : P.Prime) (hP3 : P % 3 = 1)
    (hu : u % 3 = 2) (hv : v % 3 = 2) (huP : u < P) (hvP : v < P) (huv : u ≠ v)
    (hdu : P ∣ 1 + u + u ^ 2) (hdv : P ∣ 1 + v + v ^ 2) : False := by
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · have := shared_prime_le hv hu h hP hP3 hdv hdu
    omega
  · have := shared_prime_le hu hv h hP hP3 hdu hdv
    omega

/-- The rows of the prime factors other than `q` carry at most one unit at the largest prime
factor `P` when `v_P(N) = 4`. -/
private theorem mlp_rest_le_one {N q P : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N)
    (hP : P ∈ N.primeFactors) (hmax : ∀ p ∈ N.primeFactors, p ≤ P) (hPq : P ≠ q)
    (hP4 : N.factorization P = 4) :
    ∑ p ∈ N.primeFactors.erase q, sigmaWeight N p P ≤ 1 := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hP2 := hPp.two_le
  have hP3 : P ≠ 3 := fun h' => h3 (h' ▸ Nat.dvd_of_mem_primeFactors hP)
  have hterm : ∀ p ∈ N.primeFactors.erase q, sigmaWeight N p P ≤ 1 ∧
      (sigmaWeight N p P ≠ 0 → p % 3 = 2 ∧ p < P ∧ P ∣ 1 + p + p ^ 2) := by
    intro p hp
    obtain ⟨hpq, hp'⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hp'
    have hp1 := hpp.two_le
    have hw : sigmaWeight N p P = (σ 1 (p ^ N.factorization p)).factorization P := rfl
    by_cases hpP : p = P
    · rw [hpP, sigmaWeight_self hPp]
      exact ⟨by omega, fun h0 => absurd rfl h0⟩
    have hlt : p < P := lt_of_le_of_ne (hmax p hp') hpP
    have hσ0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
    rcases hexp p hp' hpq with hf | hf
    · have hs : σ 1 (p ^ N.factorization p) = 1 + p + p ^ 2 := by
        rw [hf, sigma_one_apply_prime_pow hpp, mlp_geom_three]
      have hbig : 1 + p + p ^ 2 < P ^ 2 := by nlinarith
      refine ⟨?_, fun h0 => ⟨mixed_square_prime_mod_three h hp' hf h3, hlt, ?_⟩⟩
      · by_contra hc
        have hd : P ^ 2 ∣ σ 1 (p ^ N.factorization p) :=
          (hPp.pow_dvd_iff_le_factorization hσ0).mpr (by omega)
        rw [hs] at hd
        exact absurd (Nat.le_of_dvd (by positivity) hd) (by omega)
      · rw [← hs]
        exact Nat.dvd_of_factorization_pos (by rw [← hw]; exact h0)
    · have hz : sigmaWeight N p P = 0 := by
        rw [hw]
        refine Nat.factorization_eq_zero_of_not_dvd fun hd => ?_
        rw [hf] at hd
        have := mixed_quartic_row_target_exponent_two h hexp h5 hp' hf hPp hd hPq
        omega
      rw [hz]
      exact ⟨by omega, fun h0 => absurd rfl h0⟩
  have hcard : ((N.primeFactors.erase q).filter (fun p => sigmaWeight N p P ≠ 0)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    obtain ⟨hx3, hxP, hxd⟩ := (hterm x hx1).2 hx2
    obtain ⟨hy3, hyP, hyd⟩ := (hterm y hy1).2 hy2
    have hPmod : P % 3 = 1 := by
      by_contra hc
      refine not_dvd_geom_sum_of_not_dvd_sub_one hPp Nat.prime_three hP3 (by omega) x ?_
      rw [mlp_geom_three]
      exact hxd
    by_contra hxy
    exact mlp_two_square_senders hPp hPmod hx3 hy3 hxP hyP hxy hxd hyd
  rw [← Finset.sum_filter_ne_zero]
  have := Finset.sum_le_card_nsmul
    ((N.primeFactors.erase q).filter (fun p => sigmaWeight N p P ≠ 0))
    (fun p => sigmaWeight N p P) 1
    (fun p hp => (hterm p (Finset.mem_filter.mp hp).1).1)
  simp only [smul_eq_mul, mul_one] at this
  omega

/-- Largest prime of exponent `4`. Let `N` be an odd perfect number with special prime `q` such
that every other prime factor has exponent `2` or `4`, let `3 ∤ N` and `5 ∤ N` (explicit
hypotheses; in this family they follow from the Main Theorem of Fletcher, Nielsen and Ochem,
Math. Comp. 81 (2012), not formalized here), and let `P ≠ q` be the largest prime factor of
`N`. If `v_P(N) = 4`, then `P ^ 3 ∣ σ(q ^ v_q(N))`. Restricted family result: the family is not
excluded; novelty not verified. -/
theorem mixed_largest_cube_dvd_sigma_special {N q P : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N)
    (hP : P ∈ N.primeFactors) (hmax : ∀ p ∈ N.primeFactors, p ≤ P) (hPq : P ≠ q)
    (hP4 : N.factorization P = 4) : P ^ 3 ∣ σ 1 (q ^ N.factorization q) := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hP2 : P ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hP)
  have hsum := sigmaWeight_sum_eq h.perfect hPp hP2
  have hrest := mlp_rest_le_one h hexp h3 h5 hP hmax hPq hP4
  by_cases hqN : q ∈ N.primeFactors
  · rw [← Finset.add_sum_erase _ _ hqN, hP4] at hsum
    have hqp := Nat.prime_of_mem_primeFactors hqN
    have hσ0 : σ 1 (q ^ N.factorization q) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hqp.ne_zero)).ne'
    have hw : sigmaWeight N q P = (σ 1 (q ^ N.factorization q)).factorization P := rfl
    exact (hPp.pow_dvd_iff_le_factorization hσ0).mpr (by omega)
  · rw [Finset.erase_eq_of_notMem hqN, hsum, hP4] at hrest
    omega

/-- Special exponent one. Let `N` be an odd perfect number with special prime `q` such that
every other prime factor has exponent `2` or `4`, let `3 ∤ N` and `5 ∤ N` (explicit hypotheses;
in this family they follow from the Main Theorem of Fletcher, Nielsen and Ochem, Math. Comp. 81
(2012), not formalized here), and let `P ≠ q` be the largest prime factor of `N`. If
`v_q(N) = 1`, then `v_P(N) = 2` and `P ≡ 11 (mod 15)`. Restricted family result: the family is
not excluded; novelty not verified. -/
theorem mixed_largest_exponent_two_of_special_exponent_one {N q P : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N)
    (hP : P ∈ N.primeFactors) (hmax : ∀ p ∈ N.primeFactors, p ≤ P) (hPq : P ≠ q)
    (hq1 : N.factorization q = 1) : N.factorization P = 2 ∧ P % 15 = 11 := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hP2 : P ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hP)
  have hqN : q ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by omega)
  have hqp := Nat.prime_of_mem_primeFactors hqN
  have hq2 : q ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hqN)
  have hqP : q < P := lt_of_le_of_ne (hmax q hqN) (Ne.symm hPq)
  have hs : σ 1 (q ^ N.factorization q) = q + 1 := by
    rw [hq1, sigma_one_apply_prime_pow hqp]
    simp [Finset.sum_range_succ, add_comm]
  have hnd : ¬ P ∣ q + 1 := by
    rintro ⟨k, hk⟩
    have ho1 := hqp.eq_two_or_odd.resolve_left hq2
    have ho2 := hPp.eq_two_or_odd.resolve_left hP2
    rcases k with _ | _ | k
    · omega
    · omega
    · nlinarith
  have hP2' : N.factorization P = 2 := by
    rcases hexp P hP hPq with hf | hf
    · exact hf
    · have hd := mixed_largest_cube_dvd_sigma_special h hexp h3 h5 hP hmax hPq hf
      rw [hs] at hd
      exact absurd ((dvd_pow_self P (by norm_num)).trans hd) hnd
  have hP3 := mixed_square_prime_mod_three h hP hP2' h3
  have hsum := sigmaWeight_sum_eq h.perfect hPp hP2
  rw [hP2'] at hsum
  obtain ⟨p, hp, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [hsum]; norm_num : ∑ p ∈ N.primeFactors, sigmaWeight N p P ≠ 0)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpq : p ≠ q := by
    rintro rfl
    apply hw
    unfold sigmaWeight
    rw [hs]
    exact Nat.factorization_eq_zero_of_not_dvd hnd
  have hpP : p ≠ P := by
    rintro rfl
    exact hw (sigmaWeight_self hpp)
  have hd : P ∣ σ 1 (p ^ N.factorization p) := Nat.dvd_of_factorization_pos hw
  have hP5 : P ≠ 5 := fun h' => h5 (h' ▸ Nat.dvd_of_mem_primeFactors hP)
  rcases hexp p hp hpq with hf | hf
  · rw [hf] at hd
    have := mixed_square_row_target_exponent_four h hexp h3 hp hf hPp hd hPq
    omega
  · rw [hf, sigma_one_apply_prime_pow hpp] at hd
    have hP51 : P % 5 = 1 := by
      by_contra hc
      have := hPp.two_le
      exact not_dvd_geom_sum_of_not_dvd_sub_one hPp Nat.prime_five hP5 (by omega) p hd
    exact ⟨hP2', by omega⟩

end OddPerfect

#print axioms OddPerfect.mixed_largest_cube_dvd_sigma_special
#print axioms OddPerfect.mixed_largest_exponent_two_of_special_exponent_one
