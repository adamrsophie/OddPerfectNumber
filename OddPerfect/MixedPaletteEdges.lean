import OddPerfect.RankTwoPalette
import OddPerfect.CountingZelinsky

/-!
# Edges in the palette of exponents 2 and 4 without the primes 3 and 5

Restricted family results; the family is not excluded, and whether the results are in the
literature was not verified.

Let `N` be an odd perfect number with special prime `q` such that every other prime factor
has exponent `2` or `4` (the mixed family).

* Edge alternation. If `3 ∤ N`, every prime factor of exponent `2` is `2 (mod 3)`
  (`mixed_square_prime_mod_three`), and every prime `r ≠ q` dividing `σ(p ^ 2)` for such a
  prime `p` has exponent `4` (`mixed_square_row_target_exponent_four`). If `5 ∤ N`, no prime
  factor of exponent `4` is `1 (mod 5)` (`mixed_quartic_prime_mod_five`), and every prime
  `r ≠ q` dividing `σ(p ^ 4)` for such a prime `p` has exponent `2`
  (`mixed_quartic_row_target_exponent_two`).
* Lower weight. If `3 ∤ N`, the rows of the primes below `q` carry at most
  `(if q % 3 = 1 then 1 else 0) + (if q % 5 = 1 then 6 else 0)` at `q`
  (`mixed_sum_sigmaWeight_below_special_le_mod_of_not_three_dvd`), against `2` in place of
  `1` in `sum_sigmaWeight_below_special_le_mod`. The square rows that reach `q` come from
  primes `2 (mod 3)`, each carries one unit (`1 + u + u ^ 2 < q ^ 2`), and by Zelinsky's
  lemma `shared_prime_le` two of them cannot both reach `q`.

The two square senders statement (two primes `u ≠ v` below a prime `q ≡ 1 (mod 3)`, both
`2 (mod 3)`, do not both have `q ∣ 1 + u + u ^ 2`) is a direct consequence of the landed
`shared_prime_le` and is used here only as the private step `mpe_two_square_senders`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem mpe_sigmaWeight_eq_geom {N p q : ℕ} (hp : p.Prime) :
    sigmaWeight N p q =
      (∑ i ∈ Finset.range (N.factorization p + 1), p ^ i).factorization q := by
  unfold sigmaWeight
  rw [sigma_one_apply_prime_pow hp]

private theorem mpe_geom_three (u : ℕ) : ∑ i ∈ Finset.range 3, u ^ i = 1 + u + u ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- Modulo `m`, a geometric sum of `l` terms with ratio `1 (mod m)` is `l`. -/
private theorem mpe_cast_geom_sum {l m p : ℕ} (hp : p % m = 1) :
    ((∑ i ∈ Finset.range l, p ^ i : ℕ) : ZMod m) = l := by
  push_cast
  rw [show (p : ZMod m) = 1 by rw [← ZMod.natCast_mod, hp, Nat.cast_one]]
  simp

private theorem mpe_dvd_geom_sum {l p : ℕ} (hp : p % l = 1) :
    l ∣ ∑ i ∈ Finset.range l, p ^ i :=
  (ZMod.natCast_eq_zero_iff _ _).mp (by rw [mpe_cast_geom_sum hp, ZMod.natCast_self])

private theorem mpe_dvd_of_dvd_geom_sum {l m p : ℕ} (hp : p % m = 1)
    (hd : m ∣ ∑ i ∈ Finset.range l, p ^ i) : m ∣ l :=
  (ZMod.natCast_eq_zero_iff _ _).mp (by
    rw [← mpe_cast_geom_sum (l := l) hp]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd)

/-- A prime dividing a component divisor sum of odd length is an odd prime factor. -/
private theorem mpe_mem_of_dvd_sigma {N p r l : ℕ} (h : OddPerfect N)
    (hp : p ∈ N.primeFactors) (hl : N.factorization p + 1 = l) (hl2 : ¬ 2 ∣ l)
    (hr : r.Prime) (hd : r ∣ ∑ i ∈ Finset.range l, p ^ i) : r ∈ N.primeFactors := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p % 2 = 1 :=
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hl2 (mpe_dvd_of_dvd_geom_sum hp2 hd)
  have hd' : r ∣ σ 1 (p ^ N.factorization p) := by
    rw [sigma_one_apply_prime_pow hpp, hl]
    exact hd
  have h0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
  have hw : 1 ≤ sigmaWeight N p r := hr.factorization_pos_of_dvd h0 hd'
  exact mem_primeFactors_of_sigmaWeight_ne_zero h.perfect hp hr2 (by omega)

private theorem mpe_ne_of_not_dvd {N r l : ℕ} (hr : r ∈ N.primeFactors) (hl : ¬ l ∣ N) :
    r ≠ l := by
  rintro rfl
  exact hl (Nat.dvd_of_mem_primeFactors hr)

/-- Edge alternation, squares. Let `N` be an odd perfect number with `3 ∤ N`. Every prime
factor `p` of `N` with exponent `2` satisfies `p ≡ 2 (mod 3)`: otherwise
`3 ∣ σ(p ^ 2) ∣ 2 N`. -/
theorem mixed_square_prime_mod_three {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (hp2 : N.factorization p = 2) (h3 : ¬ 3 ∣ N) : p % 3 = 2 := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp3 := mpe_ne_of_not_dvd hp h3
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h0 | h1 | h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm hp3
  · exact absurd (Nat.dvd_of_mem_primeFactors
      (mpe_mem_of_dvd_sigma h hp (by omega) (by norm_num) Nat.prime_three
        (mpe_dvd_geom_sum h1))) h3
  · exact h2

/-- Edge alternation, quartics. Let `N` be an odd perfect number with `5 ∤ N`. No prime
factor `p` of `N` with exponent `4` satisfies `p ≡ 1 (mod 5)`: otherwise
`5 ∣ σ(p ^ 4) ∣ 2 N`. -/
theorem mixed_quartic_prime_mod_five {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (hp4 : N.factorization p = 4) (h5 : ¬ 5 ∣ N) : p % 5 ≠ 1 := fun h1 =>
  h5 (Nat.dvd_of_mem_primeFactors
    (mpe_mem_of_dvd_sigma h hp (by omega) (by norm_num) Nat.prime_five (mpe_dvd_geom_sum h1)))

/-- Edge alternation, square rows. Let `N` be an odd perfect number with special prime `q`
such that every other prime factor has exponent `2` or `4`, and let `3 ∤ N`. If `p` is a prime
factor of exponent `2` and `r ≠ q` is a prime dividing `σ(p ^ 2)`, then `r` has exponent `4`
in `N`. Restricted family result; novelty not verified. -/
theorem mixed_square_row_target_exponent_four {N q p r : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N)
    (hp : p ∈ N.primeFactors) (hp2 : N.factorization p = 2) (hr : r.Prime)
    (hrd : r ∣ σ 1 (p ^ 2)) (hrq : r ≠ q) : N.factorization r = 4 := by
  rw [sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)] at hrd
  have hrN := mpe_mem_of_dvd_sigma h hp (by omega) (by norm_num) hr hrd
  rcases hexp r hrN hrq with hr2 | hr4
  · have hr3 := mixed_square_prime_mod_three h hrN hr2 h3
    exact absurd hrd (not_dvd_geom_sum_of_not_dvd_sub_one hr Nat.prime_three
      (mpe_ne_of_not_dvd hrN h3) (by omega) p)
  · exact hr4

/-- Edge alternation, quartic rows. Let `N` be an odd perfect number with special prime `q`
such that every other prime factor has exponent `2` or `4`, and let `5 ∤ N`. If `p` is a prime
factor of exponent `4` and `r ≠ q` is a prime dividing `σ(p ^ 4)`, then `r` has exponent `2`
in `N`. Restricted family result; novelty not verified. -/
theorem mixed_quartic_row_target_exponent_two {N q p r : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h5 : ¬ 5 ∣ N)
    (hp : p ∈ N.primeFactors) (hp4 : N.factorization p = 4) (hr : r.Prime)
    (hrd : r ∣ σ 1 (p ^ 4)) (hrq : r ≠ q) : N.factorization r = 2 := by
  rw [sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)] at hrd
  have hrN := mpe_mem_of_dvd_sigma h hp (by omega) (by norm_num) hr hrd
  rcases hexp r hrN hrq with hr2 | hr4
  · exact hr2
  · have hr5 := mixed_quartic_prime_mod_five h hrN hr4 h5
    have hr1 := hr.two_le
    exact absurd hrd (not_dvd_geom_sum_of_not_dvd_sub_one hr Nat.prime_five
      (mpe_ne_of_not_dvd hrN h5) (by omega) p)

/-- Two square senders: for a prime `q ≡ 1 (mod 3)` and distinct `u, v < q`, both
`2 (mod 3)`, `q` does not divide both `1 + u + u ^ 2` and `1 + v + v ^ 2`. A direct
consequence of `shared_prime_le`. -/
private theorem mpe_two_square_senders {q u v : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1)
    (hu : u % 3 = 2) (hv : v % 3 = 2) (huq : u < q) (hvq : v < q) (huv : u ≠ v)
    (hdu : q ∣ 1 + u + u ^ 2) (hdv : q ∣ 1 + v + v ^ 2) : False := by
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · have := shared_prime_le hv hu h hq hq3 hdv hdu
    omega
  · have := shared_prime_le hu hv h hq hq3 hdu hdv
    omega

/-- Lower weight without the prime `3`. Let `N` be an odd perfect number with special prime
`q` such that every other prime factor has exponent `2` or `4`, and let `3 ∤ N`. Then the rows
of the prime factors below `q` carry at most
`(if q % 3 = 1 then 1 else 0) + (if q % 5 = 1 then 6 else 0)` at `q`; in particular at most
`7`. Restricted family result: the family is not excluded; novelty not verified. -/
theorem mixed_sum_sigmaWeight_below_special_le_mod_of_not_three_dvd {N q : ℕ}
    (h : OddPerfect N) (hq : q.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤
      (if q % 3 = 1 then 1 else 0) + (if q % 5 = 1 then 6 else 0) := by
  classical
  set U := N.primeFactors.filter (· < q) with hU
  have hUp : ∀ s : Finset ℕ, s ⊆ U → ∀ u ∈ s, u.Prime ∧ u < q := fun s hs u hu =>
    ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (hs hu)).1,
      (Finset.mem_filter.mp (hs hu)).2⟩
  have hq2 := hq.two_le
  by_cases hsmall : q = 3 ∨ q = 5
  · have hz : ∀ p ∈ U, sigmaWeight N p q = 0 := by
      intro p hp
      obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hp'
      have hp2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp')
      have hp3 : p = 3 ∧ q = 5 := by
        have := hpp.two_le
        rcases hsmall with rfl | rfl
        · omega
        · interval_cases p
          · exact absurd rfl hp2
          · exact ⟨rfl, rfl⟩
          · exact absurd hpp (by norm_num)
      obtain ⟨rfl, rfl⟩ := hp3
      rw [mpe_sigmaWeight_eq_geom hpp]
      rcases hexp 3 hp' (by norm_num) with hf | hf <;> rw [hf] <;>
        exact Nat.factorization_eq_zero_of_not_dvd (by decide)
    rw [Finset.sum_eq_zero hz]
    exact Nat.zero_le _
  push Not at hsmall
  have hpt : ∀ p ∈ U, sigmaWeight N p q ≤
      (if N.factorization p = 2 then (∑ i ∈ Finset.range 3, p ^ i).factorization q else 0) +
      (if N.factorization p = 4 then (∑ i ∈ Finset.range 5, p ^ i).factorization q
        else 0) := by
    intro p hp
    obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hp'
    rw [mpe_sigmaWeight_eq_geom hpp]
    rcases hexp p hp' (by omega) with hf | hf
    · rw [if_pos hf, if_neg (by omega), add_zero, hf]
    · rw [if_neg (by omega), if_pos hf, zero_add, hf]
  have hle := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hle
  have h2 : ∑ p ∈ U.filter (fun p => N.factorization p = 2),
      (∑ i ∈ Finset.range 3, p ^ i).factorization q ≤ if q % 3 = 1 then 1 else 0 := by
    split_ifs with h3q
    · simp only [mpe_geom_three]
      set S := U.filter (fun p => N.factorization p = 2)
      have hterm : ∀ u ∈ S, (1 + u + u ^ 2).factorization q ≤ 1 ∧
          ((1 + u + u ^ 2).factorization q ≠ 0 → q ∣ 1 + u + u ^ 2) ∧ u % 3 = 2 ∧
          u < q := by
        intro u hu
        obtain ⟨huU, hu2⟩ := Finset.mem_filter.mp hu
        obtain ⟨hu', huq⟩ := Finset.mem_filter.mp huU
        have hu1 := (Nat.prime_of_mem_primeFactors hu').two_le
        have hne : 1 + u + u ^ 2 ≠ 0 := by positivity
        have hlt : 1 + u + u ^ 2 < q ^ 2 := by nlinarith
        refine ⟨?_, fun h0 => Nat.dvd_of_factorization_pos h0,
          mixed_square_prime_mod_three h hu' hu2 h3, huq⟩
        by_contra hc
        have hd : q ^ 2 ∣ 1 + u + u ^ 2 :=
          (hq.pow_dvd_iff_le_factorization hne).mpr (by omega)
        exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
      have hcard : (S.filter (fun p => (1 + p + p ^ 2).factorization q ≠ 0)).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun x hx y hy => ?_
        obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
        obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
        obtain ⟨-, hxd, hx3, hxq⟩ := hterm x hx1
        obtain ⟨-, hyd, hy3, hyq⟩ := hterm y hy1
        by_contra hxy
        exact mpe_two_square_senders hq h3q hx3 hy3 hxq hyq hxy (hxd hx2) (hyd hy2)
      rw [← Finset.sum_filter_ne_zero]
      have := Finset.sum_le_card_nsmul
        (S.filter (fun p => (1 + p + p ^ 2).factorization q ≠ 0))
        (fun p => (1 + p + p ^ 2).factorization q) 1
        (fun p hp => (hterm p (Finset.mem_filter.mp hp).1).1)
      simp only [smul_eq_mul, mul_one] at this
      omega
    · refine (Finset.sum_eq_zero fun u _ => Nat.factorization_eq_zero_of_not_dvd ?_).le
      exact not_dvd_geom_sum_of_not_dvd_sub_one hq Nat.prime_three hsmall.1 (by omega) u
  have h4 : ∑ p ∈ U.filter (fun p => N.factorization p = 4),
      (∑ i ∈ Finset.range 5, p ^ i).factorization q ≤ if q % 5 = 1 then 6 else 0 := by
    split_ifs with h5
    · exact sum_factorization_geom_sum_five_le_six_of_primes hq hsmall.2 _
        (hUp _ (Finset.filter_subset _ _))
    · refine (Finset.sum_eq_zero fun u _ => Nat.factorization_eq_zero_of_not_dvd ?_).le
      exact not_dvd_geom_sum_of_not_dvd_sub_one hq Nat.prime_five hsmall.2 (by omega) u
  omega

end OddPerfect

#print axioms OddPerfect.mixed_square_prime_mod_three
#print axioms OddPerfect.mixed_quartic_prime_mod_five
#print axioms OddPerfect.mixed_square_row_target_exponent_four
#print axioms OddPerfect.mixed_quartic_row_target_exponent_two
#print axioms OddPerfect.mixed_sum_sigmaWeight_below_special_le_mod_of_not_three_dvd
